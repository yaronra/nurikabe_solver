"""
Possible next steps:

Combine and uncombine?

In chaining: find pairs of edges where one of them must exist (island A must touch either B or C).
    This allows us to rule out variants that create a cycle wheter AB or AC exist.

Common move we can't find: if island A goes here, it pushes island B here, and this closes a chain. (e.g. janko 467)
Another common one: if A goes here, then B will either touch it or touch C, and both options close a loop

Start an unclued island for a square with only two known sea cells (so all variants must include at least one of the others).
    # did that, but not clear if it helps (it hurts the combine phase)

cloud blocked points are known points and their neighbors, but it may be possible to do better.

cloud subvariants:
    create subvariants of the max size you can.  use them for intersections (known / blocked cells) in addition to current method.
    as culling proceeds, try to increase subvariant size.

When solving ILP, check that there's only one solution (by removing the one you found and re-solving).
    This requires plowing through all remaining solutions with sea-disconnection

Bugs:
If a clue is very large, gets an error for exceeding recursion depth.  exit gracefully instead.


Unsolved puzzles:

Simon: possible move is: if the 10 goes next to the 4, we get black between them, which forces white to prevent pool, which blocks the top sea / creates chain.
janko 430: if the top left 4 goes two up, the sea needs to emerge between the 4 and the 3 below it, creating a pool. 
janko 756: the two unclued each have two possible clouds (the 22's)
    Option 1: identify which goes to which.  This would happen if they were variants based.
    Option 2: Since 2 unclueds have the same 2 islands, those islands must go to the unclued (even if we don't know which is which)
        But since we don't have this logic, the 22's themselves are not attached to the unclued, so we don't know about their reach constraints.
janko 798: if the final cell of the bottom left 9 goes right, the 5 will either touch it or touch the 1 (that touches it), creating a loop
janko 799: at end, remove variants of 5 that touch the 2, because the 5 is grounded, and the 2 *would be* grounded if those variants are chosen.

"""

from collections import defaultdict
import itertools
import math
import networkx as nx
from optparse import OptionParser
import pulp
from time import time
from tqdm import tqdm

import progress


MAX_VARIANTS_PER_ISLAND = 11000

def main():
    parser = OptionParser()
    parser.add_option('-p', "--puzzle_filename")
    parser.add_option('-s', "--solution_filename", help="optional, for debugging")
    parser.add_option('-c', "--connected_cost_in_mip", action='store_true', help="maximize number of adjacent sea squares in mip")
    parser.add_option('-v', "--verbose", action='store_true')
    parser.add_option('-l', "--solver_logs", action='store_true')
    options, _ = parser.parse_args()

    solver = Solver.from_filenames(options.puzzle_filename, options.solution_filename, options.connected_cost_in_mip, options.verbose, options.solver_logs)
    solver.solve()

def char2num(char):
    if char == '.':
        return 0
    try:
        return int(char)
    except ValueError:
        return ord(char) - ord('a') + 10

def str2row(str):
    return [char2num(char) for char in str]

def num2char(num):
    if num <= 9:
        return str(num)
    return chr(ord('a') + num - 10)

directions = [
    (0, 1),
    (0, -1),
    (1, 0),
    (-1, 0)
]

diagonals = [
    (1, 1),
    (1, -1), 
    (-1, 1),
    (-1, -1),
]

directions_with_diagonals = directions + diagonals

class OffGridException(Exception):
    pass

class TooManyVariants(Exception):
    pass

class InvalidCloud(Exception):
    pass

class ProblemTooHard(Exception):
    pass

class NoPossibleSolution(Exception):
    pass


class IslandVariant:
    def __init__(self, cells, solver):
        self.cells = set(cells)
        self.solver = solver
        self.extended_cells = self.cells.copy()
        for cell in self.cells:
            for neighbor in solver.get_neighbors(cell):
                self.extended_cells.add(neighbor)
        self.extended_cells_with_diagonals = self.cells.copy()
        for cell in self.cells:
            for neighbor in solver.get_neighbors_with_diagonals(cell):
                self.extended_cells_with_diagonals.add(neighbor)
        self._hash = hash(tuple(sorted(cells)))

    def __hash__(self):
        return self._hash
    
    def __eq__(self, other):
        return self._hash == other._hash

    @property
    def islands(self):
        return self.solver.variant_islands[self]

    def remove_from_all_islands(self):
        for island in self.islands:
            island.remove_variant(self)
        del self.solver.variant_islands[self]

    def add_island(self, island):
        self.islands.add(island)


class IslandInterface:
    """
    Holds known information about an island and responds to queries.
    """
    def __init__(self, variants: list[IslandVariant], solver, n_clues=1):
        self.variants = set(variants)
        self.solver = solver
        self.n_clues = n_clues
        for variant in self.variants:
            variant.add_island(self)
        self._clear_cache()

    def _clear_cache(self):
        self._known_cells = None
        self._all_possible_cells = None
        self._blocked_cells = None

    @property
    def known_cells(self):
        if self._known_cells is None:
            self._known_cells = set.intersection(*[variant.cells for variant in self.variants])
        return self._known_cells

    @property
    def all_possible_cells(self):
        if self._all_possible_cells is None:
            self._all_possible_cells = set.union(*[variant.cells for variant in self.variants])
        return self._all_possible_cells
    
    @property
    def blocked_cells(self):
        if self._blocked_cells is None:
            self._blocked_cells = set.intersection(*[variant.extended_cells for variant in self.variants])
        return self._blocked_cells

    def remove_variant(self, variant):
        """This should not be called directly
        The way to remove a variant form all islands is to use IslandVariant.remove() - which will call remove on all relevant islands
        """
        self.variants.remove(variant)
        if not self.variants:
            raise NoPossibleSolution(f"No variants left when removing variant {variant.cells} from {self}")
        self._clear_cache()

    def force_reaching_cell_set(self, cell_set):
        variants_to_remove = [variant for variant in self.variants if not(variant.cells & cell_set)]
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        return len(variants_to_remove) > 0

    def block_from_island(self, blocking_island):
        blocked_cells = blocking_island.blocked_cells
        variants_to_remove = [variant for variant in self.variants if blocking_island not in variant.islands and (variant.cells & blocked_cells)]
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        return len(variants_to_remove) > 0

    def block_from_cell_set(self, blocking_set):
        variants_to_remove = [variant for variant in self.variants if (variant.cells & blocking_set)]
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        return len(variants_to_remove) > 0

    def block_from_island_variants(self, blocking_island):
        blocking_variants = blocking_island.get_variants_for_blocking()
        # A cloud will return an empty list, to be ignored.
        if not blocking_variants:
            return False
        variants_to_remove = [variant for variant in self.variants if blocking_island not in variant.islands and
                              all(variant.cells & blocking_variant.extended_cells for blocking_variant in blocking_variants)]
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        return len(variants_to_remove) > 0

    def get_cloud_origins(self):
        return []

    def __hash__(self):
        return hash(id(self))
    
    def __eq__(self, other):
        return self is other

    def get_size_string(self):
        return str(len(self.variants))
    

class CluedIsland(IslandInterface):
    """
    Holds the variants of an island based on a specific number clue in the grid.
    """
    @staticmethod
    def from_initial_clues(initial_loc, solver):
        exclusion_set = set()
        for other_loc in solver.clues:
            if other_loc == initial_loc:
                continue
            exclusion_set.add(other_loc)
            for neighbor in solver.get_neighbors(other_loc):
                exclusion_set.add(neighbor)
        try:
            variant_cell_tuples = CluedIsland._recursive_make_variants(
                initial_loc, 
                size=solver.clues[initial_loc], 
                exclusion_set=exclusion_set,
                solver=solver)
            variants = [IslandVariant(set(cell_tuple), solver) for cell_tuple in variant_cell_tuples]
            return CluedIsland(variants, solver)
        except TooManyVariants:
            return CloudIsland.from_initial_clues(initial_loc, solver)

    @staticmethod
    def _recursive_make_variants(loc, size, exclusion_set, solver):
        if size == 1:
            return {(loc,)}
        variants = set()
        sub_variants = CluedIsland._recursive_make_variants(loc, size-1, exclusion_set, solver)
        if len(sub_variants) >= MAX_VARIANTS_PER_ISLAND:
            raise TooManyVariants()
        for sub_variant in sub_variants:
            sub_variant_list = list(sub_variant)
            for loc in sub_variant:
                for neighbor in solver.get_neighbors(loc):
                    if neighbor in sub_variant:
                        continue
                    if neighbor in exclusion_set:
                        continue
                    variants.add(tuple(sorted(sub_variant_list + [neighbor])))
        if solver.verbose:
            print(f"{size}: {len(variants)}")
        return variants
    
    def can_reach_cell_set(self, cell_set):
        return bool(cell_set & self.all_possible_cells)
    
    def can_set_be_included_in_island(self, cell_set):
        return any(cell_set <= variant.cells for variant in self.variants)

    def get_variants_reaching_sets(self, additional_forced_sets):
        return [variant for variant in self.variants if all(variant.cells & s for s in additional_forced_sets)]

    def get_reaching_variants(self, cell_set):
        return [v for v in self.variants if v.cells & cell_set]
    
    def get_reach_blocking_variants(self, cell_set):
        return [v for v in self.variants if (intersection := v.extended_cells & cell_set) and not (intersection & v.cells)]

    def get_variants_for_chaining(self):
        return self.variants
    
    def get_variants_for_blocking(self):
        return self.variants

    def remove_sea_splitting_variants(self, possible_sea_graph: nx.Graph):
        variants_to_remove = []
        if len(self.variants) >= MAX_VARIANTS_PER_ISLAND:
            for variant in tqdm(self.variants):
                sea_copy = possible_sea_graph.copy()
                sea_copy.remove_nodes_from(variant.cells)
                if not nx.is_connected(sea_copy):
                    variants_to_remove.append(variant)
        else:
            for variant in self.variants:
                sea_copy = possible_sea_graph.copy()
                sea_copy.remove_nodes_from(variant.cells)
                if not nx.is_connected(sea_copy):
                    variants_to_remove.append(variant)
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        return len(variants_to_remove) > 0


class UncluedIsland(IslandInterface):
    """
    Holds the variants of an island based on a known island point, which is not yet connected to a specific clue.
    """
    def __init__(self, variants, clouds, solver, original_set):
        super().__init__(variants, solver, n_clues=0)
        self.clouds = clouds
        self.original_set = original_set

    @staticmethod
    def from_deduced_cells(deduced_cells, solver):
        """Island must include at least one of deduced cells."""
        variants = []
        clouds = []
        for island in solver.clued_islands:
            # This can generate either a list of variants or a cloud island.
            try:
                result = island.get_variants_reaching_sets([deduced_cells])
            except InvalidCloud:
                pass
            if isinstance(result, list):
                variants += result
            else:
                clouds.append(result)
        return UncluedIsland(variants, clouds, solver, deduced_cells)    

    def _clean_clouds(self):
        clouds_removed = False
        for cloud in list(self.clouds):
            try:
                graph = cloud.graph
            except InvalidCloud:
                self._remove_cloud(cloud)
                clouds_removed = True
        return clouds_removed        

    def _remove_cloud(self, cloud):
        cloud.original_cloud.sub_clouds.remove(cloud)
        for variant in cloud.variants:
            if cloud in variant.islands:
                variant.islands.remove(cloud)
        self.clouds.remove(cloud)

    def disappear_if_redundant(self, silent=False):
        # self destruct if duplicating another island.
        if len(self.variants) == 0:
            assert len(self.clouds) > 0
            if len(self.clouds) == 1:
                # no variants, one cloud
                self._disappear(silent)
                return True
            return False
        if self.clouds:
            return False
        n_islands_in_variants = len(set.intersection(*[variant.islands for variant in self.variants]))
        if n_islands_in_variants > 1:
            # all variants belong to the same island (other than this one), no clouds.
            self._disappear(silent)
            return True
        return False
    
    def _disappear(self, silent=False):
        if not silent:
            print("removing unclued island")
        for variant in self.variants:
            variant.islands.remove(self)
        self.solver.unclued_islands = [island for island in self.solver.unclued_islands if island is not self]
        if self.clouds:
            self.clouds[0].force_reaching_cell_set(self.original_set)

    @property
    def known_cells(self):
        self._clean_clouds()
        if self._known_cells is None:
            sets = [variant.cells for variant in self.variants] + [cloud.known_cells for cloud in self.clouds]
            self._known_cells = set.intersection(*sets)
        return self._known_cells

    @property
    def all_possible_cells(self):
        self._clean_clouds()
        if self._all_possible_cells is None:
            sets = [variant.cells for variant in self.variants] + [cloud.all_possible_cells for cloud in self.clouds]
            self._all_possible_cells = set.union(*sets)
        return self._all_possible_cells
    
    @property
    def blocked_cells(self):
        self._clean_clouds()
        if self._blocked_cells is None:
            sets = [variant.extended_cells for variant in self.variants] + [cloud.blocked_cells for cloud in self.clouds]
            self._blocked_cells = set.intersection(*sets)
        return self._blocked_cells

    def remove_variant(self, variant):
        """This should not be called directly
        The way to remove a variant form all islands is to use IslandVariant.remove() - which will call remove on all relevant islands
        """
        self.variants.remove(variant)
        if not self.variants and not self.clouds:
            raise NoPossibleSolution(f"No variants left when removing variant {variant.cells} from {self}")
        self._clear_cache()

    def can_set_be_included_in_island(self, cell_set):
        self._clean_clouds()
        return any(cell_set <= variant.cells for variant in self.variants) or any(cell_set <= cloud.all_possible_cells for cloud in self.clouds)

    def force_reaching_cell_set(self, cell_set):
        variants_to_remove = [variant for variant in self.variants if not(variant.cells & cell_set)]
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        clouds_affected = False
        for cloud in list(self.clouds):
            try:
                if cloud.force_reaching_cell_set(cell_set):
                    clouds_affected = True
            except InvalidCloud:
                self._remove_cloud(cloud)
                clouds_affected = True
        return len(variants_to_remove) > 0 or clouds_affected

    def block_from_island(self, blocking_island):
        blocked_cells = blocking_island.blocked_cells
        possible_blocker_islands = set([blocking_island] + blocking_island.get_cloud_origins())
        variants_to_remove = [variant for variant in self.variants 
                              if not (possible_blocker_islands & variant.islands) 
                              and (variant.cells & blocked_cells)]
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        clouds_affected = False
        for cloud in list(self.clouds):
            if cloud.original_cloud in possible_blocker_islands:
                continue
            try:
                if cloud.block_from_island(blocking_island):
                    clouds_affected = True
            except InvalidCloud:
                self._remove_cloud(cloud)
                clouds_affected = True
        return len(variants_to_remove) > 0 or clouds_affected

    def block_from_cell_set(self, blocking_set):
        variants_to_remove = [variant for variant in self.variants if (variant.cells & blocking_set)]
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
        clouds_affected = False
        for cloud in self.clouds:
            try:
                if cloud.block_from_cell_set(blocking_set):
                    clouds_affected = True
            except InvalidCloud:
                self._remove_cloud(cloud)
                clouds_affected = True
        return len(variants_to_remove) > 0

#    def block_from_island_variants(self, blocking_island):
        # We only block our variants, nothing to be done about our sub clouds.
        # also, because clouds (or unclued with clouds) don't generate blocking variants, non need to worry
        # about cloud origins of the blocking island.
        # In short, this is just like the basic method from the interface, no changes needed.

    def convert_sub_clouds(self):
        self._clean_clouds()
        clouds_to_remove = []
        for cloud in self.clouds:
            try:
                variants = set(cloud.get_all_variants())
                self.variants |= variants
                cloud.original_cloud.variants |= variants
                clouds_to_remove.append(cloud)
            except TooManyVariants:
                pass
        self.clouds = [c for c in self.clouds if c not in clouds_to_remove]
        return len(clouds_to_remove) > 0

    def get_cloud_origins(self):
        origins = set()
        if self.variants:
            origins = set.union(*[v.islands for v in self.variants])
        for cloud in self.clouds:
            origins.add(cloud) # probably unnecessary?
            origins.add(cloud.original_cloud)
        return list(origins)

    def get_variants_for_blocking(self):
        # if we have clouds, then our list of variants is not really comprehensive,
        # and we can't block other islands based on conflicting with it.
        if len(self.clouds) > 0:
            return []
        return self.variants

    def get_size_string(self):
        self._clean_clouds()
        return ''.join([str(len(self.variants))] + [cloud.get_size_string() for cloud in self.clouds])

class CloudIsland(CluedIsland):
    """
    When an island has too many variants, we can forego keeping track of them, and instead just track the set of reachable cells.
    """

    def __init__(self, initial_loc, graph, forced_sets, variants, solver, original_cloud=None):
        self.initial_loc = initial_loc
        self._graph = graph
        self.forced_sets = forced_sets
        self.variants = set(variants)
        self.solver = solver
        self.size = solver.clues[initial_loc]
        self.original_cloud = original_cloud or self # In sub clouds created as part of an unclued island, this will refer back to the original island.
        self.sub_clouds = []
        self._clear_cache()

    @staticmethod
    def from_initial_loc(initial_loc, excluded_cell_set, solver):
        graph: nx.Graph = nx.grid_2d_graph(solver.n_rows, solver.n_cols)
        for cell in excluded_cell_set:
            graph.remove_node(cell)
        return CloudIsland(initial_loc, graph, [{initial_loc}], set(), solver)
    
    def copy(self):
        return CloudIsland(self.initial_loc, self._graph.copy(), self.forced_sets.copy(), self.variants.copy(), self.solver, original_cloud=self)

    def _clear_cache(self):
        self._graph_updated = False
        self._all_possible_cells = None
        self._known_cells = None
        self._blocked_cells = None

    def _update_graph(self):
        tree_edges = self.size - 1
        if self.initial_loc not in self._graph:
            raise InvalidCloud
        self._graph: nx.Graph = nx.ego_graph(self._graph, self.initial_loc, radius=tree_edges).copy()
        for i in range(len(self.forced_sets)):
            self.forced_sets[i] = self.forced_sets[i] & self._graph.nodes()
            if not self.forced_sets[i]:
                raise InvalidCloud()
        for i, forced_set in enumerate(self.forced_sets):
            forced_set_distances = nx.multi_source_dijkstra_path_length(self._graph, forced_set)
            nx.set_node_attributes(self._graph, forced_set_distances, str(i))
        # We want to know if each node in the graph has a steiner tree of weight k:=tree_edges with all forced sets.
        # As a bound, we check that the total sum of paths between all forced sets (if adding the node as a set)
        # doesn't exceed k * int ((n_sets / 2) ** 2)
        total_path_length = sum(
            min(self._graph.nodes[cell][str(j)] for cell in self.forced_sets[i])
            for i, j in itertools.combinations(range(len(self.forced_sets)), 2)
        )
        max_total_length_with_extra_node = tree_edges * int(((len(self.forced_sets) + 1) / 2) ** 2)
        budget = max_total_length_with_extra_node - total_path_length
        if budget < 0:
            raise InvalidCloud
        cells_to_remove = [cell for cell in self._graph.nodes() if sum(self._graph.nodes[cell][str(i)] for i in range(len(self.forced_sets))) > budget]
        self._graph.remove_nodes_from(cells_to_remove)
        if len(self._graph) < self.size:
            raise InvalidCloud()
        self._graph_updated = True

    @staticmethod
    def from_initial_clues(initial_loc, solver):
        excluded_cell_set = set()
        for cell in solver.clues:
            if cell == initial_loc:
                continue
            excluded_cell_set.add(cell)
            for neighbor in solver.get_neighbors(cell):
                excluded_cell_set.add(neighbor)
        return CloudIsland.from_initial_loc(initial_loc, excluded_cell_set, solver)

    @property
    def graph(self):
        if not self._graph_updated:
            self._update_graph()
        return self._graph

    @property
    def known_cells(self):
        if self._known_cells is None:
            self._set_known_cells()
        return self._known_cells

    @property
    def all_possible_cells(self):
        if self._all_possible_cells is None:
            self._all_possible_cells = set(self.graph.nodes())
        return self._all_possible_cells

    @property
    def blocked_cells(self):
        if self._blocked_cells is None:
            self._set_blocked_cells()
        return self._blocked_cells

    def _set_known_cells(self):
        self._known_cells = set()
        for s in self.forced_sets:
            if len(s) == 1:
                self._known_cells |= s
        g = self.graph
        for articulation_point in nx.articulation_points(g):
            if articulation_point in self._known_cells:
                continue
            g_copy = g.copy()
            g_copy.remove_node(articulation_point)
            components = list(nx.connected_components(g_copy))
            component_sets = [set(component) | {articulation_point} for component in components]
            # if you have a forced set on each side of the point, the point must be in the island
            # also, if you have a forced set on one side, and that side is too small to hold the entire island, the point must be in the island
            forced_inclusions = [any(forced_set <= component_set for forced_set in self.forced_sets) for component_set in component_sets]
            if all(forced_inclusions) or any(len(s) <= self.size and inclusion for s, inclusion in zip(component_sets, forced_inclusions)):
                self._known_cells.add(articulation_point)

    def _set_blocked_cells(self):
        known_cells = self.known_cells
        self._blocked_cells = known_cells.copy()
        for cell in known_cells:
            for neighbor in self.solver.get_neighbors(cell):
                self._blocked_cells.add(neighbor)

    def remove_variant(self, variant):
        """This should not be called directly
        The way to remove a variant form all islands is to use IslandVariant.remove() - which will call remove on all relevant islands
        """
        self.variants.remove(variant)

    def can_set_be_included_in_island(self, cell_set):
        if len(cell_set) > self.size:
            return False
        if not cell_set <= self.all_possible_cells:
            return False
        g = self.graph
        max_distance_from_forced_sets = max(min(g.nodes[cell][str(i)] for cell in cell_set) for i in range(len(self.forced_sets)))
        return len(cell_set) + max_distance_from_forced_sets <= self.size

    def force_reaching_cell_set(self, cell_set):
        if any(existing_set <= cell_set for existing_set in self.forced_sets):
            return False
        self.forced_sets = [s for s in self.forced_sets if not s >= cell_set]
        self.forced_sets.append(set(cell_set))
        self._clear_cache()
        for sub_cloud in self.sub_clouds:
            sub_cloud.force_reaching_cell_set(cell_set)
        # this will usually be correct, perhaps we're being a little too conservative.
        return True

    def block_from_island(self, blocking_island):
        if any(blocking_island in variant.islands for variant in self.variants):
            return False
        if self in blocking_island.get_cloud_origins():
            return False
        return self.block_from_cell_set(blocking_island.blocked_cells)
    
    def block_from_cell_set(self, blocking_set):
        relevant_blocked_cells = blocking_set & self._graph.nodes()
        if not relevant_blocked_cells:
            return False
        self._graph.remove_nodes_from(relevant_blocked_cells)
        self._clear_cache()
        for sub_cloud in self.sub_clouds:
            sub_cloud.block_from_cell_set(blocking_set)
        return True

    def block_from_island_variants(self, blocking_island):
        return False

    def remove_sea_splitting_variants(self, possible_sea_graph: nx.Graph):
        return False

    def get_reaching_variants(self, cell_set):
        # reaching variants are requested to check if other islands' blocking variants need to be removed.
        # we create fake variants with each of the reached squares, so that blockers are only removed if they block all of them.
        reachable_cells = cell_set & self.all_possible_cells
        return [IslandVariant({cell}, self.solver) for cell in reachable_cells]
    
    def get_reach_blocking_variants(self, cell_set):
        # reach blocking variants are requested so that they are considered for removal.  a cloud island has no variants to remove.
        return []

    def get_variants_for_chaining(self):
        # variants for chaining are for checking if islands touch each other to form a chain.
        # we create a fake variant with all the known points of the island.  If anything touches this, it touches the island.
        # We also send all actual variants we have created (for unclued islands), in case one of them can be removed.
        # If the fake islands is removed, that might raise an exception.
        return [IslandVariant(self.known_cells, self.solver) for cell in set.union(*self.forced_sets)] + list(self.variants)

    def get_variants_for_blocking(self):
        return []

    def to_variants_based(self):
        return CluedIsland(self.get_all_variants(), self.solver)

    def get_all_variants(self):
        try:
            variant_sets = self._direct_make_variants()
        except TooManyVariants:
            variant_sets = CloudIsland._recursive_make_variants(self.initial_loc, self.size, self.size, self.graph, len(self.forced_sets), self.solver)
        variants = [IslandVariant(variant, self.solver) for variant in variant_sets]
        for variant in variants:
            variant.islands.add(self.original_cloud)
        return variants

    def get_variants_reaching_sets(self, additional_forced_sets=None):
        """
        Creates variants reaching an unclued island.
        If there are too many, returns a copy this cloud, restricted to reach the unclued island.
        """
        additional_forced_sets = additional_forced_sets or []
        for s in additional_forced_sets:
            if not(s & self.graph.nodes()):
                return []
        sub_cloud = self.copy()
        for forced_set in additional_forced_sets:
            sub_cloud.force_reaching_cell_set(forced_set)
        graph = sub_cloud.graph
        try:
            new_variants = [IslandVariant(variant, self.solver) for variant in CloudIsland._recursive_make_variants(self.initial_loc, self.size, self.size, graph, len(sub_cloud.forced_sets), self.solver)]
        except TooManyVariants:
            self.sub_clouds.append(sub_cloud)
            return sub_cloud
        for variant in new_variants:
            variant.add_island(self)
            self.variants.add(variant)
        return new_variants

    @staticmethod
    def _recursive_make_variants(loc, size, max_size, graph: nx.Graph, n_forced_sets, solver):
        """
        Recursively build all island variants (sub-graphs of the given graph) of given size starting from loc.
        The distance from each cell to each forced set is in the graph,and we use that to prune variants that don't
        have enough remaining size to reach each forced set.
        """
        if size == 1:
            return {(loc,)}
        variants = set()
        sub_variants = CloudIsland._recursive_make_variants(loc, size-1, max_size, graph, n_forced_sets, solver)
        if len(sub_variants) >= MAX_VARIANTS_PER_ISLAND:
            raise TooManyVariants()
        reach = max_size - size
        set_keys = [str(i) for i in range(n_forced_sets)]
        for sub_variant in sub_variants:
            sub_variant_list = list(sub_variant)
            for cell in sub_variant:
                for neighbor in graph.neighbors(cell):
                    if neighbor in sub_variant:
                        continue
                    new_variant = sub_variant_list + [neighbor]
                    # check we have cells to reach all forced sets.
                    if all(
                        min(graph.nodes[cell][k] for cell in new_variant) <= reach
                        for k in set_keys
                    ):
                        variants.add(tuple(sorted(new_variant)))
        if solver.verbose:
            print(f"{size}: {len(variants)}")
        return variants

    def _direct_make_variants(self):
        n_variants = math.comb(len(self.all_possible_cells), self.size)
        if n_variants > MAX_VARIANTS_PER_ISLAND:
            raise TooManyVariants
        variant_sets = []
        for variant_tuple in itertools.combinations(self.all_possible_cells, self.size):
            variant_set = set(variant_tuple)
            if not all(forced_set & variant_set for forced_set in self.forced_sets):
                continue
            if nx.is_connected(self.graph.subgraph(variant_tuple)):
                variant_sets.append(variant_set)
        return variant_sets

    def get_cloud_origins(self):
        return [self]

    def get_size_string(self):
        return f"C{len(self.all_possible_cells)}"


class Solver:
    def __init__(self, n_rows, n_cols, clues, solution_island_cells=None, connection_cost_in_mip=False, verbose=False, solver_logs=False):
        start_init_time = time()
        self.n_rows = n_rows
        self.n_cols = n_cols
        self.clues = clues
        self._dump_grid()
        self.solution_island_cells = solution_island_cells
        self.connection_cost_in_mip = connection_cost_in_mip
        self.verbose = verbose
        self.solver_logs = solver_logs
        print(f"{self.n_rows}x{self.n_cols} = {self.n_rows * self.n_cols} grid; {len(self.clues)} clues totalling {sum(self.clues.values())}; {self.n_rows * self.n_cols - sum(self.clues.values())} sea squares")
        self.all_dominoes = self._get_dominoes()
        self.all_squares = self._get_squares()
        self.clued_islands = [] # one for each clue in the grid
        self.unclued_islands = [] # may be added based on unaffiliated deduced white points
        self.previous_known_sea_cells = set()
        self.previous_known_island_cells = set()
        self.variant_islands = defaultdict(set) # for each variant, the set of islands it is in.
        # If a clued cloud is invalid, we have no possible solution.
        # An InvalidCloud from an unclued subcloud should be caught before getting here.
        try:
            self._generate_islands()
        except InvalidCloud:
            raise NoPossibleSolution
        print("island generation time:", time() - start_init_time)

    def _dump_grid(self):
        chars = [['.'] * self.n_cols for _ in range(self.n_rows)]
        for cell, clue in self.clues.items():
            chars[cell[0]][cell[1]] = num2char(clue)
        strings = [''.join(row) + '\n' for row in chars]
        with open('/tmp/nurikabe.txt', 'w') as f:
            f.writelines(strings)

    @staticmethod
    def from_filenames(puzzle_filename, solution_filename=None, connection_cost_in_mip=False, verbose=False, solver_logs=False):
        n_rows, n_cols, clues = Solver._parse_grid(puzzle_filename)
        solution_island_cells = Solver._parse_solution(solution_filename)
        return Solver(n_rows, n_cols, clues, solution_island_cells, connection_cost_in_mip, verbose, solver_logs)

    @staticmethod
    def _parse_grid(puzzle_filename):
        with open(puzzle_filename) as f:
            grid_strings = [row.strip() for row in f if not row.startswith("#")] # ignore comments
        grid = [str2row(s) for s in grid_strings]
        n_rows = len(grid)
        n_cols = len(grid[0])
        clues = {}
        for r, row in enumerate(grid):
            for c, size in enumerate(row):
                if size > 0:
                    clues[(r, c)] = size
        return n_rows, n_cols, clues

    @staticmethod
    def _parse_solution(solution_filename):
        solution_island_cells = set()
        if solution_filename:
            with open(solution_filename) as f:
                solution_strings = [row.strip() for row in f if not row.startswith("#")] # ignore comments
            for r, row in enumerate(solution_strings):
                for c, cell in enumerate(row):
                    if cell != '.':
                        solution_island_cells.add((r, c))
        return solution_island_cells

    @property
    def all_islands(self):
        return self.clued_islands + self.unclued_islands

    def solve(self):
        start_model_init_time = time()
        self._generate_mip_model()
        start_solve_time = time()
        print("model init time:", start_solve_time - start_model_init_time)
        iters = 0
        while True:
            if self.solver_logs:
                self.model.solve()
            else:
                self.model.solve(pulp.PULP_CBC_CMD(msg=0))
            if self.model.status != 1:
                print("Status: ", pulp.LpStatus[self.model.status])
                raise NoPossibleSolution()
            island_cells = set()
            for choice, variant_cells in zip(self.island_choices.values(), self.flat_variant_cells):
                if pulp.value(choice) == 1:
                    island_cells |= variant_cells
            sea_cells = set((r, c) for r in range(self.n_rows) for c in range(self.n_cols)) - island_cells
            component, remainder = self._find_component_and_remainder(sea_cells)
            contiguous = not remainder
            iters += 1
            print(f"{'' if contiguous else 'NOT '}CONTIGUOUS {iters} {time() - start_solve_time}")
            if self.verbose:
                self._show_solution(island_cells)
            if contiguous:
                break
            disconnecting_choices = [
                choice for choice, variant in zip(self.island_choices.values(), self.flat_variant_cells)
                if pulp.value(choice) == 1 and self._is_touching(variant, component) and self._is_touching(variant, remainder)
            ]
            self.model += sum(disconnecting_choices) <= len(disconnecting_choices) - 1
        
        self._update_progress(island_cells, set(itertools.product(range(self.n_rows), range(self.n_cols))) - island_cells)
        if not self.verbose:
            self._show_solution(island_cells)
        print("solve_time:", time() - start_solve_time)
        return island_cells

    def _show_partial_solution(self):
        known_sea_cells, known_island_cells = self._get_known_sea_and_island_cells()
        self._show_solution(known_island_cells, known_sea_cells)

    def _show_solution(self, known_island_cells, known_sea_cells=None):
        """
        if known_sea_cells is None, assume anything not known to be island is sea
        """
        if known_sea_cells is None:
            known_sea_cells = set(itertools.product(range(self.n_rows), range(self.n_cols))) - known_island_cells
        solution_chars = [
            [
                self._cell2char((r, c), known_sea_cells, known_island_cells)
                for c in range(self.n_cols)
            ]
            for r in range(self.n_rows)
        ]
        for row in solution_chars:
            print(''.join(row).upper())

    def _update_progress(self, known_island_cells=None, known_sea_cells=None):
        if known_island_cells is None or known_sea_cells is None:
            known_sea_cells, known_island_cells = self._get_known_sea_and_island_cells()
        if known_island_cells == self.previous_known_island_cells and known_sea_cells == self.previous_known_sea_cells:
            return
        self.previous_known_island_cells = known_island_cells
        self.previous_known_sea_cells = known_sea_cells
        partial_solution = [[-1] * self.n_cols for _ in range(self.n_rows)]
        for cell in known_island_cells:
            partial_solution[cell[0]][cell[1]] = 0
        for cell in known_sea_cells:
            partial_solution[cell[0]][cell[1]] = 1
        progress.step(partial_solution)

    def _cell2char(self, cell, known_sea_cells, known_island_cells):
        if cell in self.clues:
            return num2char(self.clues[cell])
        if cell in known_island_cells:
            return '#'
        if cell in known_sea_cells:
            return '.'
        return ' '

    def _generate_islands(self):
        self._generate_initial_clued_islands()
        self._pre_solve()
        if self.solution_island_cells:
            for i, island in enumerate(self.clued_islands):
                assert any(variant.cells <= self.solution_island_cells for variant in island.variants), f"clue {i+1}: {island.variants}"
        self._show_partial_solution()

    def _generate_initial_clued_islands(self):
        self.clued_islands = [CluedIsland.from_initial_clues(loc, self) for loc in self.clues]
        for island in self.clued_islands:
            if not isinstance(island, CloudIsland) and len(island.variants) == 0:
                raise(NoPossibleSolution)
        self._update_progress()
        self._report_culling("initial generation")

    def _pre_solve(self):
        while True:
            if self._cull_variants_by_neighbors():
                continue
            if self._cull_variants_by_reach():
                continue
            if self._cull_variants_by_sea_continuity():
                continue
            if self._cull_variants_by_neighbor_variants():
                continue
            if self._cull_variants_by_enhanced_reach():
                continue
            self._remove_unclued_islands()
            if self._add_unclued_islands(add_from_dominos=False):
                continue
            if self._remove_sea_splitting_variants():
                continue
            if self._remove_island_chains():
                continue
            # Adding unclued islands from dominos doesn't help much, but blocks combinations.
            # if self._add_unclued_islands(add_from_dominos=True):
            #     continue
            if self._convert_cloud_islands():
                continue
            if self._combine_islands():
                continue
            if any(isinstance(island, CloudIsland) for island in self.clued_islands):
                raise ProblemTooHard("Couldn't convert all clouds")
            return
            
    def _report_culling(self, description):
        print(f"by {description:25}", self._make_island_sizes_string())
        if self.verbose:
            self._show_partial_solution()

    def _make_island_sizes_string(self):
        strings = [' '.join(island.get_size_string() for island in islands)
                   for islands in (self.clued_islands, self.unclued_islands)]
        return f"{strings[0]} ; {strings[1]}"

    def _cull_variants_by_reach(self):
        """if there's only one clued island that can reach a pool, that island must reach the pool (remove other variants)"""
        changes_made = False
        for square in self.all_squares:
            square_set = set(square)
            does_reach_square = [island.can_reach_cell_set(square_set) for island in self.clued_islands]
            n_islands_reaching_square = sum(does_reach_square)
            if n_islands_reaching_square > 1:
                continue
            if n_islands_reaching_square == 0:
                raise NoPossibleSolution()
            for island, does_reach in zip(self.clued_islands, does_reach_square):
                if does_reach:
                    new_changes = island.force_reaching_cell_set(square_set)
                    if new_changes:
                        self._update_progress()
                    changes_made = changes_made or new_changes
        if changes_made:
            self._report_culling("reach")
        return changes_made

    def _cull_variants_by_enhanced_reach(self):
        """cull variants that don't reach a pool, but block other islands' variants from doing so."""
        changes_made = False
        for square in self.all_squares:
            square_set = set(square)
            reaching_variants = [island.get_reaching_variants(square_set) for island in self.clued_islands]
            blocking_variants = [island.get_reach_blocking_variants(square_set) for island in self.clued_islands]
            for i in range(len(self.clued_islands)):
                variants_to_remove = []
                for blocker in blocking_variants[i]:
                    if all(blocker.extended_cells & reacher.cells
                           for j in range(len(self.clued_islands)) if i != j
                           for reacher in reaching_variants[j]):
                        variants_to_remove.append(blocker)
                if not variants_to_remove:
                    continue
                blocking_variants[i] = [v for v in blocking_variants[i] if v not in variants_to_remove]
                for variant in variants_to_remove:
                    variant.remove_from_all_islands()
                self._update_progress()
                changes_made = True
        if changes_made:
            self._report_culling("enchanced reach")
        return changes_made

    def _cull_variants_by_neighbors(self):
        """cells that are on or adjacent to every variant of the same island, are unavailable to other islands.
        """
        changes_made = False
        for island in self.all_islands:
            # # in case an unclued island has self destructed
            # if island not in self.all_islands:
            #     continue
            # Now that unclued islands self destruct outside the loop, this shouldn't happen
            assert island in self.all_islands
            for other_island in self.all_islands:
                if other_island is island:
                    continue
                new_changes = other_island.block_from_island(island)
                if new_changes:
                    self._update_progress()
                changes_made = changes_made or new_changes
        if changes_made:
            self._report_culling("neighbors")
        return changes_made

    def _cull_variants_by_neighbor_variants(self):
        """
        Remove variants of island A that conflict with every variant of island B.
        """
        changes_made = False
        for island in self.all_islands:
            for other_island in self.all_islands:
                if other_island is island:
                    continue
                new_changes = other_island.block_from_island_variants(island)
                if new_changes:
                    self._update_progress()
                changes_made = changes_made or new_changes
        if changes_made:
            self._report_culling("neighbor variants")
        return changes_made

    def _cull_variants_by_sea_continuity(self):
        """
        Find points that are necessary to connect two known sea cells, and make them sea cells
        """
        changes_made = False
        known_sea_cells, known_island_cells = self._get_known_sea_and_island_cells()
        possible_sea_graph = self._make_possible_sea_graph()
        additional_sea_cells = set()
        for articulation_point in nx.articulation_points(possible_sea_graph):
            if articulation_point in known_sea_cells:
                continue
            sea_copy = possible_sea_graph.copy()
            sea_copy.remove_node(articulation_point)
            components = list(nx.connected_components(sea_copy))
            # if point splits possible sea to at least two parts with sea points, it must be a known sea point
            if sum(self._does_component_have_sea(component, known_sea_cells) for component in components) >= 2:
                additional_sea_cells.add(articulation_point)
        if additional_sea_cells:
            for island in self.all_islands:
                new_changes = island.block_from_cell_set(additional_sea_cells)
                if changes_made:
                    self._update_progress()
                changes_made = changes_made or new_changes
        if changes_made:
            self._report_culling("sea continuity")
        return changes_made

    def _make_possible_sea_graph(self):
        while True:
            known_sea_cells, known_island_cells = self._get_known_sea_and_island_cells()
            graph: nx.Graph = nx.grid_2d_graph(self.n_rows, self.n_cols)
            for cell in known_island_cells:
                graph.remove_node(cell)
            # if possible sea is not connected, all components except one (the largest) are not really sea - they should join the surrounding island
            if nx.is_connected(graph):
                return graph
            sea_components = list(nx.connected_components(graph))
            max_size = max(len(component) for component in sea_components)
            for component in sea_components:
                if len(component) == max_size:
                    continue
                for island in self.all_islands:
                    if self._is_touching(island.known_cells, component):
                        for cell in component:
                            island.force_reaching_cell_set({cell})
 
    def _does_component_have_sea(self, component, known_sea_cells):
        if component & known_sea_cells:
            return True
        return not any(island.can_set_be_included_in_island(component) for island in self.clued_islands)

    def _remove_unclued_islands(self):
        islands_removed = False
        for island in list(self.unclued_islands): # copy unclued_islands because this loop can change the list.
            if island.disappear_if_redundant():
                islands_removed = True
        return islands_removed

    def _add_unclued_islands(self, add_from_dominos=False):
        known_sea_cells, known_island_cells = self._get_known_sea_and_island_cells_without_new_deduced_islands()
        islands_added = False
        for square in self.all_squares:
            square_set = set(square)
            known_in_square = square_set & known_sea_cells
            if len(known_in_square) <= 1:
                continue
            if len(known_in_square) == 2:
                if not add_from_dominos:
                    continue
                # only make the island if the 2 known sea cells are a domino.
                xs = set(cell[0] for cell in known_in_square)
                ys = set(cell[1] for cell in known_in_square)
                if len(xs) == 2 and len(ys) == 2:
                    continue
            deduced_island_cells = square_set - known_sea_cells
            if deduced_island_cells & known_island_cells:
                continue
            new_island = UncluedIsland.from_deduced_cells(deduced_island_cells, self)
            self.unclued_islands.append(new_island)
            if new_island.disappear_if_redundant(silent=True):
                continue
            print(f"adding unclued island around {deduced_island_cells}")
            self._update_progress()
            known_island_cells |= new_island.known_cells
            islands_added = True
        if islands_added:
            self._report_culling("adding unclued islands")
        return islands_added

    def _remove_sea_splitting_variants(self):
        changes_made = False
        possible_sea_graph = self._make_possible_sea_graph()
        for island in self.clued_islands:
            new_changes = island.remove_sea_splitting_variants(possible_sea_graph)
            if new_changes:
                self._update_progress()
            changes_made = changes_made or new_changes
        if changes_made:
            self._report_culling("enhanced sea continuity")
        return changes_made

    def _get_known_sea_and_island_cells(self):
        known_sea_cells, known_island_cells = self._get_known_sea_and_island_cells_without_new_deduced_islands()
        for square in self.all_squares:
            square_set = set(square)
            if len(square_set & known_sea_cells) == 3:
                known_island_cells |= (square_set - known_sea_cells)
        return known_sea_cells, known_island_cells

    def _get_known_sea_and_island_cells_without_new_deduced_islands(self):
        possible_island_cells = set.union(*[island.all_possible_cells for island in self.clued_islands])
        known_sea_cells = set(itertools.product(range(self.n_rows), range(self.n_cols))) - possible_island_cells
        known_island_cells = set.union(*[island.known_cells for island in self.all_islands])
        return known_sea_cells, known_island_cells

    def _remove_island_chains(self):
        # If we have combination islands, the chaining logic will break (as an "island" may not be contiguous, and the sea may cross it).
        if len(self.clued_islands) < len(self.clues):
            return False 
        variants = [island.get_variants_for_chaining() for island in self.clued_islands]
        # The coast variant has all coastal cells as extended cells, so we can check variant.cells & coast_variant.extended_cells_with_diagonals.
        # However, note that the other way won't work, because the coast variant has no cells.
        coast_variant = IslandVariant({}, self)
        coast_variant.extended_cells_with_diagonals = {(r, c) for r, c in itertools.product(range(self.n_rows), range(self.n_cols))
                                                       if r in (0, self.n_rows - 1) or c in (0, self.n_cols - 1)}
        coast_island = UncluedIsland([coast_variant], [], self, set())
        chain_islands = self.clued_islands + [coast_island]
        variants.append([coast_variant])
        touched_islands_per_variant = [
            [
                {
                    touched_island
                    for touched_island, touched_variants in zip(chain_islands, variants) 
                    if touched_island is not island and all(variant.cells & touched_variant.extended_cells_with_diagonals
                                                            for touched_variant in touched_variants)
                }
                for variant in island_variants
            ]
            for island, island_variants in zip(self.clued_islands, variants[:-1])
        ]
        touched_islands_per_island = [
            set.intersection(*touched_islands) for touched_islands in touched_islands_per_variant
        ]
        chain_graph = nx.Graph()
        for island, touched_islands in zip(self.clued_islands, touched_islands_per_island):
            for touched_island in touched_islands:
                chain_graph.add_edge(island, touched_island)
        # chain_graph contains edges that certainly exist (island A touches B).  
        # Now let's find pairs, where one of them must exist (island A touches B or C)
        necessary_edge_pairs = []
        for island, islands_touched_by_island, touched_islands_per_variant_list in zip(
            self.clued_islands, touched_islands_per_island, touched_islands_per_variant):
            touchable_islands = set.union(*touched_islands_per_variant_list) - islands_touched_by_island
            n = len(touched_islands_per_variant_list)
            all_bits = (1 << n) - 1
            mask = {i: 0 for i in touchable_islands}
            for i, touched_islands in enumerate(touched_islands_per_variant_list):
                for touched_island in touched_islands - islands_touched_by_island:
                    mask[touched_island] |= 1 << i
            pairs = itertools.combinations(touchable_islands, 2)
            for a, b in pairs:
                if (mask[a] | mask[b]) == all_bits:
                    necessary_edge_pairs.append(((island, a), (island, b)))
        # find variants that complete cycles.
        variants_to_remove = []
        for island, island_variants, islands_touched_by_island, touched_islands_per_variant_list in zip(
                self.clued_islands, variants[:-1], touched_islands_per_island, touched_islands_per_variant):
            for variant, islands_touched_by_variant in zip(island_variants, touched_islands_per_variant_list):
                additional_touched_islands = islands_touched_by_variant - islands_touched_by_island
                if not additional_touched_islands:
                    continue
                chain_graph_copy = chain_graph.copy()
                for touched_island in additional_touched_islands:
                    chain_graph_copy.add_edge(island, touched_island)
                if not nx.is_forest(chain_graph_copy):
                    variants_to_remove.append(variant)
                    continue
                for edge1, edge2 in necessary_edge_pairs:
                    if chain_graph_copy.has_edge(*edge1) or chain_graph_copy.has_edge(*edge2):
                        continue
                    for edge in (edge1, edge2):
                        chain_graph_copy.add_edge(*edge)
                        still_forest = nx.is_forest(chain_graph_copy)
                        chain_graph_copy.remove_edge(*edge)
                        if still_forest:
                            break
                    else:
                        variants_to_remove.append(variant)
                        break
        for variant in variants_to_remove:
            variant.remove_from_all_islands()
            self._update_progress()
        # For clouds, remove all points that create chains by themselves.
        cloud_cells_removed = False
        for island, islands_touched_by_island in zip(
                self.clued_islands, touched_islands_per_island):
            if not isinstance(island, CloudIsland):
                continue
            possible_cells = island.all_possible_cells
            cells_to_remove = []
            for cell in possible_cells:
                islands_touched_by_cell = {
                    touched_island
                    for touched_island, touched_variants in zip(chain_islands, variants)
                    if touched_island is not island and all(cell in touched_variant.extended_cells_with_diagonals
                                                            for touched_variant in touched_variants)
                }
                additional_touched_islands = islands_touched_by_cell - islands_touched_by_island
                if not additional_touched_islands:
                    continue
                chain_graph_copy = chain_graph.copy()
                for touched_island in additional_touched_islands:
                    chain_graph_copy.add_edge(island, touched_island)
                if not nx.is_forest(chain_graph_copy):
                    cells_to_remove.append(cell)
            if cells_to_remove:
                island.block_from_cell_set(cells_to_remove)
                cloud_cells_removed = True
                self._update_progress()
        changes_made = len(variants_to_remove) > 0 or cloud_cells_removed
        if changes_made:
            self._report_culling("island chains")
        return changes_made

    def _combine_islands(self):
        combinable_islands = [
            island for island in self.clued_islands
            if not isinstance(island, CloudIsland) and
            len(island.variants) > 1 and
            all(len(variant.islands) == 1 for variant in island.variants)
        ]
        best_combination_set = None
        best_islands = None
        best_cost = (1e8, 1.0) # lowest number of clues, than lowest survival rate for variants
        for island1, island2 in itertools.combinations(combinable_islands, 2):
            n_clues = island1.n_clues + island2.n_clues
            if n_clues > best_cost[0]:
                continue
            initial_n_combinations = len(island1.variants) * len(island2.variants)
            if initial_n_combinations > MAX_VARIANTS_PER_ISLAND:
                continue
            combinations = [
                comb for comb in itertools.product(island1.variants, island2.variants)
                if not(comb[0].cells & comb[1].extended_cells)
            ]
            survival_rate = len(combinations) / initial_n_combinations
            if survival_rate == 1.0:
                continue
            cost = (n_clues, survival_rate)
            if cost < best_cost:
                best_combination_set = combinations
                best_islands = (island1, island2)
                best_cost = cost
        if best_combination_set == None:
            return False
        variants = [IslandVariant(comb[0].cells | comb[1].cells, self) for comb in best_combination_set]
        new_island = CluedIsland(variants, self, n_clues=best_islands[0].n_clues + best_islands[1].n_clues)
        self.clued_islands = [island for island in self.clued_islands if island not in best_islands] + [new_island]
        print(f"combined islands with {len(best_islands[0].variants)} x {len(best_islands[1].variants)} = {len(best_islands[0].variants) * len(best_islands[1].variants)} variants; survival {len(best_combination_set)} ({best_cost[1]})")
        print(f"island with {best_islands[0].n_clues} clues:", best_islands[0].known_cells)
        print(f"island with {best_islands[1].n_clues} clues:", best_islands[1].known_cells)
        return True

    def get_neighbors(self, loc):
        neighbors = []
        for dir in directions:
            try:
                neighbors.append(self._get_neighbor(loc, dir))
            except OffGridException:
                pass
        return neighbors

    def get_neighbors_with_diagonals(self, loc):
        neighbors = []
        for dir in directions_with_diagonals:
            try:
                neighbors.append(self._get_neighbor(loc, dir))
            except OffGridException:
                pass
        return neighbors

    def _get_neighbor(self, loc, dir):
        r = loc[0] + dir[0]
        if not 0 <= r < self.n_rows:
            raise OffGridException
        c = loc[1] + dir[1]
        if not 0 <= c < self.n_cols:
            raise OffGridException
        return (r, c)

    def _get_dominoes(self):
        return [{(r, c), (r, c+1)} for r in range(self.n_rows) for c in range(self.n_cols - 1)] + \
               [{(r, c), (r+1, c)} for r in range(self.n_rows - 1) for c in range(self.n_cols)]

    def _get_squares(self):
        return [{(r, c),
                 (r+1, c),
                 (r, c+1),
                 (r+1, c+1)}
                 for r in range(self.n_rows - 1) for c in range(self.n_cols - 1)]

    def _find_component_and_remainder(self, cells):
        remainder = set(cells)
        component = []
        queue = {remainder.pop()}
        while queue:
            cell = queue.pop()
            component.append(cell)
            neighbors = self.get_neighbors(cell)
            for neighbor in neighbors:
                if neighbor in remainder:
                    remainder.remove(neighbor)
                    queue.add(neighbor)
        return component, remainder

    def _is_touching(self, cells1, cells2):
        cells2 = set(cells2)
        for cell in cells1:
            neighbors = self.get_neighbors(cell)
            for neighbor in neighbors:
                if neighbor in cells2:
                    return True
        return False

    def _convert_cloud_islands(self):
        conversions_made = False
        for island in self.unclued_islands:
            if island.convert_sub_clouds():
                conversion_made = True
        for i, island in enumerate(self.clued_islands):
            if isinstance(island, CloudIsland):
                try:
                    self.clued_islands[i] = island.to_variants_based()
                    for variant in self.clued_islands[i].variants:
                        variant.islands.remove(island)
                    conversions_made = True
                    self._update_progress()
                except TooManyVariants:
                    pass
        if conversions_made:
            self._report_culling("by cloud conversion")
        return conversions_made

    def _generate_mip_model(self):
        self.flat_variants = sum((list(island.variants) for island in self.clued_islands), [])
        self.flat_variant_cells = [variant.cells for variant in self.flat_variants]
        self.model = pulp.LpProblem(sense=pulp.LpMaximize)
        self.island_choices = pulp.LpVariable.dicts("Choice", range(len(self.flat_variants)), cat='Binary')
        # Choose one variant for each island
        current_i = 0
        for island in self.clued_islands:
            self.model += sum(self.island_choices[i] for i in range(current_i, current_i + len(island.variants))) == 1
            current_i += len(island.variants)
        # No two islands can share a domino (which also means they can't overlap)
        for domino in self.all_dominoes:
            overlapping_choices = [choice for choice, variant in zip(self.island_choices.values(), self.flat_variant_cells) if domino & variant]
            if len(overlapping_choices) > 1:
                self.model += sum(overlapping_choices) <= 1
        # There's at least one island in each square
        for square in self.all_squares:
            overlapping_choices = [choice for choice, variant in zip(self.island_choices.values(), self.flat_variant_cells) if square & variant]
            if len(overlapping_choices) == 0:
                raise NoPossibleSolution(f"Square with no reaching island: {square}")
            self.model += sum(overlapping_choices) >= 1
        # Require k-1 pairs of adjacent sea squares (if k is number of sea cells).  
        # This does not guarantee a connected solution (loops negate disconnections),
        # but removes some disconnected solutions without removing the connected one, reducing the number of iterations needed.
        # The downside is that solving the mip in each iteration takes longer.
        if self.connection_cost_in_mip:
            is_sea = {}
            for row in range(self.n_rows):
                for col in range(self.n_cols):
                    cell_choices = [choice for choice, variant in zip(self.island_choices.values(), self.flat_variant_cells) if (row, col) in variant]
                    is_sea[(row, col)] = 1 - sum(cell_choices) if cell_choices else 1
            connection_variables = [pulp.LpVariable(f"connection_{i}", cat='Binary') for i in range(len(self.all_dominoes))]
            for connection_variable, domino in zip(connection_variables, self.all_dominoes):
                for cell in domino:
                    self.model += connection_variable <= is_sea[cell]
            n_sea_cells = self.n_rows * self.n_cols - sum(self.clues.values())
            self.model += sum(connection_variables) >= n_sea_cells - 1


if __name__ == '__main__':
    main()
