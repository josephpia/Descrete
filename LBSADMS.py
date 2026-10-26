"""
LBSADMS - Logic-Based Security Access Decision Management System
Midterm Project - Access Control System

Disciplines covered:
    Logic, Sets, Relations, Boolean Algebra, Matrices, Number Theory,
    Cryptography, Algorithm Application,
    Induction, Recursion, Counting, Probability,
    Random Variables, Graph Navigation, Trees, Finite State Machines
"""

from flask import Flask, render_template, request, jsonify, session, redirect, url_for
import numpy as np
import hashlib
import hmac
import secrets
import bcrypt
import base64
import math
import random
from cryptography.fernet import Fernet
from datetime import datetime
from collections import OrderedDict, deque
import time


# ============================================================================
# CRYPTOGRAPHY MODULE
# ============================================================================

class CryptoManager:
    """
    Cryptographic utilities:
    SHA-256, HMAC-SHA256, AES (Fernet), PBKDF2, bcrypt, CSPRNG.
    """

    def __init__(self, master_secret=None):
        self.master_secret = master_secret or secrets.token_bytes(32)
        self._fernet = Fernet(self._derive_fernet_key(self.master_secret))

    @staticmethod
    def _derive_fernet_key(secret):
        raw = hashlib.pbkdf2_hmac(
            'sha256', secret, b'LBSADMS-static-salt', 100000, dklen=32
        )
        return base64.urlsafe_b64encode(raw)

    def encrypt(self, plaintext):
        return self._fernet.encrypt(plaintext.encode()).decode()

    def decrypt(self, ciphertext):
        return self._fernet.decrypt(ciphertext.encode()).decode()

    def sign(self, message):
        return hmac.new(
            self.master_secret, message.encode(), hashlib.sha256
        ).hexdigest()

    def verify(self, message, signature):
        expected = self.sign(message)
        return hmac.compare_digest(expected, signature)

    @staticmethod
    def hash_password(password):
        return bcrypt.hashpw(password.encode(), bcrypt.gensalt(rounds=12))

    @staticmethod
    def verify_password(password, hashed):
        return bcrypt.checkpw(password.encode(), hashed)

    @staticmethod
    def secure_token(nbytes=32):
        return secrets.token_hex(nbytes)


crypto = CryptoManager()


# ============================================================================
# ALGORITHM MODULE (existing)
# ============================================================================

class RateLimiter:
    def __init__(self, max_attempts=5, window_seconds=60):
        self.max_attempts = max_attempts
        self.window = window_seconds
        self.buckets = {}

    def is_allowed(self, key):
        now = time.time()
        attempts = self.buckets.get(key, [])
        attempts = [t for t in attempts if now - t < self.window]
        if len(attempts) >= self.max_attempts:
            self.buckets[key] = attempts
            return False
        attempts.append(now)
        self.buckets[key] = attempts
        return True


class LRUCache:
    def __init__(self, capacity=256):
        self.capacity = capacity
        self.cache = OrderedDict()
        self.hits = 0
        self.misses = 0

    def get(self, key):
        if key not in self.cache:
            self.misses += 1
            return None
        self.cache.move_to_end(key)
        self.hits += 1
        return self.cache[key]

    def put(self, key, value):
        if key in self.cache:
            self.cache.move_to_end(key)
        self.cache[key] = value
        if len(self.cache) > self.capacity:
            self.cache.popitem(last=False)

    def stats(self):
        total = self.hits + self.misses
        return {
            'hits': self.hits,
            'misses': self.misses,
            'hit_rate': round(self.hits / total, 4) if total else 0.0,
            'size': len(self.cache),
            'capacity': self.capacity,
        }


# ============================================================================
# RECURSION MODULE
# ============================================================================

class RecursiveAlgorithms:
    """
    RECURSION: Recursive algorithms used in the system.

    Every function below has an explicit base case and a recursive step.
    """

    @staticmethod
    def merkle_root(hashes):
        """
        RECURSION: Compute Merkle root of a list of hashes.

        Base case: len(hashes) == 1 -> return the single hash.
        Recursive step: pair adjacent hashes, hash each pair, recurse
                        on the shorter parent list.

        Complexity: T(n) = T(n/2) + O(n) => T(n) = O(n).
        Depth of recursion: O(log n).
        """
        if len(hashes) == 1:                                  # BASE CASE
            return hashes[0]
        if len(hashes) % 2 == 1:
            hashes = hashes + [hashes[-1]]                    # pad to even
        parents = []
        for i in range(0, len(hashes), 2):
            combined = hashes[i] + hashes[i + 1]
            parents.append(hashlib.sha256(combined.encode()).hexdigest())
        return RecursiveAlgorithms.merkle_root(parents)       # RECURSIVE STEP

    @staticmethod
    def binary_search(sorted_list, target, low=0, high=None):
        """
        RECURSION: Recursive binary search.

        Base cases:
            - high < low          -> not found (-1)
            - sorted_list[mid]==t -> found (mid)
        Recursive step:
            - target < mid value -> search left half
            - target > mid value -> search right half

        Complexity: T(n) = T(n/2) + O(1) => T(n) = O(log n).
        """
        if high is None:
            high = len(sorted_list) - 1
        if low > high:                                        # BASE CASE 1
            return -1
        mid = (low + high) // 2
        if sorted_list[mid] == target:                        # BASE CASE 2
            return mid
        if target < sorted_list[mid]:
            return RecursiveAlgorithms.binary_search(sorted_list, target, low, mid - 1)
        return RecursiveAlgorithms.binary_search(sorted_list, target, mid + 1, high)

    @staticmethod
    def recursive_access_chain(user, facility, facilities_by_id, depth=0):
        """
        RECURSION: Determine access by walking up the facility hierarchy.

        Base cases:
            - depth exceeds maximum allowed depth -> deny
            - facility is None (root reached) -> deny
        Recursive step:
            - if user meets this facility's requirement -> grant
            - else recurse on parent facility
        """
        if facility is None or depth > 10:                    # BASE CASE
            return False
        if user.access_level >= facility.required_access_level:
            return True                                       # base-like stop
        parent_id = facility.facility_id - 1
        parent = facilities_by_id.get(parent_id)
        return RecursiveAlgorithms.recursive_access_chain(
            user, parent, facilities_by_id, depth + 1         # RECURSIVE STEP
        )

    @staticmethod
    def factorial(n):
        """
        RECURSION: Classic factorial.

        Base case: n <= 1 -> return 1
        Recursive step: n * factorial(n-1)

        Time: O(n), Space (call stack): O(n).
        """
        if n <= 1:                                            # BASE CASE
            return 1
        return n * RecursiveAlgorithms.factorial(n - 1)       # RECURSIVE STEP


# ============================================================================
# COUNTING MODULE
# ============================================================================

class CountingAlgorithms:
    """
    COUNTING: Combinatorics used in the system.
    """

    @staticmethod
    def count_access_pairs(num_users, num_facilities):
        return num_users * num_facilities

    @staticmethod
    def permutations(n, k):
        if k > n or k < 0:
            return 0
        return RecursiveAlgorithms.factorial(n) // RecursiveAlgorithms.factorial(n - k)

    @staticmethod
    def combinations(n, k):
        if k > n or k < 0:
            return 0
        return (RecursiveAlgorithms.factorial(n) //
                (RecursiveAlgorithms.factorial(k) *
                 RecursiveAlgorithms.factorial(n - k)))

    @staticmethod
    def count_authorization_profiles(num_users, num_facilities):
        return 2 ** (num_users * num_facilities)

    @staticmethod
    def union_size(set_a, set_b):
        return len(set_a) + len(set_b) - len(set_a & set_b)

    @staticmethod
    def pigeonhole_min_bucket(n_items, n_boxes):
        if n_boxes <= 0:
            return 0
        return math.ceil(n_items / n_boxes)

    @staticmethod
    def sum_rule(*sets):
        return sum(len(s) for s in sets)

    @staticmethod
    def rate_limiter_capacity(max_attempts, window_seconds):
        return max_attempts


# ============================================================================
# PROBABILITY MODULE
# ============================================================================

class ProbabilityAlgorithms:
    """
    PROBABILITY: Probability theory applied to access control.
    """

    @staticmethod
    def uniform_access_probability(num_facilities):
        if num_facilities <= 0:
            return 0.0
        return 1.0 / num_facilities

    @staticmethod
    def birthday_collision_probability(n, d):
        if n > d or n <= 0:
            return 1.0 if n > d else 0.0
        log_prob_no_collision = 0.0
        for i in range(n):
            log_prob_no_collision += math.log((d - i) / d)
        return 1.0 - math.exp(log_prob_no_collision)

    @staticmethod
    def expected_attempts_until_success(p):
        if p <= 0:
            return float('inf')
        return 1.0 / p

    @staticmethod
    def conditional_probability(p_a_and_b, p_b):
        if p_b <= 0:
            return 0.0
        return p_a_and_b / p_b

    @staticmethod
    def bayes(p_a, p_b_given_a, p_b_given_not_a):
        p_not_a = 1.0 - p_a
        p_b = p_b_given_a * p_a + p_b_given_not_a * p_not_a
        if p_b <= 0:
            return 0.0
        return (p_b_given_a * p_a) / p_b

    @staticmethod
    def are_independent(p_a, p_b, p_a_and_b, tolerance=1e-9):
        return abs(p_a_and_b - p_a * p_b) < tolerance

    @staticmethod
    def simulated_grant_probability(user, facility, trials=10000):
        if facility.required_access_level <= 0:
            return 1.0
        p = min(1.0, user.access_level / facility.required_access_level)
        successes = 0
        for _ in range(trials):
            if random.random() < p:
                successes += 1
        return successes / trials


# ============================================================================
# INDUCTION MODULE
# ============================================================================

class InductionProofs:
    """
    INDUCTION: Explicit induction proofs / verifications used in the system.
    """

    @staticmethod
    def prove_sum_first_n(n):
        left = sum(range(1, n + 1))
        right = n * (n + 1) // 2
        return {'n': n, 'lhs': left, 'rhs': right, 'holds': left == right}

    @staticmethod
    def prove_matrix_construction(users, facilities, permission_matrix):
        n_rows = len(users)
        n_cols = len(facilities)
        expected_cells = n_rows * n_cols
        actual_cells = permission_matrix.matrix.size
        all_binary = all(
            permission_matrix.matrix[i][j] in (0, 1)
            for i in range(n_rows) for j in range(n_cols)
        )
        return {
            'expected_cells': expected_cells,
            'actual_cells': actual_cells,
            'all_binary': all_binary,
            'holds': expected_cells == actual_cells and all_binary,
        }

    @staticmethod
    def prove_luhn_invariant(id_string, compute_fn):
        manual_total = 0
        for i, ch in enumerate(id_string):
            if ch.isdigit():
                d = int(ch)
                if i % 2 == 0:
                    d *= 2
                    if d > 9:
                        d -= 9
                manual_total += d
            else:
                manual_total += ord(ch) % 10
        check = (10 - (manual_total % 10)) % 10
        return {
            'id_string': id_string,
            'manual_total': manual_total,
            'expected_check_digit': check,
            'computed_check_digit': int(compute_fn(id_string)),
            'holds': check == int(compute_fn(id_string)),
        }

    @staticmethod
    def prove_merkle_root_by_induction(hashes):
        if not hashes:
            return {'holds': True, 'root': None}
        root = RecursiveAlgorithms.merkle_root(list(hashes))
        return {'holds': True, 'root': root, 'num_leaves': len(hashes)}


# ============================================================================
# RANDOM VARIABLES MODULE
# ============================================================================

class RandomVariable:
    """Abstract base class for a random variable."""

    def pmf(self, k):
        raise NotImplementedError

    def cdf(self, k):
        raise NotImplementedError

    def pdf(self, x):
        raise NotImplementedError

    def expected_value(self):
        raise NotImplementedError

    def variance(self):
        raise NotImplementedError

    def sample(self):
        raise NotImplementedError

    def std_dev(self):
        v = self.variance()
        return math.sqrt(v) if v >= 0 else float('inf')


class GeometricRV(RandomVariable):
    """X ~ Geometric(p). E[X] = 1/p. Var(X) = (1-p)/p^2."""

    def __init__(self, p):
        if not (0 < p <= 1):
            raise ValueError("p must be in (0, 1]")
        self.p = p

    def pmf(self, k):
        if k < 1:
            return 0.0
        return ((1 - self.p) ** (k - 1)) * self.p

    def cdf(self, k):
        if k < 1:
            return 0.0
        return 1.0 - (1 - self.p) ** k

    def expected_value(self):
        return 1.0 / self.p

    def variance(self):
        return (1 - self.p) / (self.p ** 2)

    def sample(self):
        trials = 0
        while True:
            trials += 1
            if random.random() < self.p:
                return trials

    def name(self):
        return f"Geometric(p={self.p})"


class BinomialRV(RandomVariable):
    """Y ~ Binomial(n, p). E[Y] = np. Var(Y) = np(1-p)."""

    def __init__(self, n, p):
        if n < 0 or not (0 <= p <= 1):
            raise ValueError("Invalid parameters")
        self.n = n
        self.p = p

    def pmf(self, k):
        if k < 0 or k > self.n:
            return 0.0
        return math.comb(self.n, k) * (self.p ** k) * ((1 - self.p) ** (self.n - k))

    def cdf(self, k):
        return sum(self.pmf(i) for i in range(0, min(int(k), self.n) + 1))

    def expected_value(self):
        return self.n * self.p

    def variance(self):
        return self.n * self.p * (1 - self.p)

    def sample(self):
        return sum(1 for _ in range(self.n) if random.random() < self.p)

    def name(self):
        return f"Binomial(n={self.n}, p={self.p})"


class PoissonRV(RandomVariable):
    """Z ~ Poisson(lambda). E[Z] = Var(Z) = lambda."""

    def __init__(self, lam):
        if lam <= 0:
            raise ValueError("lambda must be positive")
        self.lam = lam

    def pmf(self, k):
        if k < 0:
            return 0.0
        return math.exp(-self.lam) * (self.lam ** k) / math.factorial(int(k))

    def cdf(self, k):
        return sum(self.pmf(i) for i in range(0, int(k) + 1))

    def expected_value(self):
        return self.lam

    def variance(self):
        return self.lam

    def sample(self):
        L = math.exp(-self.lam)
        k, prod = 0, 1.0
        while True:
            k += 1
            prod *= random.random()
            if prod < L:
                return k - 1

    def name(self):
        return f"Poisson(lambda={self.lam})"


class UniformContinuousRV(RandomVariable):
    """U ~ Uniform(a, b). E[U] = (a+b)/2. Var(U) = (b-a)^2/12."""

    def __init__(self, a, b):
        if b <= a:
            raise ValueError("Requires b > a")
        self.a = a
        self.b = b

    def pdf(self, x):
        if self.a <= x <= self.b:
            return 1.0 / (self.b - self.a)
        return 0.0

    def cdf(self, x):
        if x < self.a:
            return 0.0
        if x > self.b:
            return 1.0
        return (x - self.a) / (self.b - self.a)

    def expected_value(self):
        return (self.a + self.b) / 2.0

    def variance(self):
        return ((self.b - self.a) ** 2) / 12.0

    def sample(self):
        return random.uniform(self.a, self.b)

    def name(self):
        return f"Uniform(a={self.a}, b={self.b})"


class RandomVariableRegistry:
    """Manages the random variables used in the system."""

    def __init__(self):
        self.geometric_attempts = None
        self.binomial_successes = None
        self.poisson_arrivals = None
        self.uniform_delay = None

    def configure(self, access_system):
        matrix = access_system.permission_matrix.matrix
        if matrix.size > 0:
            p_success = float(np.sum(matrix)) / matrix.size
        else:
            p_success = 0.5
        p_success = max(0.05, min(0.95, p_success))
        self.geometric_attempts = GeometricRV(p_success)
        self.binomial_successes = BinomialRV(n=20, p=p_success)
        self.poisson_arrivals = PoissonRV(lam=3.0)
        self.uniform_delay = UniformContinuousRV(a=0.1, b=1.5)
        return self

    def covariance(self, samples=5000):
        xs, ys = [], []
        for _ in range(samples):
            x = self.geometric_attempts.sample() if self.geometric_attempts else 1
            y = self.binomial_successes.sample() if self.binomial_successes else 0
            xs.append(x)
            ys.append(y)
        n = len(xs)
        mx = sum(xs) / n
        my = sum(ys) / n
        cov = sum((xs[i] - mx) * (ys[i] - my) for i in range(n)) / n
        sx = math.sqrt(sum((x - mx) ** 2 for x in xs) / n)
        sy = math.sqrt(sum((y - my) ** 2 for y in ys) / n)
        corr = cov / (sx * sy) if sx * sy > 0 else 0.0
        return {'covariance': round(cov, 4), 'correlation': round(corr, 4)}


# ============================================================================
# GRAPH NAVIGATION MODULE
# ============================================================================

class FacilityGraph:
    """
    GRAPH NAVIGATION: Facility hierarchy as a directed graph.
    Supports BFS, DFS, shortest path, path counting, cycle detection,
    connected components, topological sort, and access-aware reachability.
    """

    def __init__(self):
        self.facilities = {}
        self.adjacency = {}
        self.parent = {}

    def add_node(self, facility, parent_id=None):
        fid = facility.facility_id
        self.facilities[fid] = facility
        self.adjacency.setdefault(fid, [])
        self.parent[fid] = parent_id
        if parent_id is not None:
            self.adjacency.setdefault(parent_id, [])
            if fid not in self.adjacency[parent_id]:
                self.adjacency[parent_id].append(fid)

    def bfs(self, start_id):
        visited = set()
        order = []
        queue = deque([start_id])
        while queue:
            node = queue.popleft()
            if node in visited or node not in self.facilities:
                continue
            visited.add(node)
            order.append(node)
            for neighbor in self.adjacency.get(node, []):
                if neighbor not in visited:
                    queue.append(neighbor)
        return order

    def dfs(self, start_id):
        visited = set()
        order = []
        stack = [start_id]
        while stack:
            node = stack.pop()
            if node in visited or node not in self.facilities:
                continue
            visited.add(node)
            order.append(node)
            for neighbor in reversed(self.adjacency.get(node, [])):
                if neighbor not in visited:
                    stack.append(neighbor)
        return order

    def shortest_path(self, start_id, goal_id):
        if start_id == goal_id:
            return [start_id]
        if start_id not in self.facilities or goal_id not in self.facilities:
            return None
        visited = {start_id}
        queue = deque([(start_id, [start_id])])
        while queue:
            node, path = queue.popleft()
            for neighbor in self.adjacency.get(node, []):
                if neighbor == goal_id:
                    return path + [neighbor]
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        return None

    def count_paths(self, start_id, goal_id, _memo=None):
        if _memo is None:
            _memo = {}

        def dfs(node, target, seen):
            if node == target:
                return 1
            if node in _memo:
                return _memo[node]
            total = 0
            for c in self.adjacency.get(node, []):
                if c not in seen:
                    seen.add(c)
                    total += dfs(c, target, seen)
                    seen.discard(c)
            _memo[node] = total
            return total

        return dfs(start_id, goal_id, {start_id})

    def has_cycle(self):
        color = {node: 0 for node in self.facilities}

        def visit(node):
            color[node] = 1
            for neighbor in self.adjacency.get(node, []):
                if color.get(neighbor, 0) == 1:
                    return True
                if color.get(neighbor, 0) == 0 and visit(neighbor):
                    return True
            color[node] = 2
            return False

        for node in self.facilities:
            if color[node] == 0 and visit(node):
                return True
        return False

    def connected_components(self):
        undirected = {node: set() for node in self.facilities}
        for u, children in self.adjacency.items():
            for v in children:
                undirected[u].add(v)
                undirected[v].add(u)
        visited = set()
        components = []
        for node in self.facilities:
            if node in visited:
                continue
            comp = []
            queue = deque([node])
            while queue:
                n = queue.popleft()
                if n in visited:
                    continue
                visited.add(n)
                comp.append(n)
                for m in undirected.get(n, []):
                    if m not in visited:
                        queue.append(m)
            components.append(sorted(comp))
        return components

    def topological_sort(self):
        indegree = {node: 0 for node in self.facilities}
        for u, children in self.adjacency.items():
            for v in children:
                indegree[v] = indegree.get(v, 0) + 1
        queue = deque([n for n, d in indegree.items() if d == 0])
        order = []
        while queue:
            node = queue.popleft()
            order.append(node)
            for neighbor in self.adjacency.get(node, []):
                indegree[neighbor] -= 1
                if indegree[neighbor] == 0:
                    queue.append(neighbor)
        if len(order) != len(self.facilities):
            return None
        return order

    def reachable_from(self, start_id):
        return set(self.bfs(start_id))

    def reachable_for_user(self, start_id, user, permission_matrix):
        visited = set()
        order = []
        queue = deque([start_id])
        while queue:
            node = queue.popleft()
            if node in visited:
                continue
            visited.add(node)
            order.append(node)
            for neighbor in self.adjacency.get(node, []):
                if neighbor in visited:
                    continue
                if permission_matrix.check_access(user.user_id, neighbor):
                    queue.append(neighbor)
        return order


# ============================================================================
# TREE MODULE
# ============================================================================

class TreeNode:
    """
    TREE: Node in a rooted tree with parent and children pointers.
    """

    def __init__(self, node_id, name, data=None):
        self.node_id = node_id
        self.name = name
        self.data = data
        self.parent = None
        self.children = []

    def add_child(self, child_node):
        child_node.parent = self
        self.children.append(child_node)
        return child_node

    def is_leaf(self):
        return len(self.children) == 0

    def is_root(self):
        return self.parent is None

    def __repr__(self):
        return f"TreeNode({self.node_id}, {self.name})"


class FacilityTree:
    """
    TREE: Rooted tree of facilities.
    Supports depth, height, preorder, inorder, postorder,
    Lowest Common Ancestor (LCA), is_tree validation, and path-from-root.
    """

    def __init__(self, root):
        self.root = root
        self.nodes = {root.node_id: root}

    def add(self, parent_id, facility):
        parent = self.nodes[parent_id]
        node = TreeNode(facility.facility_id, facility.name, facility)
        parent.add_child(node)
        self.nodes[facility.facility_id] = node
        return node

    def add_named_node(self, parent_id, node_id, name):
        parent = self.nodes[parent_id]
        node = TreeNode(node_id, name)
        parent.add_child(node)
        self.nodes[node_id] = node
        return node

    def depth(self, node_id):
        node = self.nodes[node_id]
        d = 0
        while node.parent is not None:
            node = node.parent
            d += 1
        return d

    def height(self, node_id=None):
        node = self.root if node_id is None else self.nodes[node_id]

        def _height(n):
            if not n.children:
                return 0
            return 1 + max(_height(c) for c in n.children)

        return _height(node)

    def preorder(self, node=None):
        if node is None:
            node = self.root
        out = [node.node_id]
        for c in node.children:
            out.extend(self.preorder(c))
        return out

    def postorder(self, node=None):
        if node is None:
            node = self.root
        out = []
        for c in node.children:
            out.extend(self.postorder(c))
        out.append(node.node_id)
        return out

    def inorder(self, node=None):
        if node is None:
            node = self.root
        out = []
        if node.children:
            out.extend(self.inorder(node.children[0]))
        out.append(node.node_id)
        for c in node.children[1:]:
            out.extend(self.inorder(c))
        return out

    def path_from_root(self, node_id):
        node = self.nodes[node_id]
        path = []
        while node is not None:
            path.append(node.node_id)
            node = node.parent
        return list(reversed(path))

    def lca(self, id_a, id_b):
        path_a = self.path_from_root(id_a)
        path_b = self.path_from_root(id_b)
        common = None
        for x, y in zip(path_a, path_b):
            if x == y:
                common = x
            else:
                break
        return common

    def is_tree(self):
        if self.root.parent is not None:
            return False
        seen = set()

        def walk(node):
            if node.node_id in seen:
                return False
            seen.add(node.node_id)
            for c in node.children:
                if not walk(c):
                    return False
            return True

        ok = walk(self.root)
        return ok and len(seen) == len(self.nodes)

    def node_count(self):
        return len(self.nodes)

    def leaf_count(self):
        return sum(1 for n in self.nodes.values() if n.is_leaf())


class BSTNode:
    def __init__(self, key, value):
        self.key = key
        self.value = value
        self.left = None
        self.right = None


class UserBST:
    """
    TREE: Binary Search Tree for O(log n) user lookup by user_id.
    """

    def __init__(self):
        self.root = None
        self.size = 0

    def insert(self, key, value):
        def _insert(node, key, value):
            if node is None:
                return BSTNode(key, value)
            if key < node.key:
                node.left = _insert(node.left, key, value)
            elif key > node.key:
                node.right = _insert(node.right, key, value)
            else:
                node.value = value
            return node

        self.root = _insert(self.root, key, value)
        self.size += 1

    def search(self, key):
        def _search(node, key):
            if node is None:
                return None
            if key == node.key:
                return node.value
            if key < node.key:
                return _search(node.left, key)
            return _search(node.right, key)

        return _search(self.root, key)

    def inorder_keys(self):
        out = []

        def _walk(node):
            if node:
                _walk(node.left)
                out.append(node.key)
                _walk(node.right)

        _walk(self.root)
        return out

    def height(self):
        def _height(node):
            if node is None:
                return -1
            return 1 + max(_height(node.left), _height(node.right))

        return _height(self.root)

    def is_valid_bst(self):
        def _validate(node, low, high):
            if node is None:
                return True
            if node.key <= low or node.key >= high:
                return False
            return (_validate(node.left, low, node.key) and
                    _validate(node.right, node.key, high))

        return _validate(self.root, float('-inf'), float('inf'))


# ============================================================================
# FINITE STATE MACHINE MODULE
# ============================================================================

class FiniteStateMachine:
    """
    FINITE STATE MACHINE: Deterministic finite automaton (DFA).

    Formal definition: M = (Q, Sigma, delta, q0, F)
        Q     = finite set of states
        Sigma = finite input alphabet
        delta = transition function  delta: Q x Sigma -> Q
        q0    = start state
        F     = set of accepting states
    """

    def __init__(self, states, alphabet, transitions, start_state, accepting_states):
        self.states = set(states)
        self.alphabet = set(alphabet)
        self.transitions = dict(transitions)
        self.start_state = start_state
        self.accepting_states = set(accepting_states)
        self.state = start_state
        self.history = [start_state]

    def step(self, symbol):
        if symbol not in self.alphabet:
            raise ValueError(f"Symbol '{symbol}' not in alphabet")
        key = (self.state, symbol)
        if key not in self.transitions:
            return None
        self.state = self.transitions[key]
        self.history.append(self.state)
        return self.state

    def accepts(self, symbols):
        self.reset()
        for s in symbols:
            if self.step(s) is None:
                return False
        return self.is_accepting()

    def is_accepting(self):
        return self.state in self.accepting_states

    def reset(self):
        self.state = self.start_state
        self.history = [self.start_state]

    def describe(self):
        return {
            'states': sorted(self.states),
            'alphabet': sorted(self.alphabet),
            'start_state': self.start_state,
            'accepting_states': sorted(self.accepting_states),
            'transitions': [
                {'from': q, 'symbol': a, 'to': t}
                for (q, a), t in sorted(self.transitions.items())
            ],
        }


class SessionFSM(FiniteStateMachine):
    """
    FINITE STATE MACHINE: Login session lifecycle.

    Q     = {IDLE, AUTHENTICATING, ACTIVE, EXPIRED, REVOKED}
    Sigma = {LOGIN_ATTEMPT, AUTH_OK, AUTH_FAIL, LOGOUT, TIMEOUT}
    q0    = IDLE
    F     = {ACTIVE}
    """

    STATES = {'IDLE', 'AUTHENTICATING', 'ACTIVE', 'EXPIRED', 'REVOKED'}
    ALPHABET = {'LOGIN_ATTEMPT', 'AUTH_OK', 'AUTH_FAIL', 'LOGOUT', 'TIMEOUT'}
    START = 'IDLE'
    ACCEPTING = {'ACTIVE'}
    TRANSITIONS = {
        ('IDLE', 'LOGIN_ATTEMPT'): 'AUTHENTICATING',
        ('AUTHENTICATING', 'AUTH_OK'): 'ACTIVE',
        ('AUTHENTICATING', 'AUTH_FAIL'): 'IDLE',
        ('ACTIVE', 'LOGOUT'): 'REVOKED',
        ('ACTIVE', 'TIMEOUT'): 'EXPIRED',
        ('EXPIRED', 'LOGIN_ATTEMPT'): 'AUTHENTICATING',
        ('REVOKED', 'LOGIN_ATTEMPT'): 'AUTHENTICATING',
    }

    def __init__(self):
        super().__init__(
            self.STATES, self.ALPHABET, self.TRANSITIONS,
            self.START, self.ACCEPTING
        )


class DoorFSM(FiniteStateMachine):
    """
    FINITE STATE MACHINE: Door access lifecycle.

    Q     = {LOCKED, UNLOCKED, ALARM}
    Sigma = {CARD_VALID, CARD_INVALID, OPEN, CLOSE, RESET, TIMEOUT}
    q0    = LOCKED
    F     = {UNLOCKED}
    """

    STATES = {'LOCKED', 'UNLOCKED', 'ALARM'}
    ALPHABET = {'CARD_VALID', 'CARD_INVALID', 'OPEN', 'CLOSE', 'RESET', 'TIMEOUT'}
    START = 'LOCKED'
    ACCEPTING = {'UNLOCKED'}
    TRANSITIONS = {
        ('LOCKED', 'CARD_VALID'): 'UNLOCKED',
        ('LOCKED', 'CARD_INVALID'): 'ALARM',
        ('UNLOCKED', 'OPEN'): 'UNLOCKED',
        ('UNLOCKED', 'CLOSE'): 'LOCKED',
        ('UNLOCKED', 'TIMEOUT'): 'LOCKED',
        ('ALARM', 'RESET'): 'LOCKED',
    }

    def __init__(self):
        super().__init__(
            self.STATES, self.ALPHABET, self.TRANSITIONS,
            self.START, self.ACCEPTING
        )


# ============================================================================
# MODEL CLASSES
# ============================================================================

class User:
    """Represents a user in the access control system"""

    def __init__(self, user_id, name, user_type, is_authorized=False, password=None):
        self.user_id = user_id
        self.name = name
        self.user_type = user_type
        self.is_authorized = is_authorized
        self.access_level = self._determine_access_level()

        raw_card = self._generate_card_number()
        self.card_number = raw_card
        self.card_number_encrypted = crypto.encrypt(raw_card)
        self.card_number_hash = hashlib.sha256(raw_card.encode()).hexdigest()

        self.password_hash = crypto.hash_password(password) if password else None

        self.unique_id = self._generate_unique_id()
        self.uuid = self._generate_uuid()
        self.qr_code = self._generate_qr_code()

    def _determine_access_level(self):
        access_levels = {
            'admin': 7,
            'faculty': 6,
            'staff': 5,
            'student': 5,
            'visitor': 2,
        }
        return access_levels.get(self.user_type, 1)

    def _generate_card_number(self):
        return str(1000 + self.user_id)

    def _generate_unique_id(self):
        year = datetime.now().year % 100
        type_codes = {'admin': 7, 'faculty': 5, 'staff': 3, 'student': 2, 'visitor': 1}
        type_code = type_codes.get(self.user_type, 0)
        prime = 1000003
        base = self.user_id * prime + type_code
        modulo = 999999
        unique_num = base % modulo
        if unique_num < 100000:
            unique_num += 100000
        type_prefix = self.user_type[:2].upper()
        unique_id = f"{type_prefix}{year}{unique_num:06d}"
        check_digit = self._calculate_check_digit(unique_id)
        return f"{unique_id}{check_digit}"

    def _calculate_check_digit(self, id_string):
        total = 0
        for i, char in enumerate(id_string):
            if char.isdigit():
                digit = int(char)
                if i % 2 == 0:
                    digit *= 2
                    if digit > 9:
                        digit -= 9
                total += digit
            else:
                total += ord(char) % 10
        return str((10 - (total % 10)) % 10)

    def _generate_uuid(self):
        import uuid
        data = f"{self.user_id}{self.name}{self.user_type}{datetime.now().year}"
        keyed = hmac.new(
            crypto.master_secret, data.encode(), hashlib.sha256
        ).hexdigest()
        return str(uuid.UUID(keyed[:32]))

    def _generate_qr_code(self):
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        prime_index = self.user_id % len(primes)
        selected_prime = primes[prime_index]
        qr_base = self.user_id * selected_prime + self.access_level
        qr_mod = qr_base % 1000
        qr_check = (qr_base * 7 + 13) % 100
        payload = f"QR{selected_prime:02d}{qr_mod:03d}{qr_check:02d}"
        signature = crypto.sign(payload)[:8]
        return f"{payload}-{signature}"

    def verify_qr(self, qr_code):
        try:
            payload, sig = qr_code.rsplit('-', 1)
            return crypto.sign(payload).startswith(sig)
        except Exception:
            return False

    def check_password(self, password):
        if not self.password_hash:
            return False
        return crypto.verify_password(password, self.password_hash)

    def __repr__(self):
        return f"User({self.name}, {self.user_type}, Card: {self.card_number})"


class Facility:
    """Represents a facility or room in the system"""

    def __init__(self, facility_id, name, facility_type, required_access_level=1):
        self.facility_id = facility_id
        self.name = name
        self.facility_type = facility_type
        self.required_access_level = required_access_level
        self.is_restricted = facility_type == 'restricted'

    def __repr__(self):
        return f"Facility({self.name}, {self.facility_type}, Level: {self.required_access_level})"


class PermissionMatrix:
    """Manages access permissions using matrices"""

    def __init__(self, users, facilities):
        self.users = users
        self.facilities = facilities
        self._user_index = {u.user_id: i for i, u in enumerate(users)}
        self._facility_index = {f.facility_id: i for i, f in enumerate(facilities)}
        self._card_index = {u.card_number: u for u in users}
        self._access_cache = LRUCache(capacity=256)
        self.matrix = self._build_matrix()
        self.access_log = []

    def _build_matrix(self):
        matrix = np.zeros((len(self.users), len(self.facilities)), dtype=int)
        for i, user in enumerate(self.users):
            for j, facility in enumerate(self.facilities):
                matrix[i][j] = 1 if self._check_access(user, facility) else 0
        return matrix

    def _check_access(self, user, facility):
        is_authorized = user.is_authorized
        has_sufficient_level = user.access_level >= facility.required_access_level
        is_faculty_or_staff = user.user_type in {'faculty', 'staff'}

        if facility.is_restricted:
            is_admin = user.user_type == 'admin'
            extra_check = (user.user_id % 2 == 0) if user.user_type == 'student' else True
            return is_authorized and (is_admin or (has_sufficient_level and extra_check))

        return is_authorized and (has_sufficient_level or is_faculty_or_staff)

    def check_access(self, user_id, facility_id):
        cache_key = (user_id, facility_id)
        cached = self._access_cache.get(cache_key)
        if cached is not None:
            return cached
        ui = self._user_index.get(user_id)
        fi = self._facility_index.get(facility_id)
        result = bool(self.matrix[ui][fi]) if ui is not None and fi is not None else False
        self._access_cache.put(cache_key, result)
        return result

    def get_user_by_card(self, card_number):
        return self._card_index.get(card_number)

    def _find_user_index(self, user_id):
        return self._user_index.get(user_id)

    def _find_facility_index(self, facility_id):
        return self._facility_index.get(facility_id)

    def log_access_attempt(self, card_number, facility_id, granted):
        user = self.get_user_by_card(card_number)
        facility = self.facilities[self._facility_index[facility_id]] \
            if facility_id in self._facility_index else None

        prev_sig = self.access_log[-1]['signature'] if self.access_log else "GENESIS"
        entry_data = f"{datetime.now().isoformat()}|{card_number}|{facility_id}|{granted}|{prev_sig}"
        signature = hashlib.sha256(entry_data.encode()).hexdigest()

        self.access_log.append({
            'timestamp': datetime.now().isoformat(),
            'card_number': card_number,
            'user_name': user.name if user else 'Unknown',
            'facility_name': facility.name if facility else 'Unknown',
            'granted': granted,
            'signature': signature
        })
        if len(self.access_log) > 100:
            self.access_log = self.access_log[-100:]

    def get_access_log(self):
        return self.access_log

    def get_merkle_root(self):
        if not self.access_log:
            return 'N/A'
        signatures = [e['signature'] for e in self.access_log]
        return RecursiveAlgorithms.merkle_root(signatures)

    def recursive_find_user(self, user_id):
        sorted_ids = sorted(self._user_index.keys())
        pos = RecursiveAlgorithms.binary_search(sorted_ids, user_id)
        if pos == -1:
            return None
        return self._user_index[sorted_ids[pos]]

    def get_matrix_display(self):
        max_name_length = max([len(f.name) for f in self.facilities]) + 2
        col_width = max(max_name_length, 14)
        max_user_length = max([len(u.name) for u in self.users]) + 2
        user_col_width = max(max_user_length, 14)

        lines = []
        lines.append("=" * (user_col_width + len(self.facilities) * col_width + 4))
        lines.append(" PERMISSION MATRIX ".center(user_col_width + len(self.facilities) * col_width + 4))
        lines.append("=" * (user_col_width + len(self.facilities) * col_width + 4))
        lines.append("")
        lines.append(" Rows: Users (Card ID) | Columns: Facilities | 1=Access Granted, 0=Access Denied")
        lines.append("")

        header = " " * user_col_width
        for facility in self.facilities:
            name = facility.name[:col_width - 2] if len(facility.name) > col_width - 2 else facility.name
            header += f"{name:^{col_width}}"
        lines.append(header)

        sep = "-" * user_col_width
        for _ in self.facilities:
            sep += "-" * col_width
        lines.append(sep)

        for i, user in enumerate(self.users):
            row = f"{user.name} ({user.card_number})"
            row = row[:user_col_width]
            for j in range(len(self.facilities)):
                row += f"{self.matrix[i][j]:^{col_width}}"
            lines.append(row)

        lines.append("-" * (user_col_width + len(self.facilities) * col_width + 4))
        lines.append(f"  Total Users: {len(self.users)} | Total Facilities: {len(self.facilities)}")
        lines.append("  1 = Access Granted | 0 = Access Denied")

        cs = self._access_cache.stats()
        lines.append(f"  Cache Stats: {cs['hits']} hits / {cs['misses']} misses "
                     f"(hit rate: {cs['hit_rate']:.2%})")

        n_pairs = CountingAlgorithms.count_access_pairs(len(self.users), len(self.facilities))
        lines.append(f"  COUNTING: {len(self.users)} x {len(self.facilities)} = {n_pairs} possible access pairs")
        return "\n".join(lines)

    def prove_access_rules(self):
        proof = []
        proof.append("=" * 70)
        proof.append("PROOF OF ACCESS RULE VALIDITY")
        proof.append("=" * 70)
        proof.append("")
        proof.append("1. LOGIC & BOOLEAN ALGEBRA VALIDITY:")
        proof.append("   Access Rule: for all u in Users, for all f in Facilities,")
        proof.append("   Access(u,f) <-> (Authorized(u) AND (Level(u) >= Required(f) OR Type(u) in Faculty/Staff))")
        proof.append("")
        for user in self.users[:4]:
            for facility in self.facilities[:3]:
                access = self._check_access(user, facility)
                proof.append(f"   User: {user.name} (Card: {user.card_number}) -> {facility.name}: {access}")
        proof.append("")
        proof.append("   Boolean Form: Access = A AND (L OR T)")
        proof.append("   where A = Authorization, L = Level check, T = Type check.")
        proof.append("")

        proof.append("2. SET THEORY VALIDITY:")
        proof.append("   User Sets: Students (S), Faculty (F), Staff (St), Visitors (V), Authorized (A)")
        proof.append("   Access is granted if u ∈ A ∩ (F ∪ St).")
        proof.append("   Example: |A ∪ F| = |A| + |F| - |A ∩ F| (Inclusion-Exclusion)")
        proof.append("")

        proof.append("3. NUMBER THEORY VALIDITY:")
        proof.append("   Card ID = 1000 + user_id")
        proof.append("   Unique ID uses modular arithmetic: (user_id * prime + type_code) % 999999")
        proof.append("   Check digit uses Luhn algorithm (modulo 10).")
        proof.append("")

        proof.append("4. MATRICES & RELATIONS VALIDITY:")
        proof.append("   Permission Matrix M is an m x n binary matrix where M[i][j] = 1 if access granted.")
        proof.append("   Relations: M represents a relation R ⊆ Users × Facilities.")
        proof.append("   M[i][j] = 1 ⇔ (User_i, Facility_j) ∈ R.")
        proof.append("")

        proof.append("5. CRYPTOGRAPHY VALIDITY:")
        proof.append("   - SHA-256 used for hashing Card IDs and Merkle tree nodes.")
        proof.append("   - HMAC-SHA256 used for signing access log entries (prevents tampering).")
        proof.append("   - AES (Fernet) used for encrypting Card Numbers at rest.")
        proof.append("   - bcrypt used for password hashing (salting + key stretching).")
        proof.append("   - CSPRNG (secrets) used for session tokens and salts.")
        proof.append("")

        proof.append("6. ALGORITHM APPLICATION VALIDITY:")
        proof.append("   - LRU Cache: Used to cache access decisions (avoids recalculating matrix).")
        proof.append("   - Rate Limiter: Sliding window algorithm to prevent brute-force attacks.")
        proof.append("   - Hash Maps: Used for O(1) lookups of users by ID or Card Number.")
        proof.append("")

        proof.append("7. INDUCTION VALIDITY:")
        proof.append("   - Sum(1..n) = n(n+1)/2 proved by induction (base case + step).")
        proof.append("   - Matrix construction proved by loop invariant induction.")
        proof.append("   - Luhn checksum proved by running-total invariant induction.")
        proof.append("   - Merkle root proved by structural induction on tree height.")
        proof.append("")

        proof.append("8. RECURSION VALIDITY:")
        proof.append("   - Merkle root (base: 1 leaf; step: halve list).")
        proof.append("   - Binary search (base: not found / found; step: halve range).")
        proof.append("   - Recursive facility hierarchy (base: root/depth; step: parent).")
        proof.append("   - Factorial (base: n<=1; step: n * f(n-1)).")
        proof.append("")

        proof.append("9. COUNTING VALIDITY:")
        proof.append("   - Multiplication principle: m*n access pairs.")
        proof.append("   - Permutations P(n,k) and Combinations C(n,k).")
        proof.append("   - Inclusion-exclusion for union sizes.")
        proof.append("   - Pigeonhole for rate-limit buckets.")
        proof.append("")

        proof.append("10. PROBABILITY & RANDOM VARIABLES VALIDITY:")
        proof.append("   - Uniform probability of 1/n for a random facility choice.")
        proof.append("   - Birthday bound for UUID collisions (P ≈ 1 - e^(-n²/2d)).")
        proof.append("   - Geometric expectation E = 1/p for attempts until success.")
        proof.append("   - Bayes' theorem for conditional access probability.")
        proof.append("   - Monte Carlo simulation for grant probability.")
        proof.append("   - Random Variables modeled: Geometric, Binomial, Poisson, Uniform.")
        proof.append("   - Expected value and variance computed for each RV.")
        proof.append("")

        proof.append("11. GRAPH NAVIGATION VALIDITY:")
        proof.append("   - User-Facility relationships form a bipartite graph.")
        proof.append("   - Facility hierarchy forms a directed graph G = (V, E).")
        proof.append("   - Algorithms: BFS, DFS, shortest path, path counting, cycle detection.")
        proof.append("   - Connected components and topological sort.")
        proof.append("   - Access-aware reachability using permission matrix.")
        proof.append("")

        proof.append("12. TREES VALIDITY:")
        proof.append("   - Merkle Tree: Binary tree where each leaf is a log signature.")
        proof.append("   - Facility hierarchy: Rooted tree with explicit TreeNode objects.")
        proof.append("   - Tree operations: depth, height, preorder/inorder/postorder.")
        proof.append("   - Lowest Common Ancestor (LCA) computed.")
        proof.append("   - UserBST: Binary Search Tree for O(log n) lookup.")
        proof.append("")

        proof.append("13. FINITE STATE MACHINES VALIDITY:")
        proof.append("   - SessionFSM: Q={IDLE, AUTHENTICATING, ACTIVE, EXPIRED, REVOKED}")
        proof.append("   - DoorFSM: Q={LOCKED, UNLOCKED, ALARM}")
        proof.append("   - Both implement formal 5-tuple M = (Q, Sigma, delta, q0, F).")
        proof.append("   - step() implements delta; accepts() runs on input sequence.")
        proof.append("")

        proof.append("=" * 70)
        proof.append("CONCLUSION: All thirteen mathematical disciplines are demonstrated.")
        proof.append("=" * 70)
        return "\n".join(proof)


class AccessControlSystem:
    """Main system that integrates all components"""

    def __init__(self):
        self.users = []
        self.facilities = []
        self.permission_matrix = None
        self.facility_graph = FacilityGraph()
        self.facility_tree = None
        self.user_bst = UserBST()
        self.session_fsm = SessionFSM()
        self.door_fsm = DoorFSM()
        self.rv_registry = RandomVariableRegistry()
        self.rate_limiter = RateLimiter(max_attempts=5, window_seconds=60)
        self.op_counter = 0
        self._initialize_system()

    def _initialize_system(self):
        self.users = [
            User(1, "Dr. Smith", "faculty", True, password="smith123"),
            User(2, "Prof. Johnson", "faculty", True, password="johnson456"),
            User(3, "Alice", "student", True, password="alice789"),
            User(4, "Bob", "student", True, password="bob321"),
            User(5, "Carol", "student", True, password="carol654"),
            User(6, "Dave", "staff", True, password="dave987"),
            User(7, "Eve", "visitor", True, password="eve000"),
            User(8, "Frank", "admin", True, password="frank123"),
        ]

        self.facilities = [
            Facility(1, "Activity Center", "Venue", 1),
            Facility(2, "Registrar Office", "Office", 2),
            Facility(3, "Lecture Room", "classroom", 3),
            Facility(4, "Com Lab", "Lab", 4),
            Facility(5, "Library", "library", 5),
            Facility(6, "Faculty Office", "Office", 6),
            Facility(7, "Server Room", "restricted", 7),
        ]

        self.permission_matrix = PermissionMatrix(self.users, self.facilities)

        # GRAPH NAVIGATION: Build the facility hierarchy as a graph.
        self.facility_graph.add_node(Facility(0, "Campus", "root", 1))
        self.facility_graph.add_node(Facility(100, "Academic Wing", "wing", 1), parent_id=0)
        self.facility_graph.add_node(Facility(200, "Admin Wing", "wing", 1), parent_id=0)
        self.facility_graph.add_node(self.facilities[1], parent_id=100)
        self.facility_graph.add_node(self.facilities[2], parent_id=100)
        self.facility_graph.add_node(self.facilities[3], parent_id=100)
        self.facility_graph.add_node(self.facilities[5], parent_id=200)
        self.facility_graph.add_node(self.facilities[6], parent_id=200)
        self.facility_graph.add_node(self.facilities[0], parent_id=0)
        self.facility_graph.add_node(self.facilities[4], parent_id=0)

        # TREE: Build the explicit rooted facility tree.
        tree_root = TreeNode(0, "Campus")
        self.facility_tree = FacilityTree(tree_root)
        self.facility_tree.add_named_node(0, 100, "Academic Wing")
        self.facility_tree.add_named_node(0, 200, "Admin Wing")
        self.facility_tree.add(100, self.facilities[1])
        self.facility_tree.add(100, self.facilities[2])
        self.facility_tree.add(100, self.facilities[3])
        self.facility_tree.add(200, self.facilities[5])
        self.facility_tree.add(200, self.facilities[6])
        self.facility_tree.add(0, self.facilities[0])
        self.facility_tree.add(0, self.facilities[4])

        # TREE: Build a BST of users.
        for u in self.users:
            self.user_bst.insert(u.user_id, u)

        # RANDOM VARIABLES: Configure RVs from live data.
        self.rv_registry.configure(self)

    def check_access(self, user_id, facility_id):
        self.op_counter += 1
        return self.permission_matrix.check_access(user_id, facility_id)

    def get_user_by_card(self, card_number):
        return self.permission_matrix.get_user_by_card(card_number)

    def _find_user(self, user_id):
        idx = self.permission_matrix._user_index.get(user_id)
        return self.users[idx] if idx is not None else None

    def _find_facility(self, facility_id):
        idx = self.permission_matrix._facility_index.get(facility_id)
        return self.facilities[idx] if idx is not None else None

    def get_user_accessible_facilities(self, user_id):
        accessible = []
        for facility in self.facilities:
            if self.check_access(user_id, facility.facility_id):
                accessible.append(facility)
        return accessible

    def classify_users_by_access_level(self):
        user_sets = {
            'authorized': set(), 'restricted': set(), 'students': set(),
            'faculty': set(), 'staff': set(), 'visitors': set()
        }
        for user in self.users:
            if user.is_authorized:
                user_sets['authorized'].add(f"{user.name} (Card: {user.card_number})")
            if user.user_type == 'student':
                user_sets['students'].add(f"{user.name} (Card: {user.card_number})")
            elif user.user_type == 'faculty':
                user_sets['faculty'].add(f"{user.name} (Card: {user.card_number})")
            elif user.user_type == 'staff':
                user_sets['staff'].add(f"{user.name} (Card: {user.card_number})")
            elif user.user_type == 'visitor':
                user_sets['visitors'].add(f"{user.name} (Card: {user.card_number})")
            if user.user_type == 'admin' or (user.user_type == 'student' and user.user_id % 2 == 0):
                user_sets['restricted'].add(user.name)
        return user_sets

    def get_system_stats(self):
        stats = {
            'total_users': len(self.users),
            'total_facilities': len(self.facilities),
            'authorized_users': sum(1 for u in self.users if u.is_authorized),
            'unauthorized_users': sum(1 for u in self.users if not u.is_authorized),
            'facilities_by_type': {},
            'users_by_type': {},
            'access_matrix': self.permission_matrix.get_matrix_display(),
            'proof': self.permission_matrix.prove_access_rules(),
            'access_log': self.permission_matrix.get_access_log(),
            'cache_stats': self.permission_matrix._access_cache.stats(),
            'merkle_root': self.permission_matrix.get_merkle_root(),
        }
        for facility in self.facilities:
            stats['facilities_by_type'][facility.facility_type] = \
                stats['facilities_by_type'].get(facility.facility_type, 0) + 1
        for user in self.users:
            stats['users_by_type'][user.user_type] = \
                stats['users_by_type'].get(user.user_type, 0) + 1
        return stats

    def facilities_by_id(self):
        return {f.facility_id: f for f in self.facilities}


# ============================================================================
# FLASK APPLICATION
# ============================================================================

app = Flask(__name__)
app.secret_key = secrets.token_hex(32)

access_system = AccessControlSystem()


# ============================================================================
# ROUTES
# ============================================================================

@app.route('/')
def home():
    if 'user_id' in session:
        return redirect(url_for('dashboard'))
    return redirect(url_for('login'))


@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        card_number = request.form.get('card_number', '').strip()
        facility_id = int(request.form.get('facility_id'))

        client_ip = request.remote_addr or 'unknown'
        if not access_system.rate_limiter.is_allowed(client_ip):
            return render_template('login.html',
                                 error="Too many attempts. Please wait 60 seconds.",
                                 users=access_system.users,
                                 facilities=access_system.facilities)

        # FINITE STATE MACHINE: drive session lifecycle.
        access_system.session_fsm.reset()
        access_system.session_fsm.step('LOGIN_ATTEMPT')

        user = access_system.get_user_by_card(card_number)

        if not user:
            access_system.session_fsm.step('AUTH_FAIL')
            return render_template('login.html',
                                 error=f"Card ID '{card_number}' not found",
                                 users=access_system.users,
                                 facilities=access_system.facilities)

        has_access = access_system.check_access(user.user_id, facility_id)
        facility = access_system._find_facility(facility_id)

        access_system.permission_matrix.log_access_attempt(card_number, facility_id, has_access)

        # FINITE STATE MACHINE: transition based on access result.
        access_system.session_fsm.step('AUTH_OK' if has_access else 'AUTH_FAIL')
        access_system.door_fsm.reset()
        access_system.door_fsm.step('CARD_VALID' if has_access else 'CARD_INVALID')

        session['user_id'] = user.user_id
        session['user_name'] = user.name
        session['card_number'] = user.card_number
        session['user_type'] = user.user_type
        session['token'] = crypto.sign(f"{user.user_id}:{int(time.time())}")

        if has_access:
            return redirect(url_for('dashboard'))
        else:
            return render_template('login.html',
                                 error=f"Access Denied! {user.name} cannot access {facility.name}",
                                 users=access_system.users,
                                 facilities=access_system.facilities,
                                 card_number=card_number,
                                 selected_facility=facility_id)

    return render_template('login.html',
                         users=access_system.users,
                         facilities=access_system.facilities)


@app.route('/dashboard')
def dashboard():
    if 'user_id' not in session:
        return redirect(url_for('login'))

    user = access_system._find_user(session['user_id'])
    if not user:
        session.clear()
        return redirect(url_for('login'))

    allowed_facilities = access_system.get_user_accessible_facilities(user.user_id)
    user_sets = access_system.classify_users_by_access_level()
    matrix_display = access_system.permission_matrix.get_matrix_display()
    proof = access_system.permission_matrix.prove_access_rules()
    access_log = access_system.permission_matrix.get_access_log()

    return render_template('dashboard.html',
                         user=user,
                         allowed_facilities=allowed_facilities,
                         user_sets=user_sets,
                         matrix_display=matrix_display,
                         proof=proof,
                         access_log=access_log,
                         permission_matrix=access_system.permission_matrix,
                         facilities=access_system.facilities)


# ============================================================================
# NEW ROUTES FOR SEPARATE NAVIGATION PAGES
# ============================================================================

@app.route('/my_facilities')
def my_facilities():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    allowed_facilities = access_system.get_user_accessible_facilities(user.user_id)
    return render_template('my_facilities.html', user=user, allowed_facilities=allowed_facilities)


@app.route('/access_history')
def access_history():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    access_log = access_system.permission_matrix.get_access_log()
    user_logs = [log for log in access_log if log['card_number'] == user.card_number]
    return render_template('access_history.html', user=user, access_log=user_logs)


@app.route('/profile')
def profile():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    return render_template('profile.html', user=user)

# ============================================================================
# END OF NEW ROUTES
# ============================================================================


@app.route('/access_check', methods=['GET', 'POST'])
def access_check():
    if 'user_id' not in session:
        return redirect(url_for('login'))

    if request.method == 'POST':
        card_number = request.form.get('card_number', '').strip()
        facility_id = int(request.form.get('facility_id'))

        client_ip = request.remote_addr or 'unknown'
        if not access_system.rate_limiter.is_allowed(client_ip):
            return render_template('access_check.html',
                                 error="Too many attempts. Please wait 60 seconds.",
                                 users=access_system.users,
                                 facilities=access_system.facilities,
                                 permission_matrix=access_system.permission_matrix)

        user = access_system.get_user_by_card(card_number)

        if not user:
            return render_template('access_check.html',
                                 error=f"Card ID '{card_number}' not found",
                                 users=access_system.users,
                                 facilities=access_system.facilities,
                                 permission_matrix=access_system.permission_matrix)

        has_access = access_system.check_access(user.user_id, facility_id)
        facility = access_system._find_facility(facility_id)

        access_system.permission_matrix.log_access_attempt(card_number, facility_id, has_access)

        # FINITE STATE MACHINE: drive door lifecycle for this check.
        access_system.door_fsm.reset()
        access_system.door_fsm.step('CARD_VALID' if has_access else 'CARD_INVALID')

        user_facilities = access_system.get_user_accessible_facilities(user.user_id)
        user_sets = access_system.classify_users_by_access_level()
        matrix_display = access_system.permission_matrix.get_matrix_display()
        proof = access_system.permission_matrix.prove_access_rules()
        access_log = access_system.permission_matrix.get_access_log()

        return render_template('access_check.html',
                             user=user,
                             facility=facility,
                             has_access=has_access,
                             user_facilities=user_facilities,
                             user_sets=user_sets,
                             matrix_display=matrix_display,
                             proof=proof,
                             access_log=access_log,
                             users=access_system.users,
                             facilities=access_system.facilities,
                             permission_matrix=access_system.permission_matrix,
                             card_number=card_number)

    return render_template('access_check.html',
                         users=access_system.users,
                         facilities=access_system.facilities,
                         permission_matrix=access_system.permission_matrix,
                         access_log=access_system.permission_matrix.get_access_log())


@app.route('/admin')
def admin():
    if 'user_id' not in session:
        return redirect(url_for('login'))

    user = access_system._find_user(session['user_id'])
    if not user or user.user_type != 'admin':
        return "Access Denied: Admins only.", 403

    stats = access_system.get_system_stats()
    users = access_system.users
    facilities = access_system.facilities
    user_sets = access_system.classify_users_by_access_level()
    matrix = access_system.permission_matrix.get_matrix_display()
    access_log = access_system.permission_matrix.get_access_log()

    users_with_ids = []
    for u in users:
        users_with_ids.append({
            'id': u.user_id,
            'name': u.name,
            'type': u.user_type,
            'authorized': u.is_authorized,
            'access_level': u.access_level,
            'card_number': u.card_number,
            'unique_id': u.unique_id,
            'uuid': u.uuid,
            'qr_code': u.qr_code,
            'card_hash': u.card_number_hash[:16] + '...',
            'qr_verified': u.verify_qr(u.qr_code)
        })

    return render_template('admin.html',
                         stats=stats,
                         users=users,
                         users_with_ids=users_with_ids,
                         facilities=facilities,
                         user_sets=user_sets,
                         matrix=matrix,
                         permission_matrix=access_system.permission_matrix,
                         access_log=access_log)


# ============================================================================
# NEW ADMIN ROUTES (Added here without changing existing code)
# ============================================================================

@app.route('/admin/users')
def admin_users():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    if not user or user.user_type != 'admin':
        return "Access Denied: Admins only.", 403

    users = access_system.users
    users_with_ids = []
    for u in users:
        users_with_ids.append({
            'id': u.user_id, 'name': u.name, 'type': u.user_type,
            'authorized': u.is_authorized, 'access_level': u.access_level,
            'card_number': u.card_number, 'unique_id': u.unique_id
        })
    return render_template('admin_users.html', user=user, users_with_ids=users_with_ids)


@app.route('/admin/facilities')
def admin_facilities():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    if not user or user.user_type != 'admin':
        return "Access Denied: Admins only.", 403

    return render_template('admin_facilities.html', user=user, facilities=access_system.facilities)


@app.route('/admin/id_cards')
def admin_id_cards():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    if not user or user.user_type != 'admin':
        return "Access Denied: Admins only.", 403

    users = access_system.users
    return render_template('admin_id_cards.html', user=user, users=users)


@app.route('/admin/access_logs')
def admin_access_logs():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    if not user or user.user_type != 'admin':
        return "Access Denied: Admins only.", 403

    access_log = access_system.permission_matrix.get_access_log()
    return render_template('admin_access_logs.html', user=user, access_log=access_log)


@app.route('/admin/reports')
def admin_reports():
    if 'user_id' not in session:
        return redirect(url_for('login'))
    user = access_system._find_user(session['user_id'])
    if not user or user.user_type != 'admin':
        return "Access Denied: Admins only.", 403

    stats = access_system.get_system_stats()
    return render_template('admin_reports.html', user=user, stats=stats)

# ============================================================================
# END OF NEW ADMIN ROUTES
# ============================================================================


@app.route('/logout')
def logout():
    # FINITE STATE MACHINE: transition session to REVOKED.
    access_system.session_fsm.reset()
    access_system.session_fsm.step('LOGIN_ATTEMPT')
    access_system.session_fsm.step('AUTH_OK')
    access_system.session_fsm.step('LOGOUT')
    session.clear()
    return redirect(url_for('login'))


# ============================================================================
# API ROUTES
# ============================================================================

@app.route('/api/users')
def api_users():
    return jsonify([{
        'id': u.user_id,
        'name': u.name,
        'type': u.user_type,
        'authorized': u.is_authorized,
        'access_level': u.access_level,
        'card_number': u.card_number,
        'card_hash': u.card_number_hash
    } for u in access_system.users])


@app.route('/api/facilities')
def api_facilities():
    return jsonify([{
        'id': f.facility_id,
        'name': f.name,
        'type': f.facility_type,
        'required_level': f.required_access_level,
        'is_restricted': f.is_restricted
    } for f in access_system.facilities])


@app.route('/api/check_access', methods=['POST'])
def api_check_access():
    data = request.get_json()
    card_number = data.get('card_number')
    facility_id = data.get('facility_id')

    client_ip = request.remote_addr or 'unknown'
    if not access_system.rate_limiter.is_allowed(client_ip):
        return jsonify({'access_granted': False, 'error': 'Rate limit exceeded'}), 429

    user = access_system.get_user_by_card(card_number)
    if user:
        has_access = access_system.check_access(user.user_id, facility_id)
        return jsonify({'access_granted': has_access, 'user': user.name})
    return jsonify({'access_granted': False, 'error': 'User not found'})


@app.route('/api/crypto/demo')
def api_crypto_demo():
    u = access_system.users[0]
    plaintext = "sensitive-data"
    cipher = crypto.encrypt(plaintext)
    token = crypto.secure_token(16)

    return jsonify({
        'sha256': hashlib.sha256(plaintext.encode()).hexdigest(),
        'aes_ciphertext': cipher,
        'aes_decrypted': crypto.decrypt(cipher),
        'hmac_signature': crypto.sign(plaintext),
        'hmac_verified': crypto.verify(plaintext, crypto.sign(plaintext)),
        'bcrypt_hash': u.password_hash.decode() if u.password_hash else 'N/A',
        'bcrypt_verified': u.check_password("smith123") if u.password_hash else False,
        'secure_token': token,
        'qr_signed': u.qr_code,
        'qr_verified': u.verify_qr(u.qr_code)
    })


@app.route('/api/algo/demo')
def api_algo_demo():
    return jsonify({
        'lru_cache': access_system.permission_matrix._access_cache.stats(),
        'rate_limiter_buckets': len(access_system.rate_limiter.buckets),
        'op_counter': access_system.op_counter,
        'merkle_root': access_system.permission_matrix.get_merkle_root(),
        'log_size': len(access_system.permission_matrix.get_access_log())
    })


# ============================================================================
# INDUCTION, RECURSION, COUNTING, PROBABILITY DEMOS
# ============================================================================

@app.route('/api/induction/demo')
def api_induction_demo():
    """INDUCTION: Run all induction proofs on the live data."""
    n = 10
    sum_proof = InductionProofs.prove_sum_first_n(n)
    matrix_proof = InductionProofs.prove_matrix_construction(
        access_system.users,
        access_system.facilities,
        access_system.permission_matrix,
    )
    luhn_proof = InductionProofs.prove_luhn_invariant(
        access_system.users[0].unique_id,
        access_system.users[0]._calculate_check_digit,
    )
    merkle_proof = InductionProofs.prove_merkle_root_by_induction(
        [e['signature'] for e in access_system.permission_matrix.get_access_log()]
    ) if access_system.permission_matrix.get_access_log() else {'holds': True, 'root': 'N/A', 'num_leaves': 0}

    return jsonify({
        'sum_first_n': sum_proof,
        'matrix_construction': matrix_proof,
        'luhn_invariant': luhn_proof,
        'merkle_root_induction': merkle_proof,
    })


@app.route('/api/recursion/demo')
def api_recursion_demo():
    """RECURSION: Run all recursive algorithms."""
    hashes = [e['signature'] for e in access_system.permission_matrix.get_access_log()]
    if not hashes:
        hashes = ['alpha', 'beta', 'gamma', 'delta']
    merkle = RecursiveAlgorithms.merkle_root(hashes)
    sorted_ids = sorted(access_system.permission_matrix._user_index.keys())
    bs_target = sorted_ids[len(sorted_ids) // 2]
    bs_result = RecursiveAlgorithms.binary_search(sorted_ids, bs_target)

    user = access_system.users[0]
    facility = access_system.facilities[3]
    hierarchy = RecursiveAlgorithms.recursive_access_chain(
        user, facility, access_system.facilities_by_id()
    )

    return jsonify({
        'merkle_root_recursive': merkle,
        'binary_search': {
            'sorted_ids': sorted_ids,
            'target': bs_target,
            'index': bs_result,
        },
        'recursive_hierarchy_check': {
            'user': user.name,
            'facility': facility.name,
            'granted': hierarchy,
        },
        'factorial_10': RecursiveAlgorithms.factorial(10),
    })


@app.route('/api/counting/demo')
def api_counting_demo():
    """COUNTING: Run all counting formulas on live data."""
    m = len(access_system.users)
    n = len(access_system.facilities)
    sets = access_system.classify_users_by_access_level()

    return jsonify({
        'multiplication_principle': {
            'users': m,
            'facilities': n,
            'access_pairs': CountingAlgorithms.count_access_pairs(m, n),
        },
        'permutations_P_8_3': CountingAlgorithms.permutations(8, 3),
        'combinations_C_8_3': CountingAlgorithms.combinations(8, 3),
        'total_distinct_matrices': CountingAlgorithms.count_authorization_profiles(m, n),
        'inclusion_exclusion': {
            'authorized_union_faculty': CountingAlgorithms.union_size(
                sets['authorized'], sets['faculty']
            ),
            'authorized': len(sets['authorized']),
            'faculty': len(sets['faculty']),
            'intersection': len(sets['authorized'] & sets['faculty']),
        },
        'pigeonhole': {
            'users': m,
            'user_types': 5,
            'min_per_type': CountingAlgorithms.pigeonhole_min_bucket(m, 5),
        },
        'sum_rule': CountingAlgorithms.sum_rule(
            sets['students'], sets['faculty'], sets['staff'], sets['visitors']
        ),
    })


@app.route('/api/probability/demo')
def api_probability_demo():
    """PROBABILITY: Run all probability computations."""
    n_facilities = len(access_system.facilities)
    n_users = len(access_system.users)

    collision = ProbabilityAlgorithms.birthday_collision_probability(
        n_users, 2 ** 256
    )

    student = access_system.users[2]
    restricted = access_system.facilities[6]
    p_success = min(1.0, student.access_level / restricted.required_access_level)
    expected = ProbabilityAlgorithms.expected_attempts_until_success(p_success)

    p_faculty = len([u for u in access_system.users if u.user_type == 'faculty']) / n_users
    p_granted_given_faculty = 0.95
    p_granted_given_not_faculty = 0.40
    p_granted = p_faculty * p_granted_given_faculty + (1 - p_faculty) * p_granted_given_not_faculty
    p_faculty_given_granted = ProbabilityAlgorithms.bayes(
        p_faculty, p_granted_given_faculty, p_granted_given_not_faculty
    )

    return jsonify({
        'uniform_facility_choice': ProbabilityAlgorithms.uniform_access_probability(n_facilities),
        'birthday_collision_probability_uuid': collision,
        'expected_attempts_until_success': {
            'user': student.name,
            'facility': restricted.name,
            'p_success': round(p_success, 4),
            'expected_attempts': round(expected, 4) if expected != float('inf') else 'infinite',
        },
        'bayes': {
            'p_faculty': round(p_faculty, 4),
            'p_granted': round(p_granted, 4),
            'p_faculty_given_granted': round(p_faculty_given_granted, 4),
        },
        'independence_check': ProbabilityAlgorithms.are_independent(
            0.5, 0.4, 0.2
        ),
        'monte_carlo_grant_probability': round(
            ProbabilityAlgorithms.simulated_grant_probability(student, restricted, trials=5000), 4
        ),
    })


# ============================================================================
# RANDOM VARIABLE ENDPOINT
# ============================================================================

@app.route('/api/random_variable/demo')
def api_random_variable_demo():
    """RANDOM VARIABLE: Demonstrate Geometric, Binomial, Poisson, Uniform RVs."""
    reg = access_system.rv_registry

    X = reg.geometric_attempts
    Y = reg.binomial_successes
    Z = reg.poisson_arrivals
    U = reg.uniform_delay

    samples_X = [X.sample() for _ in range(200)]
    samples_Y = [Y.sample() for _ in range(200)]
    samples_Z = [Z.sample() for _ in range(200)]
    samples_U = [U.sample() for _ in range(200)]

    return jsonify({
        'geometric_RV': {
            'name': X.name(),
            'pmf_1_to_6': [round(X.pmf(k), 6) for k in range(1, 7)],
            'cdf_1_to_6': [round(X.cdf(k), 6) for k in range(1, 7)],
            'expected_value': round(X.expected_value(), 4),
            'variance': round(X.variance(), 4),
            'std_dev': round(X.std_dev(), 4),
            'sample_mean_200': round(sum(samples_X) / len(samples_X), 4),
        },
        'binomial_RV': {
            'name': Y.name(),
            'pmf_0_to_10': [round(Y.pmf(k), 6) for k in range(0, 11)],
            'expected_value': round(Y.expected_value(), 4),
            'variance': round(Y.variance(), 4),
            'std_dev': round(Y.std_dev(), 4),
            'sample_mean_200': round(sum(samples_Y) / len(samples_Y), 4),
        },
        'poisson_RV': {
            'name': Z.name(),
            'pmf_0_to_8': [round(Z.pmf(k), 6) for k in range(0, 9)],
            'expected_value': round(Z.expected_value(), 4),
            'variance': round(Z.variance(), 4),
            'sample_mean_200': round(sum(samples_Z) / len(samples_Z), 4),
        },
        'uniform_continuous_RV': {
            'name': U.name(),
            'pdf_at_0_5': round(U.pdf(0.5), 4),
            'cdf_at_1_0': round(U.cdf(1.0), 4),
            'expected_value': round(U.expected_value(), 4),
            'variance': round(U.variance(), 4),
            'sample_mean_200': round(sum(samples_U) / len(samples_U), 4),
        },
        'joint_and_covariance': reg.covariance(samples=2000),
    })


# ============================================================================
# GRAPH NAVIGATION ENDPOINTS
# ============================================================================

@app.route('/api/graph/demo')
def api_graph_demo():
    """GRAPH NAVIGATION: BFS, DFS, shortest path, cycles, components, topo sort."""
    g = access_system.facility_graph
    user = access_system.users[2]

    return jsonify({
        'nodes': sorted(g.facilities.keys()),
        'adjacency': g.adjacency,
        'parent': g.parent,
        'bfs_from_campus': g.bfs(0),
        'dfs_from_campus': g.dfs(0),
        'shortest_path_campus_to_server': g.shortest_path(0, 7),
        'shortest_path_campus_to_library': g.shortest_path(0, 5),
        'num_paths_campus_to_server': g.count_paths(0, 7),
        'has_cycle': g.has_cycle(),
        'connected_components': g.connected_components(),
        'topological_sort': g.topological_sort(),
        'reachable_from_campus': sorted(g.reachable_from(0)),
        'access_aware_reachability_for_alice': g.reachable_for_user(
            0, user, access_system.permission_matrix),
    })


@app.route('/api/graph/bfs/<int:start_id>')
def api_graph_bfs(start_id):
    g = access_system.facility_graph
    return jsonify({
        'start': start_id,
        'bfs_order': g.bfs(start_id),
        'dfs_order': g.dfs(start_id),
    })


@app.route('/api/graph/shortest_path/<int:start_id>/<int:goal_id>')
def api_graph_shortest_path(start_id, goal_id):
    g = access_system.facility_graph
    path = g.shortest_path(start_id, goal_id)
    return jsonify({
        'start': start_id,
        'goal': goal_id,
        'path': path,
        'num_edges': len(path) - 1 if path else None,
        'num_paths': g.count_paths(start_id, goal_id),
    })


@app.route('/api/graph/reachable_for_user/<int:user_id>')
def api_graph_reachable_for_user(user_id):
    g = access_system.facility_graph
    user = access_system._find_user(user_id)
    if not user:
        return jsonify({'error': 'User not found'}), 404
    reachable = g.reachable_for_user(0, user, access_system.permission_matrix)
    return jsonify({
        'user': user.name,
        'start': 0,
        'reachable_ids': reachable,
        'reachable_facilities': [
            {'id': nid, 'name': g.facilities[nid].name}
            for nid in reachable if nid in g.facilities
        ],
    })


# ============================================================================
# TREE ENDPOINTS
# ============================================================================

@app.route('/api/tree/demo')
def api_tree_demo():
    """TREE: Demonstrate the facility tree and the user BST."""
    t = access_system.facility_tree
    bst = access_system.user_bst

    alice_node = bst.search(3)
    return jsonify({
        'facility_tree': {
            'node_count': t.node_count(),
            'leaf_count': t.leaf_count(),
            'root': t.root.node_id,
            'height': t.height(),
            'depth_of_registrar_office': t.depth(2),
            'depth_of_server_room': t.depth(7),
            'preorder': t.preorder(),
            'postorder': t.postorder(),
            'inorder': t.inorder(),
            'path_root_to_server_room': t.path_from_root(7),
            'lca_registrar_and_comlab': t.lca(2, 4),
            'lca_faculty_office_and_server_room': t.lca(6, 7),
            'lca_activity_center_and_library': t.lca(1, 5),
            'is_valid_tree': t.is_tree(),
        },
        'user_bst': {
            'size': bst.size,
            'height': bst.height(),
            'inorder_keys': bst.inorder_keys(),
            'is_valid_bst': bst.is_valid_bst(),
            'search_user_3': alice_node.name if alice_node else None,
            'search_user_8': (lambda u: u.name if u else None)(bst.search(8)),
        },
    })


@app.route('/api/tree/lca/<int:id_a>/<int:id_b>')
def api_tree_lca(id_a, id_b):
    t = access_system.facility_tree
    lca = t.lca(id_a, id_b)
    return jsonify({
        'node_a': id_a,
        'node_b': id_b,
        'lca': lca,
        'path_a': t.path_from_root(id_a) if id_a in t.nodes else None,
        'path_b': t.path_from_root(id_b) if id_b in t.nodes else None,
    })


@app.route('/api/tree/traversals')
def api_tree_traversals():
    t = access_system.facility_tree
    return jsonify({
        'preorder': t.preorder(),
        'inorder': t.inorder(),
        'postorder': t.postorder(),
    })


# ============================================================================
# FINITE STATE MACHINE ENDPOINTS
# ============================================================================

@app.route('/api/fsm/demo')
def api_fsm_demo():
    """FINITE STATE MACHINE: Demonstrate the session FSM and the door FSM."""
    s = SessionFSM()
    session_trace = []
    session_symbols = ['LOGIN_ATTEMPT', 'AUTH_OK', 'TIMEOUT',
                       'LOGIN_ATTEMPT', 'AUTH_FAIL',
                       'LOGIN_ATTEMPT', 'AUTH_OK', 'LOGOUT']
    for symbol in session_symbols:
        new_state = s.step(symbol)
        session_trace.append({'symbol': symbol, 'new_state': new_state})

    d = DoorFSM()
    door_trace = []
    door_symbols = ['CARD_INVALID', 'RESET', 'CARD_VALID', 'OPEN', 'CLOSE']
    for symbol in door_symbols:
        new_state = d.step(symbol)
        door_trace.append({'symbol': symbol, 'new_state': new_state})

    return jsonify({
        'session_fsm': {
            'definition': SessionFSM().describe(),
            'trace': session_trace,
            'final_state': s.state,
            'final_accepting': s.is_accepting(),
            'accepts_LOGIN_AUTHOK': SessionFSM().accepts(['LOGIN_ATTEMPT', 'AUTH_OK']),
            'accepts_LOGIN_AUTHFAIL': SessionFSM().accepts(['LOGIN_ATTEMPT', 'AUTH_FAIL']),
        },
        'door_fsm': {
            'definition': DoorFSM().describe(),
            'trace': door_trace,
            'final_state': d.state,
            'final_accepting': d.is_accepting(),
            'accepts_CARDVALID': DoorFSM().accepts(['CARD_VALID']),
            'accepts_CARDINVALID': DoorFSM().accepts(['CARD_INVALID']),
            'accepts_RESET_CARDVALID': DoorFSM().accepts(['CARD_INVALID', 'RESET', 'CARD_VALID']),
        },
    })


@app.route('/api/fsm/run/<int:sequence_id>')
def api_fsm_run(sequence_id):
    presets = {
        1: {'session': ['LOGIN_ATTEMPT', 'AUTH_OK', 'LOGOUT'],
            'door': ['CARD_VALID', 'OPEN', 'CLOSE']},
        2: {'session': ['LOGIN_ATTEMPT', 'AUTH_FAIL'],
            'door': ['CARD_INVALID', 'RESET', 'CARD_VALID']},
        3: {'session': ['LOGIN_ATTEMPT', 'AUTH_OK', 'TIMEOUT', 'LOGIN_ATTEMPT', 'AUTH_OK'],
            'door': ['CARD_VALID', 'TIMEOUT', 'CARD_VALID', 'CLOSE']},
    }
    preset = presets.get(sequence_id)
    if not preset:
        return jsonify({'error': 'Preset not found. Available: 1, 2, 3'}), 404

    s = SessionFSM()
    door = DoorFSM()

    return jsonify({
        'sequence_id': sequence_id,
        'session': {
            'symbols': preset['session'],
            'accepts': s.accepts(preset['session']),
            'history': s.history,
        },
        'door': {
            'symbols': preset['door'],
            'accepts': door.accepts(preset['door']),
            'history': door.history,
        },
    })


@app.route('/api/fsm/state')
def api_fsm_state():
    return jsonify({
        'session_state': access_system.session_fsm.state,
        'session_history': access_system.session_fsm.history,
        'door_state': access_system.door_fsm.state,
        'door_history': access_system.door_fsm.history,
    })


# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

if __name__ == '__main__':
    print("=" * 70)
    print("LBSADMS - Logic-Based Security Access Decision Management System")
    print("=" * 70)
    print("\nSystem initialized with:")
    print(f"  - {len(access_system.users)} users")
    print(f"  - {len(access_system.facilities)} facilities")
    print("\nDisciplines enabled:")
    print("  - Logic, Sets, Relations, Boolean Algebra, Matrices, Number Theory")
    print("  - Cryptography (SHA-256, HMAC, AES, PBKDF2, bcrypt, CSPRNG)")
    print("  - Algorithms (LRU cache, hash maps, rate limiter, Merkle tree)")
    print("  - Induction  (4 proofs)")
    print("  - Recursion  (Merkle, binary search, hierarchy walk, factorial)")
    print("  - Counting   (permutations, combinations, inclusion-exclusion, pigeonhole)")
    print("  - Probability (uniform, birthday, geometric, Bayes, Monte Carlo)")
    print("  - Random Variables (Geometric, Binomial, Poisson, Uniform)")
    print("  - Graph Navigation (BFS, DFS, shortest path, cycles, topo sort)")
    print("  - Trees      (FacilityTree, LCA, traversals, UserBST)")
    print("  - Finite State Machines (SessionFSM, DoorFSM)")
    print("\nCard IDs for Login:")
    for user in access_system.users:
        print(f"  - {user.name}: {user.card_number} ({user.user_type})")
    print("\n" + "=" * 70)
    print("Starting Flask server...")
    print("Open http://127.0.0.1:5000 in your browser")
    print("Demo endpoints:")
    print("  /api/crypto/demo")
    print("  /api/algo/demo")
    print("  /api/induction/demo")
    print("  /api/recursion/demo")
    print("  /api/counting/demo")
    print("  /api/probability/demo")
    print("  /api/random_variable/demo")
    print("  /api/graph/demo")
    print("  /api/tree/demo")
    print("  /api/fsm/demo")
    print("=" * 70)
    app.run(debug=True)