class OrderDictionary:
    def __init__(self, m, n, order_coefficients):
        self.invariants = (m,n)
        qa.<i,j,k> = QuaternionAlgebra(QQ,m,n)
        self.quaternion_algebra = qa

        order_list = []

        for elem in order_coefficients:
            order_list.append(elem[0] + elem[1] * i + elem[2] * j + elem[3] * k)

        self.basis = order_list
        self.order= qa.quaternion_order(order_list)

        [base1, base2, base3] = (self.order.basis())[0:3]
        fr_coords = []

        for x in range(2):
            for y in range(2):
                for z in range(2):
                    fr_coords.append(x * base1 + y*base2 + z*base3)

        self.fundamental_domain_points = fr_coords

        r3_coeffs = []
        for i in range(3):
            r3_coeffs.append(order_coefficients[i][0:3])

        self.coordinate_matrix = Matrix(QQ, Matrix(QQ, r3_coeffs).transpose().inverse())

        norm_mat = [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]

        for i in range(4):
            for j in range(4):
                norm_mat[i][j] = (order_list[i] * (order_list[j].conjugate()))[0]

        self.norm_form = QuadraticForm(ZZ,2*Matrix(QQ,norm_mat))
        self.element_norm_dictionary = {0:0}
        self.largest_computed_norm = 0

    def __repr__(self):
        return(str(self.order) + " (with extra R3 information)")

    def is_positive(self, quaternion):
        [a,b,c,d] = quaternion

        if a == 0:
            if b == 0:
                if c == 0:
                    return d > 0

                return c > 0

            return b > 0

        return a > 0

    def elements_of_norm_N(self, N):
        if N <= self.largest_computed_norm:
            if N in self.element_norm_dictionary.keys():
                return self.element_norm_dictionary[N]

            else:
                return []

        bounded_norm_list = self.norm_form.representation_vector_list(N + 1)
        bounded_norm_list.reverse()

        for same_norm_list in bounded_norm_list:
            sample_norm = O.norm_form(same_norm_list[0])

            if sample_norm <= self.largest_computed_norm:
                break

            else:
                element_list = []

                for vector in same_norm_list:
                    [a,b,c,d] = vector
                    [e1, e2, e3, e4] = self.basis
                    element_list.append(a * e1 + b * e2 + c * e3 + d*e4)

                self.element_norm_dictionary[sample_norm] = element_list

        self.largest_computed_norm = N

        if N in self.element_norm_dictionary.keys():
            return self.element_norm_dictionary[N]

        else:
            return []

    def inR3(self, quaternion):
        qa.<i,j,k> = self.quaternion_algebra
        [a,b,c,d] = quaternion + 0*j

        return d == 0

    def involution(self, quaternion):
        qa.<i,j,k> = self.quaternion_algebra
        [a,b,c,d] = quaternion + 0*j
        return a + b*i + c*j - d*k

    def coordinates(self, quaternion, check = False):
        [a,b,c,d] = quaternion + 0*j

        if check and d != 0:
            raise ValueError

        vec = vector([a,b,c])

        mat = self.coordinate_matrix

        return mat * vec

    def floor(self, quaternion, check = False):
        coords = self.coordinates(quaternion, check)
        [a,b,c] = coords

        qa.<i,j,k> = self.quaternion_algebra
        coeffs = self.basis

        vec = floor(a) * vector(coeffs[0]) + floor(b) * vector(coeffs[1]) + floor(c) * vector(coeffs[2])

        return vec[0] + vec[1] * i + vec[2] * j

    def round(self, quaternion, check = False):
        qa.<i,j,k> = self.quaternion_algebra

        floor_quaternion = self.floor(quaternion, check)
        diff = quaternion - floor_quaternion

        distance_dictionary = {}

        fr_points = self.fundamental_domain_points

        for point in fr_points:
            dist = (diff - point).reduced_norm()
            distance_dictionary[dist] = point

        min_dist = min(distance_dictionary.keys())
        closest_quaternion = distance_dictionary[min_dist]

        return floor_quaternion + closest_quaternion

    def division_lemma(self, a, b):
        z = (b.conjugate()/b.reduced_norm()) * a
        q = self.round(z)
        r = a - b * q

        return (q,r)
    
    
class InversiveCoordinateSpace:
    def __init__(self, ord_dic):
        self.order_dictionary = ord_dic
        [e_0, e_1, e_2, e_3] = ord_dic.basis

        normal_1 = e_0 * k * e_1 - e_1 * k * e_0
        normal_2 = e_1 * k * e_2 - e_2 * k * e_1
        normal_3 = e_2 * k * e_0 - e_0 * k * e_2

        plane_1 = (0,0, normal_1)
        plane_2 = (0,0, normal_2)
        plane_3 = (0,0, normal_3)

        plane_4 = self.shift(plane_1, e_2)
        plane_5 = self.shift(plane_2, e_0)
        plane_6 = self.shift(plane_3, e_1)
        self.bounding_planes = ((plane_1, e_2), (plane_2, e_0), (plane_3, e_1), (plane_4, -e_2), (plane_5, -e_0), (plane_6, -e_1))

    def spheres_in_list(self, projection_list):
        (m,n) = self.order_dictionary.invariants

        sphere_coordinate_list = []

        for elem in projection_list:
            [k,co_k, xi] = elem

            if k != 0:
                radius = float(sqrt(-n)/k)

                [x,y,z,t] = xi/k

                x_adjusted = float(x)
                y_adjusted = float(y * sqrt(-m))
                z_adjusted = float(z * sqrt(-n))

                center = (x_adjusted, y_adjusted, z_adjusted)

                sphere_coordinate_list.append((center, radius))

        return sphere_coordinate_list

    def quadratic_form(self, inversive_coordinates):
        [k, co_k, xi] = inversive_coordinates

        return -k * co_k + xi.reduced_norm()

    def bilinear_form(self, inversive_coordinates1, inversive_coordinates2, check = False):
        [k1, co_k1, xi1] = inversive_coordinates1
        [k2, co_k2, xi2] = inversive_coordinates2

        (m,n) = self.order_dictionary.invariants
        [a1,b1,c1,d1] = xi1
        [a2,b2,c2,d2] = xi2

        if check:
            assert d1 == 0 and d2 == 0

        return -(k1 * co_k2 + k2 * co_k1)/2 + (a1 * a2 - m * b1 * b2 - n * c1 * c2)

    def reverse_orientation(self, inversive_coordinates):
        (k, co_k, xi) = inversive_coordinates

        return (-k, -co_k, -xi)

    def on_cone(self, inversive_coordinates):
        (m,n) = self.order_dictionary.invariants
        return self.quadratic_form(inversive_coordinates) == -n

    def are_intersecting(self, inversive_coordinates1, inversive_coordinates2):
        (m,n) = self.order_dictionary.invariants

        return abs(self.bilinear_form(inversive_coordinates1, inversive_coordinates2)) <= -n

    def all_externally_tangent_elements(self, base_element, element_list):
        (m,n) = self.order_dictionary.invariants

        externally_tangent_list = []

        for elem in element_list:
            if self.bilinear_form(base_element, elem) == n:
                externally_tangent_list.append(elem)

        return externally_tangent_list

    def external_tangency_sort(self, base_element, element_list):
        (m,n) = self.order_dictionary.invariants

        externally_tangent_list = []
        internally_tangent_list = []
        non_tangent_list = []

        for elem in element_list:
            product = self.bilinear_form(base_element, elem)

            if product == n:
                externally_tangent_list.append(elem)

            elif product == -n:
                internally_tangent_list.append(elem)

            else:
                non_tangent_list.append(elem)

        return [externally_tangent_list, internally_tangent_list, non_tangent_list]

    def sort_externally_tangent_elements(self, base_element, externally_tangent_list):
        (m,n) = self.order_dictionary.invariants

        equivalence_class_list = []

        for elem in externally_tangent_list:
            element_sorted = False

            for equivalence_class in equivalence_class_list:
                test_element = equivalence_class[0]

                if self.bilinear_form(elem, test_element) == -n:
                    equivalence_class.append(elem)
                    element_sorted = True
                    break

            if not element_sorted:
                equivalence_class_list.append([elem])

        return equivalence_class_list

    def largest_externally_tangent_elements(self, base_element, externally_tangent_list):
        equivalence_class_list = self.sort_externally_tangent_elements(base_element, externally_tangent_list)

        largest_elements = []

        for equivalence_class in equivalence_class_list:
            guess = equivalence_class[0]
            k_guess = guess[0]

            for elem in equivalence_class:
                if elem[0] < k_guess:
                    guess = elem
                    k_guess = guess[0]

            largest_elements.append(guess)

        return largest_elements

    def maximal_immediately_tangent_set(self, graph, new_leaves, elements_to_test):
        if len(new_leaves) == 0:
            return graph

        even_newer_leaves = set([])
        new_graph = graph.copy()

        for leaf in new_leaves:
            [externally_tangent_list, internally_tangent_list, irrelevant_list] = self.external_tangency_sort(leaf, elements_to_test)

            immediately_tangent_list = self.largest_externally_tangent_elements(leaf,externally_tangent_list)

            for elem in immediately_tangent_list:
                if elem not in graph:
                    even_newer_leaves.add(elem)
                    new_graph.add(elem)

        return self.maximal_immediately_tangent_set(new_graph, even_newer_leaves, elements_to_test)

    def shift(self, inversive_coordinates, translate):
        translate = translate + 0*i
        [k, co_k, xi] = inversive_coordinates

        xi_shifted = xi + k * translate
        co_k_shifted = 2 * self.bilinear_form(inversive_coordinates, (-1,0,translate)) + k * translate.reduced_norm()

        return (k, co_k_shifted, xi_shifted)

    def points_within_radius(self, projection):
        [k, co_k, xi] = projection

        if k == 0:
            print("Not implemented yet!")
            raise ValueError

        translate = self.order_dictionary.floor(xi/k)
        new_projection = self.shift(projection, -translate)

        (m,n) = self.order_dictionary.invariants
        [e_0, e_1, e_2, e_3] = self.order_dictionary.basis
        e_0_min = 0
        e_0_max = 1
        e_1_min = 0
        e_1_max = 1
        e_2_min = 0
        e_2_max = 1

        for plane_with_normal in self.bounding_planes:
            (plane, normal) = plane_with_normal

            if (self.bilinear_form(new_projection, plane))^2 <= -n * self.quadratic_form(plane):
                if normal == e_0:
                    e_0_max = 2

                if normal == -e_0:
                    e_0_min = -1

                if normal == e_1:
                    e_1_max = 2

                if normal == -e_1:
                    e_1_min = -1

                if normal == e_2:
                    e_2_max = 2

                if normal == -e_2:
                    e_2_min = -1

        point_list = []

        for a in range(e_0_min, e_0_max):
            for b in range(e_1_min, e_1_max):
                for c in range(e_2_min, e_2_max):
                    point_list.append(self.shift(new_projection, a*e_0 + b*e_1 + c*e_2))

        return point_list
    
    
class QuaternionMatrix:
    def __init__(self, ord_dic, mat):
        self.order_dictionary = ord_dic
        self.matrix = Matrix(ord_dic.quaternion_algebra, mat)

    def __repr__(self):
        return str(self.matrix)

    def __mul__(self, other):
        [[a_self,b_self],[c_self, d_self]] = self.matrix
        [[a_other,b_other],[c_other, d_other]] = other.matrix

        a = a_self * a_other + b_self * c_other
        b = a_self * b_other + b_self * d_other
        c = c_self * a_other + d_self * c_other
        d = c_self * b_other + d_self * d_other

        return QuaternionMatrix(self.order_dictionary, [[a,b],[c,d]])

    def bend(self):
        [[a,b],[c,d]] = self.matrix
        (m,n) = self.order_dictionary.invariants

        return -2 * n * (c.conjugate() * d)[2]

    def co_bend(self):
        [[a,b],[c,d]] = self.matrix
        (m,n) = self.order_dictionary.invariants

        return -2 * n * (a.conjugate() * b)[2]

    def xi(self):
        [[a,b],[c,d]] = self.matrix

        return a * j * (d.conjugate()) - b * j * (c.conjugate())

    def center(self):
        (m,n) = self.order_dictionary.invariants
        [a,b,c,d] = self.xi()/self.bend()

        return (float(a), float(b * sqrt(-m)), float(c * sqrt(-n)))

    def projection(self):
        return (self.bend(), self.co_bend(), self.xi())

    def is_in_SL2(self):
        [[a,b],[c,d]] = self.matrix
        O = self.order_dictionary

        if not O.inR3(a * O.involution(b)):
            return False

        if not O.inR3(c * O.involution(d)):
            return False

        if a * O.involution(d) - b * O.involution(c) == 1:
            return True

        return False
    
    
class FundamentalDomain:
    def __init__(self, ord_dic):
        self.order_dictionary = ord_dic
        (m0,n0) = ord_dic.invariants

        if m0 not in [-1,-2,-3,-7,-11]:
            print("Base ring is non-Euclidean.")
            raise ValueError

        self.m = m0
        self.n = n0

    def __repr__(self):
        return("Fundamental domain of SL_2(O \cap QQ(sqrt(" + str(self.m) +"))), where O is the " + str(self.order_dictionary))

    def j_coord_min(self):
        if self.m == -1:
            return 1/sqrt(-2*self.n)

        if self.m == -2:
            return 1/(2* sqrt(-self.n))

        if self.m == -3:
            return sqrt(-2/(3 * self.n))

        if self.m == -7:
            return sqrt(-5/self.n)/4

        if self.m == -11:
            return 1/(4 * sqrt(-self.n))

        print("Something went wrong---(m,n) values have been changed.")
        raise ValueError

    def inverse_j_coord_min(self, j_upper_bound):
        if self.m == -1:
            return 2*j_upper_bound/(1 - 2 * self.n * j_upper_bound^2)

        if self.m == -2:
            return 4*j_upper_bound/(3 - 4 * self.n * j_upper_bound^2)

        if self.m == -3:
            if j_upper_bound >= 1/sqrt(-self.n):
                return j_upper_bound/(1 - self.n * j_upper_bound^2)

            if j_upper_bound >= sqrt(-3/self.n)/2:
                return j_upper_bound/(2 - sqrt(1 + self.n * j_upper_bound^2))

            min_j = self.j_coord_min()

            if j_upper_bound <= min_j:
                return min_j

            return 2 * j_upper_bound/(3 + sqrt(9 + 12 * self.n * j_upper_bound^2))

        if self.m == -7:
            return j_upper_bound/(11/16 - self.n * j_upper_bound^2)

        if self.m == -11:
            return j_upper_bound/(15/16 - self.n * j_upper_bound^2)
        
class Pair:
    def __init__(self, pair_list, ord_dic):
        self.order_dictionary = ord_dic
        self.pair = pair_list

    def R3_check(self):
        [a,b] = self.pair
        z = b.conjugate() * a

        return self.order_dictionary.inR3(z)

    def extended_Euclidean_algorithm(self):
        return self.extended_Euclidean_algorithm_helper(self.pair, (1,0), (0,1))

    def extended_Euclidean_algorithm_helper(self, r_pair, s_pair, t_pair):
        (r_past, r_current) = r_pair
        (s_past, s_current) = s_pair
        (t_past, t_current) = t_pair

        if r_current == 0:
            return (r_past, s_past, t_past)

        O = self.order_dictionary

        z = r_current.conjugate() * r_past

        if not O.inR3(z):
            print(r_pair)
            print(z)
            raise ValueError

        (q,r_new) = O.division_lemma(r_past, r_current)

        s_new = s_past - s_current * q
        t_new = t_past - t_current * q

        new_r_pair = (r_current, r_new)
        new_s_pair = (s_current, s_new)
        new_t_pair = (t_current, t_new)

        return self.extended_Euclidean_algorithm_helper(new_r_pair, new_s_pair, new_t_pair)

    def is_unimodular_pair(self):
        if not self.R3_check():
            return [False]

        [g,x,y] = self.extended_Euclidean_algorithm()

        [c,d] = self.pair
        O = self.order_dictionary

        if g == 1:
            a = O.involution(y)
            b = -O.involution(x)
            mat = QuaternionMatrix(O, [[a,b],[c,d]])
            return [True, mat]

        nrm = g.reduced_norm()

        if nrm != 1:
            return [False]

        a = O.involution(y * g.conjugate())
        b = -O.involution(x * g.conjugate())
        mat = QuaternionMatrix(O, [[a,b],[c,d]])
        return [True, mat]
    
    
class UnimodularPairs:
    def __init__(self, ord_dic, bend_upper_bound):
        self.order_dictionary = ord_dic
        self.bend_ub = bend_upper_bound

        n = -(ord_dic.invariants[1])

        F = FundamentalDomain(ord_dic)
        z_min = F.j_coord_min()

        c_upper_bound = ceil(bend_upper_bound/(2 * n * z_min))

        pair_list = []

        for c_norm in range(c_upper_bound,0, -1):
            c_list = O.elements_of_norm_N(c_norm)

            if c_list != []:
                inverse_z_min = F.inverse_j_coord_min(bend_upper_bound/(2 * n * c_norm))
                d_upper_bound = ceil(bend_upper_bound/(2 * n * inverse_z_min))

                for c in c_list:
                    for d_norm in range(d_upper_bound, 0, -1):
                        d_list = O.elements_of_norm_N(d_norm)

                        for d in d_list:
                            z = c.conjugate() * d

                            if z[3] == 0:
                                if z[2] != 0:
                                    bend = 2 * n * z[2]

                                    if abs(bend) <= bend_upper_bound:
                                        pair = Pair([c,d], ord_dic)
                                        results = pair.is_unimodular_pair()

                                        if results[0]:
                                            pair_list.append(results[1])

        self.unimodular_pairs = pair_list

    def __repr__(self):
        return("Unimodular pairs corresponding to bends bounded by " + str(self.bend_ub) + " with coefficients in the " + str(self.order_dictionary))

    def superpacking(self, remove_orientation = False):
        region = InversiveCoordinateSpace(self.order_dictionary)
        set_of_all_spheres = set([])

        for mat in self.unimodular_pairs:
            proj = mat.projection()

            if remove_orientation:
                if proj[0] < 0:
                    proj = region.reverse_orientation(proj)

            sphere_list = region.points_within_radius(proj)

            for sphere in sphere_list:
                set_of_all_spheres.add(sphere)

        return set_of_all_spheres

    def apollonian_packing(self):
        elements_to_test = self.superpacking(True)

        region = InversiveCoordinateSpace(self.order_dictionary)

        plane1 = (0,0,-j)
        plane2 = region.shift((0,0,j), self.order_dictionary.basis[2])

        graph = set([plane1, plane2])
        new_leaves = set([plane1, plane2])

        elements_to_test.add(plane1)
        elements_to_test.add(plane2)

        return region.maximal_immediately_tangent_set(graph, new_leaves, elements_to_test)
    
    
### Construction of desired super-integral crystallographic packings happens here.
    
def format_for_Mathematica(coord):
    (center, radius) = coord
    (x,y,z) = center
    
    center_string = "{" + (str(center)[1:-1]) + "}"
    radius_string = str(radius)
    
    return "{" + center_string + "," + radius_string + "}"

info_list = [((-3,-15), [[1,0,0,0], [1/2,1/2,0,0], [0,1/3,1/3,0],[0,0,1/2,1/6]], 100),((-7,-1), [[1,0,0,0], [1/2,1/2,0,0], [0,0,1,0],[0,0,1/2,1/2]], 20),((-11,-143), [[1,0,0,0], [1/2,1/2,0,0], [0,3/11,1/11,0],[0,0,1/2,1/22]], 260)]

for item in info_list:
    (inv, order_coeff, max_bend) = item
    (m,n) = inv

    O = OrderDictionary(m, n, order_coeff)
    Q.<i,j,k> = QuaternionAlgebra(QQ, m, n)
    I = InversiveCoordinateSpace(O)
    all_pairs = UnimodularPairs(O, max_bend)

    apollonian_list = all_pairs.apollonian_packing()
    sphere_coord_list = I.spheres_in_list(apollonian_list)
    
    sphere_packing_data = open("apollonian_packing_" + str(m) + "_" + str(n) + "_bends_up_to_" + str(max_bend) + ".txt", "w+")
    
    sphere_packing_data.write("{")
    sphere_packing_data.write(format_for_Mathematica(sphere_coord_list[0]))

    for elem in sphere_coord_list[1:]:
        sphere_packing_data.write(",")
        sphere_packing_data.write(format_for_Mathematica(elem))
    
    sphere_packing_data.write("}")
    sphere_packing_data.close()