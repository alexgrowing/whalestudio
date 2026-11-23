import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatake
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa

namespace Formalism.UG.P

theorem satake_inert : Formalism.UG.SatakeInert := satake_transform_inert_prime exists_spherical_function_unitary

theorem satake_mul : Formalism.UG.SatMul := satake_transform_multiplicative exists_spherical_function_unitary

end Formalism.UG.P
