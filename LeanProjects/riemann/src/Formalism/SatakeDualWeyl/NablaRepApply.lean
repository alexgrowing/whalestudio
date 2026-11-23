import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Actions
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LinSubstIsHomogeneous
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG

def stdRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Representation O (GL n O) (n → O) where
  toFun := stdAct O n
  map_one' := (P.standard_action_mul_holds O n 1 1).2
  map_mul' g h := (P.standard_action_mul_holds O n g h).1

def tensRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (⨂[O]^k (n → O)) where
  toFun := tensAct O n k
  map_one' := (P.tensor_action_mul_holds O n k 1 1).2
  map_mul' g h := (P.tensor_action_mul_holds O n k g h).1

def polyRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Representation O (GL n O) (MvPolynomial n O) where
  toFun g := (polyAct O n g).toLinearMap
  map_one' := by
    rw [(P.polynomial_action_mul_holds O n 1 1).2, AlgHom.toLinearMap_id]
    rfl
  map_mul' g h := by
    rw [(P.polynomial_action_mul_holds O n g h).1, AlgHom.comp_toLinearMap]
    rfl

def nablaRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (nabla O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict (fun P hP => Formalism.UG.P.nabla_subspace_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl

def weylRep (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ) :
    Representation O (GL n O) (weylSub O n k) where
  toFun g := (polyAct O n g).toLinearMap.restrict
    (fun P hP => Formalism.UG.P.weyl_module_stable O n k g P hP)
  map_one' := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n 1 (P : MvPolynomial n O) = (P : MvPolynomial n O)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n 1 1).2]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change polyAct O n (g * h) (P : MvPolynomial n O) = polyAct O n g (polyAct O n h P)
    rw [(Formalism.UG.P.polynomial_action_mul_holds O n g h).1]
    rfl

def ratEquiv {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] : UJ (σ : E →+* E) J ≃* ratPts σ J R :=
  Subgroup.equivMapOfInjective (UJ (σ : E →+* E) J) (bc (inclE (F := F) R))
    (Formalism.UG.P.UG_inclusion_injective F E n R inferInstance)

theorem tensRep_apply (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
    (g : GL n O) : tensRep O n k g = tensAct O n k g := rfl

theorem polyRep_apply (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (g : GL n O) : polyRep O n g = (polyAct O n g).toLinearMap := rfl

end Formalism.UG
