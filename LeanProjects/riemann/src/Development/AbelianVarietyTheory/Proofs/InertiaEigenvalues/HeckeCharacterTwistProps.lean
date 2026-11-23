import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormOneTwist

variable {D : D7}

def quotC (D : D7) : (AE D)ˣ →* (AE D)ˣ :=
  MonoidHom.id _ / Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def finQuot (D : D7) : (AE D)ˣ →* (GlobalTheory.FinalJoin.AfE D)ˣ :=
  (Units.map (finPart D).toMonoidHom).comp (quotC D)

theorem finPart_mul_inv (x : (AE D)ˣ) :
    finPart D (x : AE D) * finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
  rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]

theorem finQuot_val (x : (AE D)ˣ) :
    ((finQuot D x : (GlobalTheory.FinalJoin.AfE D)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      finPart D (x : AE D) * sigR (Af D.host.F) D.sp.cm.sig (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) := by
  show finPart D ((x : AE D) * sigR (AF D.host.F) D.sp.cm.sig ((x⁻¹ : (AE D)ˣ) : AE D)) = _
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]

theorem normOne_finQuot (x : (AE D)ˣ) : GlobalTheory.FinalJoin.NormOne (finQuot D x) := by
  change _ * sigR (Af D.host.F) D.sp.cm.sig _ = 1
  rw [finQuot_val]
  exact GlobalTheory.DetOnto.norm_one _ (GlobalTheory.DetOnto.sigR_sigR D) (finPart_mul_inv x)

theorem finQuot_of_isDetRoot {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetRoot V g x) :
    finQuot D x = Matrix.GeneralLinearGroup.det (finHom V g) := by
  apply Units.ext
  have h1 := congrArg (finPart D) hx
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR] at h1
  rw [finQuot_val, h1, mul_assoc, ← RingHom.map_mul, finPart_mul_inv x, RingHom.map_one, mul_one,
    GlobalTheory.DetRootChar.finPart_det]

theorem finQuot_incA (e : D.host.Eˣ) :
    ((finQuot D (Units.map (incA D).toMonoidHom e) : (GlobalTheory.FinalJoin.AfE D)ˣ) : GlobalTheory.FinalJoin.AfE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((e : D.host.E) * D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) := by
  rw [finQuot_val]
  show finPart D (incA D (e : D.host.E)) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (incA D ((e⁻¹ : D.host.Eˣ) : D.host.E))) = _
  show ((1 : Af D.host.F) ⊗ₜ[D.host.F] (e : D.host.E)) *
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def delta (xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ) (hn : ∀ u, GlobalTheory.FinalJoin.NormOne u → ‖((xi u : ℂˣ) : ℂ)‖ = 1) :
    (AE D)ˣ →* Circle where
  toFun x := ⟨((xi (finQuot D x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hn _ (normOne_finQuot x))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (show ((xi (finQuot D (x * y)) : ℂˣ) : ℂ) = ((xi (finQuot D x) : ℂˣ) : ℂ) * ((xi (finQuot D y) : ℂˣ) : ℂ) by
    rw [map_mul, map_mul, Units.val_mul])

end GlobalTheory.NormOneTwist

namespace GlobalTheory.NormOneTwist

variable {D : D7}

end GlobalTheory.NormOneTwist
