import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorLatSpan

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem use₂ {Kf K ι : Type} [Field Kf] [Field K] [Fintype ι] {n : ℕ} (eK : K →+* Kf) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map eK (actP lam B F) = actP lam (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) := by
  have h1 : (MvPolynomial.map eK).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc eK (B τ))).toRingHom.comp (MvPolynomial.map eK) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map eK (trAct B F) = trAct (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) :=
    congrArg (fun φ : Pol K ι n →+* Pol Kf ι n => φ F) h1
  have h3 : eK (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc eK (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

end GlobalTheory.ValCmp
