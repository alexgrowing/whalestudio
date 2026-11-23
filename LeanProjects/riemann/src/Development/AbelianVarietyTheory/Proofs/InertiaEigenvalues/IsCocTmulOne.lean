import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter

namespace GlobalTheory.TensorOneCoc

theorem isCoc_tmul_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (G : Subgroup (GQ l)) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥G →* (Y →ₗ[ℤ_[l]] Y)) (b : ℤ) (f : ↥G → Y), (∀ g h, f (g * h) = f g + ρ g (f h)) → (∀ (n : ℕ) (g : ↥G), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y) → ∀ one : ↥(Mxi (AinfSub l) (xiU AI) 0), (one : WCb l) = 1 → letI : TopologicalSpace (TensorProduct ℤ_[l] Y (Qab (AinfSub l) (xiU AI) 0 b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; IsCoc (repQ AI G ρ 0 b) (fun g => f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b)) := by
  intro l _ P AI G Y _ _ ρ b f hf hc one h1
  refine ⟨(GlobalTheory.continuous_adicModule_iff (l : ℤ_[l]) _).2 fun g n => ?_, fun g h => ?_⟩
  · filter_upwards [hc n g] with h ⟨y, e⟩
    refine ⟨y ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b), ?_⟩
    rw [← TensorProduct.sub_tmul, e, TensorProduct.smul_tmul', ← Nat.cast_pow,
      Nat.cast_smul_eq_nsmul]
  · have hq : actQab (xiOK AI) 0 b (g : GQ l)
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b) = Submodule.Quotient.mk one := by
      rw [actQab, Submodule.mapQ_apply]
      congr 1
      apply Subtype.ext
      change AI.actWCbHom (g : GQ l) (one : WCb l) = one
      rw [h1, map_one]
    have : repQ AI G ρ 0 b g (f h ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b))
        = ρ g (f h) ⊗ₜ[ℤ_[l]] actQab (xiOK AI) 0 b (g : GQ l) (Submodule.Quotient.mk one) := rfl
    beta_reduce
    rw [this, hq, hf, TensorProduct.add_tmul]

end GlobalTheory.TensorOneCoc
