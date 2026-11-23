import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.DRMat

theorem invariant_coord_bounds : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (N : ℕ), DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) → DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥ → ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ≠ 0 → (∀ i, c i ∈ (P.PD K).Fil (-(N : ℤ))) ∧ ¬ ∀ i, c i ∈ (P.PD K).Fil ((N : ℤ) + 1) := by
  intro l _ P K d ρ N hlow hhigh c hc hc0
  let b := Pi.basisFun ℚ_[l] (Fin d)
  let M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR := fun g =>
    (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l]))
  let e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR ≃ₗ[ℚ_[l]] (Fin d → P.R.BdR) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl ℚ_[l] P.R.BdR) ≪≫ₗ
      TensorProduct.comm ℚ_[l] (Fin d → ℚ_[l]) P.R.BdR ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR (Fin d)
  have he_tmul : ∀ v β, e (v ⊗ₜ β) = fun i => v i • β := by
    intro v β
    simp [e, b]
  have he : ∀ (g : ↥(GK K)) x, e (actVdR (P.PD K) (qRep ρ) g x) = M g *ᵥ fun i => P.actQdR (g : GQ l) (e x i) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, he_tmul, he_tmul]
      funext i
      simp only [M, qRep, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul,
        AlgEquiv.commutes, MonoidHom.coe_comp, Function.comp_apply]
      change algebraMap ℚ_[l] P.R.BdR ((((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) i) * _ = _
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [PadicInt.algebraMap_apply]
      ring
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  set x : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR := ∑ i, Pi.single i (1 : ℚ_[l]) ⊗ₜ c i with hx
  have hex : e x = c := by
    rw [hx, map_sum]
    funext j
    simp only [he_tmul, Finset.sum_apply, Pi.single_apply, ite_smul, one_smul, zero_smul]
    simp
  have hxD : x ∈ DdR (P.PD K) (qRep ρ) := by
    rw [GlobalTheory.DRFil.mem_DdR]
    intro g
    apply e.injective
    rw [he, hex]
    exact hc g
  have hcoord : ∀ (a : ℤ) (y : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR),
      y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) a → ∀ i, e y i ∈ (P.PD K).Fil a := by
    intro a y hy i
    refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun y => e y i ∈ (P.PD K).Fil a) ?_ ?_ ?_ hy
    · simp
    · intro v β hβ
      rw [he_tmul]
      exact ((P.PD K).Fil a |>.restrictScalars ℚ_[l]).smul_mem (v i) hβ
    · intro y z hy hz
      simpa only [map_add, Pi.add_apply] using Submodule.add_mem _ hy hz
  refine ⟨fun i => ?_, fun hall => hc0 ?_⟩
  · simpa [hex] using hcoord _ x (hlow hxD) i
  · have hxF : x ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) :=
      Submodule.sum_mem _ fun i _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (hall i)
    have h0 : x ∈ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) :=
      ⟨hxD, hxF⟩
    rw [hhigh, Submodule.mem_bot] at h0
    rw [← hex, h0, map_zero]

end GlobalTheory.DRMat
