import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

noncomputable section

namespace GlobalTheory.VacEigenLine

theorem eigen_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → ∀ (v : Pl F) (t : Matrix (Fin n) (Fin d) (AE F E) → ℂ),
    (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) (M.vac v) = t γ • M.vac v) →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) φ = t γ • φ) →
      ∃ a : ℂ, φ = a • M.vac v := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM v t hvac φ _ hφ
  classical
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l then t h.choose else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ,
      (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) f = t γ • f) →
      ∀ l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf l hl ξ
    have h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l := AddSubgroup.mem_map.mp hl
    have key := congrFun (hf _ h.choose_spec.1) ξ
    have e : locPt v (M.co.e h.choose) = l := h.choose_spec.2
    simp only [χ, dif_pos h]
    rw [e] at key
    simp only [locOp, Pi.smul_apply, smul_eq_mul] at key
    rw [GlobalTheory.LatVac.psiAt_apply, ← div_eq_inv_mul]
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ hAt
    (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hB hX hW v)
  have hfill := GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any F v _ (GlobalTheory.LatVac.psiAt B.ψ v)
    (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hB.std _) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ c hc0 hsd
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  exact GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) _ χ (M.vac v) φ (loc _ hvac) (loc φ hφ)
    (hM.vac v).2.1 hfill

end GlobalTheory.VacEigenLine

end
