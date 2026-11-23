import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTwoNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PairVacLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem transport_right {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (v : Pl F)
    (k : UA σ W.J) (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) (θ : 𝓞 E)
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (φ₁ : (Fin n × Fin d → Fv F v) → ℂ)
    (hfix : ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ))
    (hact : Acts (evFin F v) (om (1, k)) φ φ₁) :
    ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ₁) := by
  intro γ hγ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hγ' : γ * (mat k⁻¹)ᵀ ∈ latAtV X W v :=
    GlobalTheory.VacTransport.mul_transpose_mem X W v _ (fun z hz => (hk.2 z hz).2) hγ
  have hback : actAB (cA σ) ((1 : UA σ X.J), k) (γ * (mat k⁻¹)ᵀ) = γ := by
    change (1 : Matrix _ _ _) * (γ * (mat k⁻¹)ᵀ) * (mat k)ᵀ = γ
    have e : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J)
    (mat k⁻¹) (k⁻¹).2 γ γ
  have h1 := hS.impl (1, k) (γ * (mat k⁻¹)ᵀ) _ hr'.2
  rw [hback, hfix _ hγ' r hr', hsy, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, GlobalTheory.VacTransport.tens_smul]

theorem line_of_good {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX : Chr F E} (v : Pl F) (hG : GlobalTheory.PairVac.GoodPlace B M χX v) (θ : 𝓞 E)
    (φ₀ : (Fin n × Fin d → Fv F v) → ℂ) (hφSB : φ₀ ∈ SB (Fin n × Fin d → Fv F v)) (hφ0 : φ₀ ≠ 0)
    (hφ : ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ₀))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hψSB : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hψ' : ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ)) :
    ∃ c : ℂ, φ = c • φ₀ := by
  set Λ := latAtV X W v with hΛ
  set co := M.co with hco
  have hAt : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  classical
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E))
        (incM F X.J) (incM F W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ Λ, Acts (evFin F v) (co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E))
          (incM F X.J) (incM F W.J) γ γ) • f)) →
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l := AddSubgroup.mem_map.mp hl
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    have key := GlobalTheory.LatVac.heis_at_local_identity v co B.ψ h.choose f _ (hAt _ h.choose_spec.1) (hA _ h.choose_spec.1) r hr x₀ hx₀ ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  have hfill : ∀ η : Fin n × Fin d → Fv F v,
      (∀ b : Fin n × Fin d → Fv F v, ((0 : Fin n × Fin d → Fv F v), b) ∈ Λ.map (GlobalTheory.LatVac.locCo co v) →
        GlobalTheory.LatVac.psiAt B.ψ v (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ.map (GlobalTheory.LatVac.locCo co v) := by
    intro η hη
    refine ⟨0, (hG.lat _).2 fun i => ⟨?_, by simpa using zero_mem (v.adicCompletionIntegers F)⟩⟩
    refine (hG.psi (η i)).1 fun y hy => ?_
    have hb : ((0 : Fin n × Fin d → Fv F v), Pi.single i y) ∈ Λ.map (GlobalTheory.LatVac.locCo co v) := by
      refine (hG.lat _).2 fun j => ⟨by simpa using zero_mem (v.adicCompletionIntegers F), ?_⟩
      by_cases hj : j = i
      · subst hj; simpa using hy
      · simpa [Pi.single_apply, hj] using zero_mem (v.adicCompletionIntegers F)
    have := hη _ hb
    rwa [dotProduct_single, GlobalTheory.LatVac.psiAt_apply] at this
  exact GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) χ φ₀ φ (loc φ₀ hφSB hφ)
    (loc φ hψSB hψ') hφ0 hfill

end GlobalTheory.PairVacLine

theorem GlobalTheory.PairVacLine.stab_vac_line : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ v, GlobalTheory.PairVac.GoodPlace B M χX v →
      ∀ g ∈ GlobalTheory.InertSph.KAt σ W v, ∃ c : ℂ, Acts (evFin F v) (om (1, g)) (M.vac v) (c • M.vac v) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v hG g hg
  obtain ⟨hSB, hne, θ, -, hfix⟩ := hP.good.vac v
  obtain ⟨φ₁, hφ₁SB, hact⟩ := GlobalTheory.ThK.LocalOps.acts_exists hP v (1, g)
    (GlobalTheory.InertSph.one_mem_KAt σ X v).1 hg.1 (M.vac v) hSB
  have hfix₁ := GlobalTheory.PairVacLine.transport_right hP v g hg θ (M.vac v) hSB φ₁ hfix hact
  obtain ⟨c, hc⟩ := GlobalTheory.PairVacLine.line_of_good v hG θ (M.vac v) hSB hne hfix φ₁ hφ₁SB hfix₁
  exact ⟨c, hc ▸ hact⟩

end
