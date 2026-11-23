import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftReductionToFockVectorsUniformStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem sum_support_comb {Y Z G : Type*} [AddCommMonoid G] [Module ℂ G] (n : ℕ) (a : Fin n → Y →₀ ℂ)
    (b : Fin n → Y → Z →₀ ℂ) (R : Z → G) :
    ∑ z ∈ (∑ i, ∑ y ∈ (a i).support, a i y • b i y).support, (∑ i, ∑ y ∈ (a i).support, a i y • b i y) z • R z =
      ∑ i, ∑ y ∈ (a i).support, a i y • ∑ z ∈ (b i y).support, b i y z • R z := by
  change Finsupp.sum _ (fun z r => r • R z) = _
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_smul_index' (by simp)]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem twoX_of_laws : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), BiAct D → CenFock D → LiftSum D → c.Is →
    (∀ s, (t s).Is) → RealEq t → KerX t → RdX t → TwoX t := by
  intro D c 𝒯 t hBi hCen hLS hc ht hreal hker hrd
  intro j hj C hC y
  have hj0 : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  obtain ⟨χ, hχ⟩ := hrd j (by omega)
  have step1 : ∃ (n : ℕ) (P : Fin n → PolF D (c.X (j + 1)).rank (c.X j).rank)
      (P' : Fin n → PolF D (c.X (j + 1 + 1)).rank (c.X (j + 1)).rank), ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ β,
        (t s).two j (fun α => (t s).rd j α ψ y) C β = ∑ i, ∑ γ,
          ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
    by_cases hex : ∃ (s : 𝒯) (_ : (t s).Ch j) (γ : (t s).Ch (j + 1)) (_ : (t s).Ch (j + 1 + 1)), True
    · obtain ⟨s₀, α₀, γ₀, β₀, -⟩ := hex
      obtain ⟨n, P, P', hF⟩ := GlobalTheory.T.doubleLift_reduction_to_fockVectors_uniform D hBi hCen hLS c.ψ c.θ hc.inf (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))
        (c.x j) (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x j (by omega)) (hc.x (j + 1) (by omega)) (hc.x (j + 1 + 1) (by omega))
        ((t s₀).ker j α₀ γ₀) ((t s₀).ker (j + 1) γ₀ β₀) ((ht s₀).ker j hj0 α₀ γ₀) ((ht s₀).ker (j + 1) hj1 γ₀ β₀) χ C hC.1 hC.2
      refine ⟨n, P, P', fun s ψ hψ β => ?_⟩
      have hrdψ := fun α => hχ s ψ hψ α y
      have e1 : ∀ α γ, biLift ((t s).kom j) ((t s).kom (j + 1)) (c.x j).vol (c.x (j + 1)).vol ((t s).rd j α ψ y)
          (biComb c.ψ _ _ _ ((t s).dd j α γ) ((t s).dd (j + 1) γ β) C) =
          ∑ i, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := fun α γ =>
        hF ((t s).ker j α γ) ((t s).ker (j + 1) γ β) ((ht s).ker j hj0 α γ) ((ht s).ker (j + 1) hj1 γ β) rfl rfl
          (fun a ha b hb f hf => hreal j hj0 s s₀ a ha b hb f hf)
          (fun a ha b hb f hf => hreal (j + 1) hj1 s s₀ a ha b hb f hf) _ (hrdψ α).1 (hrdψ α).2
      have e2 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
          ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
        intro i γ
        have h := (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
          ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 ((t s).Ch j) Finset.univ (fun _ => 1)
          (fun α => ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y))
          (fun α _ => (hLS c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
            ((ht s).ker j hj0 α γ) (P i)).2.1 _ (hrdψ α).1)
        simpa using h
      simp only [Tup.two, e1, e2]
      rw [Finset.sum_comm]
      calc _ = ∑ γ, ∑ i, ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) :=
            Finset.sum_congr rfl fun γ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    · push Not at hex
      refine ⟨0, Fin.elim0, Fin.elim0, fun s ψ _ β => ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun γ _ => ?_
      exact ((hex s α γ β).elim)
  obtain ⟨n, P, P', hstep⟩ := step1
  choose a ha using fun i : Fin n => hker j hj0 y (P i)
  choose b hb using fun (i : Fin n) (y' : c.Fr (j + 1)) => hker (j + 1) hj1 y' (P' i)
  obtain ⟨χ', hχ'⟩ := hrd (j + 1) (by omega)
  refine ⟨∑ i, ∑ y' ∈ (a i).support, a i y' • b i y', fun s ψ hψ β => ?_⟩
  rw [hstep s ψ hψ β, sum_support_comb]
  have hKψ := (ht s).stabK j hj0 ψ hψ
  have e3 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
        (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
      ∑ y' ∈ (a i).support, ((t s).cK j * a i y') • ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1))
        (P' i) ((t s).rd (j + 1) γ ((t s).K j ψ) y') := by
    intro i γ
    rw [ha i s ψ hψ γ, Finset.smul_sum]
    simp only [smul_smul]
    exact (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
      ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 _ _ _ _ (fun y' _ => (hχ' s _ hKψ γ y').1)
  simp only [e3]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.smul_sum, hb i y' s _ hKψ β, smul_smul, smul_smul]
  congr 1
  ring

end GlobalTheory.SeeSaw

end
