import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PartialSumRootEq

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Core

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type} [AddCommGroup MM] [Module ℂ MM]
  {S : Type*} [AddCommGroup S] [Module ℂ S]

theorem mem_eigenTensorSpace_iff {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {B : Module.End ℂ (Fin n → Y)}
    {P : Submodule ℂ Y} {t : ℝ} {f : Fin n → Y} :
    f ∈ Xs B P t ↔ (∀ c, f c ∈ P) ∧ B f = ((t : ℝ) : ℂ) • f := by
  simp only [Xs, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

theorem lowestKType_tensor_lift (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) (hanti : StrictAnti lam)
    (E : Fin n → Fin n → Module.End ℂ M) (P : Submodule ℂ M)
    (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM)
    (hEM : IsGlRep EM) (hlow : ∀ a b, b < a → EM a b φ = 0)
    (hwt : ∀ a, EM a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (hgen : genSub EM (Submodule.span ℂ {φ}) = ⊤)
    (T : S →ₗ[ℂ] (Fin n → M)) (θ : S →ₗ[ℂ] (Fin n → MM))
    (ES : Module.End ℂ S) (A : Fin n → Fin n → Module.End ℂ S) (hA : IsKRel ε A)
    (hTE : ∀ x, T (ES x) = eeV E (T x)) (hθE : ∀ x, θ (ES x) = eeV EM (θ x))
    (hAE : ∀ a b, ε a = ε b → Commute (A a b) ES)
    (hθA : ∀ a x, θ (A a a x) =
      tensV EM a a (θ x) + ((lowK ε lam a - (lam a + rho n a) : ℝ) : ℂ) • θ x)
    (hTR : ∀ W : Submodule ℂ S, IsKStableSub ε A W → (∀ x ∈ W, θ x = 0) → ∀ x ∈ W, T x = 0)
    (hlift : ∀ (μ : Fin n → ℝ) (f : Fin n → M), (∀ c, f c ∈ P) → IsKHWVec ε (tensV E) μ f →
      ∃ u, IsKHWVec ε A μ u ∧ T u = f) :
    (∀ (μ : Fin n → ℝ) (f : Fin n → M), f ∈ Xs (eeV E) P (thV lam s) → f ≠ 0 →
        IsKHWVec ε (tensV E) μ f → InRootCone (μ - lowK ε (lam + Pi.single s 1))) ∧
      ∀ f₁ f₂ : Fin n → M, f₁ ∈ Xs (eeV E) P (thV lam s) → f₂ ∈ Xs (eeV E) P (thV lam s) →
        IsKHWVec ε (tensV E) (lowK ε (lam + Pi.single s 1)) f₁ →
        IsKHWVec ε (tensV E) (lowK ε (lam + Pi.single s 1)) f₂ →
        ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0 := by
  set q := k2aQ lam s with hqdef
  set c := q.eval ((thV lam s : ℝ) : ℂ) with hcdef
  have hc : c ≠ 0 := aux_statement_18 lam s hanti
  have hVC := verma_cone n MM EM lam φ s hEM hlow hwt hgen hanti
  have hK1 := (verma_product_identity n MM EM lam φ hEM hlow hwt hgen).1
  have hAq : ∀ a b, ε a = ε b → Commute (A a b) (aeval ES q) := fun a b h => lagrangeFactor_eval_ne_zero (hAE a b h) q
  have hTq : ∀ u, eeV E (T u) = ((thV lam s : ℝ) : ℂ) • T u → T (aeval ES q u) = c • T u := by
    intro u hu
    rw [aeval_intertwine_alt T ES (eeV E) hTE, aeval_eigenvector hu]
  have hKq : ∀ (ν : Fin n → ℝ) (u : S), IsKHWVec ε A ν u → IsKHWVec ε A ν (aeval ES q u) := by
    intro ν u hu
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← Module.End.mul_apply, (hAq a a rfl).eq, Module.End.mul_apply, hu.1 a, map_smul]
    · rw [← Module.End.mul_apply, (hAq a b he).eq, Module.End.mul_apply, hu.2 a b hab he, map_zero]
  have hkey : ∀ (ν : Fin n → ℝ) (u : S), IsKHWVec ε A ν u → ∀ l, KirrLow ε l →
      θ (kirrWord A (aeval ES q u) l) ∈ Xs (eeV EM) ⊤ (thV lam s) ∧
      ∀ a, tensV EM a a (θ (kirrWord A (aeval ES q u) l)) =
        (((kirrWt ν l + (lam + rho n) - lowK ε lam) a : ℝ) : ℂ) • θ (kirrWord A (aeval ES q u) l) := by
    intro ν u hu l hl
    constructor
    · rw [mem_eigenTensorSpace_iff]
      refine ⟨fun _ => Submodule.mem_top, ?_⟩
      rw [commute_aeval_of_commute_alt hAq u l hl, aeval_intertwine_alt θ ES (eeV EM) hθE, ← sub_eq_zero]
      have := shifted_aeval_lagrange_eq_zero (eeV EM) lam s hK1 (θ (kirrWord A u l))
      simpa using this
    · intro a
      have hw := word_isWeightVector hA (hKq ν u hu).1 l hl a
      have h2 := hθA a (kirrWord A (aeval ES q u) l)
      rw [hw, map_smul] at h2
      rw [eq_sub_of_add_eq h2.symm, ← sub_smul]
      congr 1
      simp only [Pi.add_apply, Pi.sub_apply]
      push_cast
      ring
  refine ⟨?_, ?_⟩
  · intro μ f hf hf0 hμ
    obtain ⟨u, hu, rfl⟩ := hlift μ f (mem_eigenTensorSpace_iff.1 hf).1 hμ
    by_contra hcone
    apply hf0
    have hθW : ∀ x ∈ kirrSpan ε A (aeval ES q u), θ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hy
        obtain ⟨hmem, hw⟩ := hkey μ u hu l hl
        by_contra hne
        apply hcone
        have h1 := hVC.1.1 _ _ hmem hne hw
        have e : (kirrWt μ l + (lam + rho n) - lowK ε lam) - (lam + rho n + Pi.single s 1) =
            kirrWt μ l - lowK ε (lam + Pi.single s 1) := by
          unfold lowK; abel
        rw [e] at h1
        have h2 := root_swap_eq_neg h1 (weight_sub_mem_rootCone (ε := ε) μ l hl)
        convert h2 using 1
        abel
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    have hT0 := hTR _ (wordSpan_isKStable hA (hKq μ u hu)) hθW _
      (kirrWord_mem (A := A) (ε := ε) (l := []) _ (by simp [KirrLow]))
    simp only [kirrWord] at hT0
    rw [hTq u (mem_eigenTensorSpace_iff.1 hf).2] at hT0
    exact (smul_eq_zero.1 hT0).resolve_left hc
  · intro f₁ f₂ hf₁ hf₂ hk₁ hk₂
    obtain ⟨u₁, hu₁, rfl⟩ := hlift _ _ (mem_eigenTensorSpace_iff.1 hf₁).1 hk₁
    obtain ⟨u₂, hu₂, rfl⟩ := hlift _ _ (mem_eigenTensorSpace_iff.1 hf₂).1 hk₂
    set Λ' := lowK ε (lam + Pi.single s 1) with hΛ'
    have e0 : kirrWt Λ' [] + (lam + rho n) - lowK ε lam = lam + rho n + Pi.single s 1 := by
      simp only [kirrWt, hΛ']; unfold lowK; abel
    obtain ⟨hm₁, hw₁⟩ := hkey Λ' u₁ hu₁ [] (by simp [KirrLow])
    obtain ⟨hm₂, hw₂⟩ := hkey Λ' u₂ hu₂ [] (by simp [KirrLow])
    rw [e0] at hw₁ hw₂
    obtain ⟨c₁, c₂, hne, hsum⟩ := hVC.1.2 _ _ hm₁ hm₂ hw₁ hw₂
    refine ⟨c₁, c₂, hne, ?_⟩
    have hu : IsKHWVec ε A Λ' (c₁ • u₁ + c₂ • u₂) := by
      refine ⟨fun a => ?_, fun a b hab he => ?_⟩
      · rw [map_add, map_smul, map_smul, hu₁.1 a, hu₂.1 a, smul_add, smul_comm c₁, smul_comm c₂]
      · rw [map_add, map_smul, map_smul, hu₁.2 a b hab he, hu₂.2 a b hab he, smul_zero, smul_zero, add_zero]
    have hθW : ∀ x ∈ kirrSpan ε A (aeval ES q (c₁ • u₁ + c₂ • u₂)), θ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hy
        rcases l with _ | ⟨p, l'⟩
        · simp only [kirrWord] at hsum ⊢
          rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, hsum]
        · obtain ⟨hmem, hw⟩ := hkey Λ' _ hu (p :: l') hl
          by_contra hne0
          have h1 := hVC.1.1 _ _ hmem hne0 hw
          have e : (kirrWt Λ' (p :: l') + (lam + rho n) - lowK ε lam) - (lam + rho n + Pi.single s 1) =
              kirrWt Λ' (p :: l') - Λ' := by
            rw [hΛ']; unfold lowK; abel
          rw [e] at h1
          exact not_rootCone_of_ne Λ' (p :: l') hl (List.cons_ne_nil _ _) h1
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    have hT0 := hTR _ (wordSpan_isKStable hA (hKq Λ' _ hu)) hθW _
      (kirrWord_mem (A := A) (ε := ε) (l := []) _ (by simp [KirrLow]))
    simp only [kirrWord] at hT0
    have heig : eeV E (T (c₁ • u₁ + c₂ • u₂)) = ((thV lam s : ℝ) : ℂ) • T (c₁ • u₁ + c₂ • u₂) := by
      rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, (mem_eigenTensorSpace_iff.1 hf₁).2,
        (mem_eigenTensorSpace_iff.1 hf₂).2, smul_add, smul_comm c₁, smul_comm c₂]
    rw [hTq _ heig] at hT0
    have := (smul_eq_zero.1 hT0).resolve_left hc
    rw [map_add, map_smul, map_smul] at this
    exact this

end Core

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
