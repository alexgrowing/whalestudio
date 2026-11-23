import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PSmooth

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

def Nr (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (h : V) (γ : Γ) : Prop :=
  ∃ hm : A γ⁻¹ h ∈ U, (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0}

theorem diffAt_of {U : Set V} (hU : IsOpen U) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {h : V} (hh : h ∈ U) : DifferentiableAt ℝ f h := by
  exact (hf.contDiffAt (hU.mem_nhds hh)).differentiableAt (by simp)

theorem psi_contDiffOn {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) (γ : Γ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (psi A φ γ) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => φ (A γ⁻¹ x)) U :=
    H.smooth.comp (A γ⁻¹).contDiff.contDiffOn (fun x hx => H.mapsTo γ⁻¹ x hx)
  exact h1

theorem nr_eventually {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) {γ : Γ} (hγ : ¬ Nr U A φ h γ) : psi A φ γ =ᶠ[𝓝 h] fun _ => 0 := by
  have hp : A γ⁻¹ h ∈ U := H.mapsTo _ h hh
  have hn : (⟨A γ⁻¹ h, hp⟩ : U) ∉ closure {x : U | φ x ≠ 0} := fun hc => hγ ⟨hp, hc⟩
  let g : U → U := fun x => ⟨A γ⁻¹ x, H.mapsTo _ x x.2⟩
  have hg : Continuous g :=
    ((A γ⁻¹).continuous.comp continuous_subtype_val).subtype_mk _
  have h1 : ∀ᶠ x in 𝓝 (⟨h, hh⟩ : U), g x ∈ (closure {x : U | φ x ≠ 0})ᶜ :=
    hg.continuousAt (isClosed_closure.isOpen_compl.mem_nhds hn)
  have h2 : ∀ᶠ x in 𝓝 (⟨h, hh⟩ : U), psi A φ γ x.1 = 0 := h1.mono fun x hx => by
    have h3 : g x ∉ {x : U | φ x ≠ 0} := fun h' => hx (subset_closure h')
    simp only [Set.mem_setOf_eq, not_not] at h3
    exact h3
  have h4 : ∀ᶠ x in Filter.map (fun x : U => (x : V)) (𝓝 (⟨h, hh⟩ : U)), psi A φ γ x = 0 := h2
  rw [map_nhds_subtype_val, H.isOpen.nhdsWithin_eq hh] at h4
  exact h4

theorem nr_fderiv {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) {γ : Γ} (hγ : ¬ Nr U A φ h γ) : fderiv ℝ (psi A φ γ) h = 0 := by
  rw [(nr_eventually H hh hγ).fderiv_eq]
  simp

theorem nr_mul {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} {O : Set Γ}
    (hOv : ∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
      (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O)
    {h : V} {γ γ' : Γ} (h1 : Nr U A φ h γ) (h2 : Nr U A φ h γ') : γ⁻¹ * γ' ∈ O := by
  obtain ⟨hm1, hc1⟩ := h1
  obtain ⟨hm2, hc2⟩ := h2
  have key : A (γ⁻¹ * γ')⁻¹ (A γ⁻¹ h) = A γ'⁻¹ h := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    rw [show (γ⁻¹ * γ')⁻¹ * γ⁻¹ = γ'⁻¹ by group]
  have hm : A (γ⁻¹ * γ')⁻¹ (A γ⁻¹ h) ∈ U := by rw [key]; exact hm2
  refine hOv (γ⁻¹ * γ') ⟨A γ⁻¹ h, hm1⟩ hc1 hm ?_
  convert hc2 using 1
  exact Subtype.ext key

theorem nr_exists {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) {h : V}
    (hh : h ∈ U) : ∃ γ, Nr U A φ h γ := by
  by_contra hne
  have hz : ∀ γ, φ (A γ⁻¹ h) = 0 := fun γ => by
    by_contra h0
    exact hne ⟨γ, H.mapsTo _ h hh, subset_closure h0⟩
  have hs := H.sum_one h hh
  simp only [hz, finsum_zero] at hs
  exact zero_ne_one hs

theorem c_bdd {O : Set Γ} (hO : O.Finite) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ τ : Fin (k + 2) → Γ, (∀ i, τ i ∈ O) → |c τ| ≤ C := by
  have hfin : (Set.pi Set.univ (fun _ : Fin (k + 2) => O)).Finite := Set.Finite.pi (fun _ => hO)
  obtain ⟨B, hB⟩ := (hfin.image (fun τ => |c τ|)).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun τ hτ => ?_⟩
  exact le_trans (hB ⟨τ, fun i _ => hτ i, rfl⟩) (le_max_left _ _)

theorem alt_smulRight_comp {n : ℕ} (f : V →L[ℝ] ℝ) (b : V [⋀^Fin n]→L[ℝ] ℝ) (T : V →L[ℝ] V) :
    (ContinuousAlternatingMap.alternatizeUncurryFin (f.smulRight b)).compContinuousLinearMap T =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((f.comp T).smulRight (b.compContinuousLinearMap T)) := by
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]
  rfl

theorem sum_compCLM {ι : Type} {n : ℕ} (s : Finset ι) (X : ι → V [⋀^Fin n]→L[ℝ] ℝ)
    (T : V →L[ℝ] V) :
    (∑ i ∈ s, X i).compContinuousLinearMap T = ∑ i ∈ s, (X i).compContinuousLinearMap T := by
  ext v
  simp [ContinuousAlternatingMap.sum_apply]

theorem nr_cons {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} {h : V} {γ : Γ} {σ : ℕ → Γ}
    (hγ : Nr U A φ h γ) (hσ : ∀ n, Nr U A φ h (σ n)) : ∀ n, Nr U A φ h (cons γ σ n) := by
  intro n
  cases n with
  | zero => exact hγ
  | succ n => exact hσ n

theorem claim {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (hL : PLoc U A φ)
    (hS : PSmooth U A φ) (hCl : PClosed U A φ) (H : Hyp U A φ) {O : Set Γ} (hO : O.Finite)
    (hOv : ∀ γ, ∀ h : U, h ∈ closure {x : U | φ x ≠ 0} → ∀ hm : A γ⁻¹ h ∈ U,
      (⟨A γ⁻¹ h, hm⟩ : U) ∈ closure {x : U | φ x ≠ 0} → γ ∈ O)
    {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ h ∈ U, ∀ (T : V →L[ℝ] V) (M : ℝ), 0 ≤ M →
      (∀ γ, ‖(fderiv ℝ (psi A φ γ) h).comp T‖ ≤ M) → ∀ σ : ℕ → Γ, (∀ n, Nr U A φ h (σ n)) →
      ‖(eta A φ c j σ h).compContinuousLinearMap T‖ ≤ C * M ^ j := by
  classical
  obtain ⟨C0, hC0, hC0b⟩ := c_bdd hO c
  induction j with
  | zero =>
    refine ⟨C0, hC0, fun h hh T M hM hT σ hσ => ?_⟩
    have e : (eta A φ c 0 σ h).compContinuousLinearMap T
        = ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i) := by
      rw [eta.eq_1]
      ext m
      simp
    rw [e, ContinuousAlternatingMap.norm_constOfIsEmpty, pow_zero, mul_one, Real.norm_eq_abs]
    rw [← hc.inv (σ 0)⁻¹ (fun i => σ i)]
    exact hC0b _ (fun i => nr_mul hOv (hσ 0) (hσ i))
  | succ j ih =>
    obtain ⟨Cj, hCj, hCjb⟩ := ih
    refine ⟨(hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * Cj),
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) hCj),
      fun h hh T M hM hT σ hσ => ?_⟩
    obtain ⟨s, W, hW, hWU, hs⟩ := hL H h hh
    have hloc : Kf A φ (eta A φ c j) σ =ᶠ[𝓝 h]
        fun x => ∑ γ ∈ s, psi A φ γ x • eta A φ c j (cons γ σ) x := by
      filter_upwards [hW] with x hx
      show ∑ᶠ γ, psi A φ γ x • eta A φ c j (cons γ σ) x = _
      apply finsum_eq_sum_of_support_subset
      intro γ hγ
      by_contra hγs
      exact (Function.mem_support.mp hγ) (by simp [hs γ hγs x hx])
    have hdψ : ∀ γ, DifferentiableAt ℝ (psi A φ γ) h :=
      fun γ => diffAt_of H.isOpen (psi_contDiffOn H γ) hh
    have hdη : ∀ γ, DifferentiableAt ℝ (eta A φ c j (cons γ σ)) h :=
      fun γ => diffAt_of H.isOpen (hS H k c j (cons γ σ)).1 hh
    have hder : fderiv ℝ (Kf A φ (eta A φ c j) σ) h = ∑ γ ∈ s,
        (psi A φ γ h • fderiv ℝ (eta A φ c j (cons γ σ)) h
          + (fderiv ℝ (psi A φ γ) h).smulRight (eta A φ c j (cons γ σ) h)) := by
      rw [hloc.fderiv_eq, fderiv_fun_sum (A := fun γ x => psi A φ γ x • eta A φ c j (cons γ σ) x)
        (fun γ _ => by exact (hdψ γ).smul (hdη γ))]
      refine Finset.sum_congr rfl fun γ _ => ?_
      exact fderiv_fun_smul (hdψ γ) (hdη γ)
    have heta : eta A φ c (j + 1) σ h = ∑ γ ∈ s, ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ (psi A φ γ) h).smulRight (eta A φ c j (cons γ σ) h)) := by
      rw [show eta A φ c (j + 1) σ = extDeriv (Kf A φ (eta A φ c j) σ) from eta.eq_2 A φ c σ j]
      show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (Kf A φ (eta A φ c j) σ) h) = _
      rw [hder, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_add, map_smul, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
        ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
      have hz : ContinuousAlternatingMap.alternatizeUncurryFin
          (fderiv ℝ (eta A φ c j (cons γ σ)) h) = 0 := hCl H k c j (cons γ σ) h hh
      rw [hz, smul_zero, zero_add]
    obtain ⟨γ0, hγ0⟩ := nr_exists H hh
    have hcard : (s.filter (Nr U A φ h)).card ≤ hO.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun γ => γ0⁻¹ * γ)
      · intro γ hγ
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_coe] at hγ
        simp only [Finset.coe_filter, Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Finset.mem_coe]
        exact nr_mul hOv hγ0 hγ.2
      · intro a _ b _ hab
        exact mul_left_cancel hab
    have hB : 0 ≤ ((j : ℝ) + 1) * (M * (Cj * M ^ j)) :=
      mul_nonneg (by positivity) (mul_nonneg hM (mul_nonneg hCj (pow_nonneg hM _)))
    have hterm : ∀ γ ∈ s, ‖ContinuousAlternatingMap.alternatizeUncurryFin
        (((fderiv ℝ (psi A φ γ) h).comp T).smulRight
          ((eta A φ c j (cons γ σ) h).compContinuousLinearMap T))‖
        ≤ if Nr U A φ h γ then ((j : ℝ) + 1) * (M * (Cj * M ^ j)) else 0 := by
      intro γ _
      split_ifs with hγ
      · refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans ?_
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hT γ) (hCjb h hh T M hM hT _ (nr_cons hγ hσ)) (norm_nonneg _) hM)
          (by positivity)
      · refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans (le_of_eq ?_)
        rw [ContinuousLinearMap.norm_smulRight_apply, nr_fderiv H hh hγ]
        simp
    rw [heta, sum_compCLM]
    simp only [alt_smulRight_comp]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    calc ((s.filter (Nr U A φ h)).card : ℝ) * (((j : ℝ) + 1) * (M * (Cj * M ^ j)))
        ≤ (hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * (M * (Cj * M ^ j))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
      _ = (hO.toFinset.card : ℝ) * (((j : ℝ) + 1) * Cj) * M ^ (j + 1) := by ring

theorem pBound (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (hL : PLoc U A φ)
    (hS : PSmooth U A φ) (hCl : PClosed U A φ) (hCoc : PCoc U A φ) (hD : PDep A φ) :
    PBound U A φ := by
  intro Hy O hO hOv _ k c hc
  obtain ⟨C, -, hC⟩ := claim hL hS hCl Hy hO hOv c hc (k + 1)
  refine ⟨C, fun h hh T M hM hT => ?_⟩
  obtain ⟨γ0, hγ0⟩ := nr_exists Hy hh
  have e1 : eta A φ c (k + 1) (fun _ => 1) = eta A φ c (k + 1) (skip 0 (cons γ0 fun _ => 1)) :=
    hD k c (k + 1) _ _ (fun n _ => by simp [skip, cons])
  have e2 : eta A φ c (k + 1) (skip 1 (cons γ0 fun _ => 1)) = eta A φ c (k + 1) (fun _ => γ0) :=
    hD k c (k + 1) _ _ (fun n hn => by
      have hn0 : n = 0 := by omega
      subst hn0
      simp [skip, cons])
  have e3 : eta A φ c (k + 1) (skip 0 (cons γ0 fun _ => 1)) h
      = eta A φ c (k + 1) (skip 1 (cons γ0 fun _ => 1)) h := by
    have e0 := hCoc Hy k c hc (k + 1) le_rfl (cons γ0 fun _ => 1) h hh
    apply sub_eq_zero.mp
    simpa [delG, Finset.sum_range_succ, sub_eq_add_neg] using e0
  rw [e1, e3, e2]
  exact hC h hh T M hM hT _ (fun _ => hγ0)

end PositivityTheory.KB.WhittakerCocycle

end
