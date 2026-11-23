import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialRootPredicateFactor
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticRootBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Polynomial Filter Topology Classical

namespace PolynomialRootPredicateFactor

noncomputable def fiberPoly {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) : ℂ[X] :=
  X ^ N + ∑ j, C (a j t) * X ^ (j : ℕ)

noncomputable def rootFactor (p : ℂ[X]) (Q : ℂ → Prop) : ℂ[X] :=
  ((p.roots.filter Q).map fun τ => X - C τ).prod

theorem fiberPoly_monic {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) : (fiberPoly a t).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem fiberPoly_natDegree {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) :
    (fiberPoly a t).natDegree = N := by
  unfold fiberPoly
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _), natDegree_X_pow]

theorem fiberPoly_eval {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ) :
    (fiberPoly a t).eval τ = τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) := by
  simp [fiberPoly, eval_finsetSum]

theorem fiberPoly_card_roots {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) :
    Multiset.card (fiberPoly a t).roots = N := by
  rw [splits_iff_card_roots.1 (IsAlgClosed.splits _), fiberPoly_natDegree]

theorem mem_roots_fiberPoly {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ) :
    τ ∈ (fiberPoly a t).roots ↔ τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0 := by
  rw [mem_roots (fiberPoly_monic a t).ne_zero, IsRoot.def, fiberPoly_eval]

theorem rootFactor_monic (p : ℂ[X]) (Q : ℂ → Prop) : (rootFactor p Q).Monic :=
  monic_multiset_prod_of_monic _ _ fun τ _ => monic_X_sub_C τ

theorem rootFactor_natDegree (p : ℂ[X]) (Q : ℂ → Prop) :
    (rootFactor p Q).natDegree = Multiset.card (p.roots.filter Q) :=
  natDegree_multiset_prod_X_sub_C_eq_card _

theorem rootFactor_eval_eq_zero (p : ℂ[X]) (Q : ℂ → Prop) (τ : ℂ) :
    (rootFactor p Q).eval τ = 0 ↔ τ ∈ p.roots ∧ Q τ := by
  have h := mem_roots (rootFactor_monic p Q).ne_zero (a := τ)
  rw [rootFactor, roots_multiset_prod_X_sub_C, Multiset.mem_filter] at h
  exact h.symm

theorem rootFactor_mul_not (p : ℂ[X]) (hp : p.Monic) (Q : ℂ → Prop) :
    rootFactor p Q * rootFactor p (fun τ => ¬ Q τ) = p := by
  have h : ((p.roots.filter Q).map fun τ => X - C τ).prod *
      ((p.roots.filter fun τ => ¬ Q τ).map fun τ => X - C τ).prod = p := by
    rw [← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp (splits_iff_card_roots.1 (IsAlgClosed.splits p))
  unfold rootFactor
  convert h

theorem norm_root_le {N : ℕ} (c : Fin N → ℂ) (τ : ℂ) (h : τ ^ N + ∑ j, c j * τ ^ (j : ℕ) = 0) :
    ‖τ‖ ≤ 1 + ∑ j, ‖c j‖ := by
  have hs : 0 ≤ ∑ j, ‖c j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  by_cases h1 : ‖τ‖ ≤ 1
  · linarith
  push Not at h1
  cases N with
  | zero => simp at h
  | succ n =>
    have key : ‖τ‖ ^ (n + 1) ≤ (∑ j, ‖c j‖) * ‖τ‖ ^ n := by
      have e : τ ^ (n + 1) = -∑ j, c j * τ ^ (j : ℕ) := eq_neg_of_add_eq_zero_left h
      rw [← norm_pow, e, norm_neg, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1.le (Nat.lt_succ_iff.1 j.2)) (norm_nonneg _)
    have hpos : 0 < ‖τ‖ ^ n := pow_pos (by linarith) n
    rw [pow_succ, mul_comm (∑ j, ‖c j‖)] at key
    have := le_of_mul_le_mul_left key hpos
    linarith

theorem norm_coeff_rootFactor_le {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (Q : ℂ → Prop)
    (k : ℕ) : ‖(rootFactor (fiberPoly a t) Q).coeff k‖ ≤ (1 + ∑ j, ‖a j t‖) ^ N * 2 ^ N := by
  have hR : 1 ≤ 1 + ∑ j, ‖a j t‖ := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hroots : ∀ z ∈ ((rootFactor (fiberPoly a t) Q).map (RingHom.id ℂ)).roots, ‖z‖ ≤ 1 + ∑ j, ‖a j t‖ := by
    intro z hz
    rw [Polynomial.map_id, rootFactor, roots_multiset_prod_X_sub_C, Multiset.mem_filter] at hz
    exact norm_root_le _ z ((mem_roots_fiberPoly a t z).1 hz.1)
  have h := coeff_le_of_roots_le k (rootFactor_monic _ Q) (IsAlgClosed.splits _) hroots
  rw [Polynomial.map_id] at h
  have hdeg : (rootFactor (fiberPoly a t) Q).natDegree ≤ N := by
    rw [rootFactor_natDegree]
    exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (fiberPoly_card_roots a t).le
  refine h.trans (mul_le_mul (pow_le_pow_right₀ hR (by omega)) ?_ (by positivity) (by positivity))
  exact_mod_cast (Nat.choose_le_two_pow _ k).trans (Nat.pow_le_pow_right two_pos hdeg)

theorem differentiableAt_coeff_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Multiset ℂ)
    (g : ℂ → E → ℂ) (x : E) (hg : ∀ τ, DifferentiableAt ℂ (g τ) x) :
    ∀ k : ℕ, DifferentiableAt ℂ (fun s => ((F.map fun τ => X - C (g τ s)).prod).coeff k) x := by
  induction F using Multiset.induction_on with
  | empty => intro k; simp
  | cons σ F ih =>
    intro k
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    cases k with
    | zero =>
      simp only [coeff_X_mul_zero, zero_sub]
      exact ((hg σ).mul (ih 0)).neg
    | succ n =>
      simp only [coeff_X_mul]
      exact (ih n).sub ((hg σ).mul (ih (n + 1)))

theorem exists_ne_zero_of_open {d : ℕ} {B : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hBc : Convex ℝ B)
    (hδ : AnalyticOnNhd ℂ δ B) {t₁ : Fin d → ℂ} (ht₁B : t₁ ∈ B) (ht₁ : δ t₁ ≠ 0) :
    ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ B → V.Nonempty → ∃ t ∈ V, δ t ≠ 0 := by
  intro V hVo hVB ⟨v, hv⟩
  by_contra hall
  push Not at hall
  have h0 : δ =ᶠ[𝓝 v] 0 := Filter.eventually_of_mem (hVo.mem_nhds hv) hall
  exact ht₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected (hVB hv) h0 ht₁B)

theorem local_filter_eq {d N : ℕ} {a : Fin N → (Fin d → ℂ) → ℂ} {Q : (Fin d → ℂ) → ℂ → Prop}
    {t₀ : Fin d → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) t₀) (hsep : (fiberPoly a t₀).Separable)
    (hbr : ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (Q s (r s) ↔ Q t₀ τ₀)) :
    ∃ ρ : ℂ → (Fin d → ℂ) → ℂ, (∀ τ, DifferentiableAt ℂ (ρ τ) t₀) ∧
      ∀ᶠ s in 𝓝 t₀, (fiberPoly a s).roots.filter (Q s) =
        ((fiberPoly a t₀).roots.filter (Q t₀)).map fun τ => ρ τ s := by
  set R₀ := (fiberPoly a t₀).roots with hR₀
  have hA : ∀ τ : ℂ, ∃ (O : Set (Fin d → ℂ)) (ρ : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧
      DifferentiableAt ℂ ρ t₀ ∧ (τ ∈ R₀ → ρ t₀ = τ ∧ ∀ s ∈ O, ρ s ∈ (fiberPoly a s).roots) := by
    intro τ
    by_cases hτ : τ ∈ R₀
    · obtain ⟨O, ρ, hO, ht, hρ, hρ0, hρr⟩ :=
        AnalyticRootBranch.proof d N a t₀ τ ha hsep ((mem_roots_fiberPoly a t₀ τ).1 hτ)
      exact ⟨O, ρ, hO, ht, (hρ t₀ ht).differentiableAt, fun _ =>
        ⟨hρ0, fun s hs => (mem_roots_fiberPoly a s _).2 (hρr s hs)⟩⟩
    · exact ⟨Set.univ, fun _ => τ, isOpen_univ, trivial, differentiableAt_const _, fun h => absurd h hτ⟩
  choose O ρ hO ht₀ hρd hρ using hA
  have hC : ∀ τ : ℂ, ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧
      (τ ∈ R₀ → ContinuousAt r t₀ ∧ r t₀ = τ ∧
        ∀ s ∈ O, r s ∈ (fiberPoly a s).roots ∧ (Q s (r s) ↔ Q t₀ τ)) := by
    intro τ
    by_cases hτ : τ ∈ R₀
    · obtain ⟨O, r, hO, ht, hr, hr0, hrr⟩ := hbr τ ((mem_roots_fiberPoly a t₀ τ).1 hτ)
      exact ⟨O, r, hO, ht, fun _ => ⟨hr.continuousAt (hO.mem_nhds ht), hr0, fun s hs =>
        ⟨(mem_roots_fiberPoly a s _).2 (hrr s hs).1, (hrr s hs).2⟩⟩⟩
    · exact ⟨Set.univ, fun _ => τ, isOpen_univ, trivial, fun h => absurd h hτ⟩
  choose O' r hO' ht₀' hr using hC
  have ev1 : ∀ᶠ s in 𝓝 t₀, ∀ τ ∈ R₀.toFinset, s ∈ O τ ∧ s ∈ O' τ :=
    (eventually_all_finset _).2 fun τ _ =>
      Filter.Eventually.and ((hO τ).mem_nhds (ht₀ τ)) ((hO' τ).mem_nhds (ht₀' τ))
  have ev2 : ∀ᶠ s in 𝓝 t₀, ∀ σ ∈ R₀.toFinset, ∀ τ ∈ R₀.toFinset,
      σ ≠ τ → ρ σ s ≠ ρ τ s ∧ r τ s ≠ ρ σ s := by
    refine (eventually_all_finset _).2 fun σ hσ => (eventually_all_finset _).2 fun τ hτ => ?_
    rw [Multiset.mem_toFinset] at hσ hτ
    by_cases hστ : σ = τ
    · exact Eventually.of_forall fun _ h => absurd hστ h
    have c1 : ContinuousAt (fun s => ρ σ s - ρ τ s) t₀ := (hρd σ).continuousAt.sub (hρd τ).continuousAt
    have c2 : ContinuousAt (fun s => r τ s - ρ σ s) t₀ := (hr τ hτ).1.sub (hρd σ).continuousAt
    have e1 : ρ σ t₀ - ρ τ t₀ ≠ 0 := by
      rw [(hρ σ hσ).1, (hρ τ hτ).1]; exact sub_ne_zero.2 hστ
    have e2 : r τ t₀ - ρ σ t₀ ≠ 0 := by
      rw [(hr τ hτ).2.1, (hρ σ hσ).1]; exact sub_ne_zero.2 (Ne.symm hστ)
    filter_upwards [c1.eventually_ne e1, c2.eventually_ne e2] with s h1 h2 _
    exact ⟨sub_ne_zero.1 h1, sub_ne_zero.1 h2⟩
  refine ⟨ρ, hρd, ?_⟩
  filter_upwards [ev1, ev2] with s h1 h2
  have h1' : ∀ τ ∈ R₀, s ∈ O τ ∧ s ∈ O' τ := fun τ hτ => h1 τ (Multiset.mem_toFinset.2 hτ)
  have h2' : ∀ σ ∈ R₀, ∀ τ ∈ R₀, σ ≠ τ → ρ σ s ≠ ρ τ s ∧ r τ s ≠ ρ σ s := fun σ hσ τ hτ =>
    h2 σ (Multiset.mem_toFinset.2 hσ) τ (Multiset.mem_toFinset.2 hτ)
  have hnd : R₀.Nodup := nodup_roots hsep
  have hMnd : (R₀.map fun τ => ρ τ s).Nodup := hnd.map_on fun σ hσ τ hτ h => by
    by_contra hne
    exact (h2' σ hσ τ hτ hne).1 h
  have hMsub : (R₀.map fun τ => ρ τ s) ⊆ (fiberPoly a s).roots := by
    intro x hx
    obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hx
    exact (hρ τ hτ).2 s (h1' τ hτ).1
  have hMeq : (R₀.map fun τ => ρ τ s) = (fiberPoly a s).roots := by
    refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hMnd).2 hMsub) ?_
    rw [Multiset.card_map, hR₀, fiberPoly_card_roots, fiberPoly_card_roots]
  rw [← hMeq, Multiset.filter_map]
  refine congrArg (Multiset.map _) (Multiset.filter_congr fun τ hτ => ?_)
  have hrs : r τ s ∈ (fiberPoly a s).roots := ((hr τ hτ).2.2 s (h1' τ hτ).2).1
  rw [← hMeq] at hrs
  obtain ⟨σ, hσ, hσe⟩ := Multiset.mem_map.1 hrs
  have hστ : σ = τ := by
    by_contra hne
    exact (h2' σ hσ τ hτ hne).2 hσe.symm
  rw [hστ] at hσe
  show Q s (ρ τ s) ↔ Q t₀ τ
  rw [hσe]
  exact ((hr τ hτ).2.2 s (h1' τ hτ).2).2

theorem extended_factor {d N : ℕ} {B : Set (Fin d → ℂ)} {a : Fin N → (Fin d → ℂ) → ℂ} {δ : (Fin d → ℂ) → ℂ}
    (Q : (Fin d → ℂ) → ℂ → Prop) (hBo : IsOpen B) (hBc : Convex ℝ B) (ha : ∀ j, AnalyticOnNhd ℂ (a j) B)
    (hδ : AnalyticOnNhd ℂ δ B) {t₁ : Fin d → ℂ} (ht₁B : t₁ ∈ B) (ht₁ : δ t₁ ≠ 0)
    (hsep : ∀ t ∈ B, δ t ≠ 0 → (fiberPoly a t).Separable)
    (hbr : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (Q s (r s) ↔ Q t₀ τ₀)) :
    ∃ (m : ℕ) (F : ℕ → (Fin d → ℂ) → ℂ), (∀ k, AnalyticOnNhd ℂ (F k) B) ∧
      ∀ t ∈ B, δ t ≠ 0 →
        rootFactor (fiberPoly a t) (Q t) = X ^ m + ∑ k ∈ Finset.range m, C (F k t) * X ^ k := by
  have hdense := exists_ne_zero_of_open hBc hδ ht₁B ht₁
  have hB'c : IsPreconnected (B ∩ {t | δ t ≠ 0}) :=
    ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero hBo hBc hδ
  have hloc : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∃ ρ : ℂ → (Fin d → ℂ) → ℂ, (∀ τ, DifferentiableAt ℂ (ρ τ) t₀) ∧
      ∀ᶠ s in 𝓝 t₀, (fiberPoly a s).roots.filter (Q s) =
        ((fiberPoly a t₀).roots.filter (Q t₀)).map fun τ => ρ τ s :=
    fun t₀ h₀ hδ₀ => local_filter_eq (fun j => ha j t₀ h₀) (hsep t₀ h₀ hδ₀) (hbr t₀ h₀ hδ₀)
  have hcount : ∀ t ∈ B, δ t ≠ 0 → Multiset.card ((fiberPoly a t).roots.filter (Q t)) =
      Multiset.card ((fiberPoly a t₁).roots.filter (Q t₁)) := by
    intro t ht hδt
    refine hB'c.constant (f := fun t => Multiset.card ((fiberPoly a t).roots.filter (Q t))) ?_
      ⟨ht, hδt⟩ ⟨ht₁B, ht₁⟩
    rintro s ⟨hs, hδs⟩
    obtain ⟨ρ, -, hev⟩ := hloc s hs hδs
    refine (Filter.EventuallyEq.continuousAt
      (y := Multiset.card ((fiberPoly a s).roots.filter (Q s))) ?_).continuousWithinAt
    filter_upwards [hev] with u hu
    rw [hu, Multiset.card_map]
  have hdiff : ∀ k, DifferentiableOn ℂ (fun t => (rootFactor (fiberPoly a t) (Q t)).coeff k)
      (B ∩ {t | δ t ≠ 0}) := by
    rintro k t ⟨ht, hδt⟩
    obtain ⟨ρ, hρ, hev⟩ := hloc t ht hδt
    refine (DifferentiableAt.congr_of_eventuallyEq
      (differentiableAt_coeff_prod ((fiberPoly a t).roots.filter (Q t)) ρ t hρ k) ?_).differentiableWithinAt
    filter_upwards [hev] with s hs
    simp only [rootFactor, hs, Multiset.map_map, Function.comp_def]
  have hbdd : ∀ k, ∀ τ ∈ B, ∃ V ∈ 𝓝 τ, Bornology.IsBounded
      ((fun t => (rootFactor (fiberPoly a t) (Q t)).coeff k) '' (V ∩ B ∩ {t | δ t ≠ 0})) := by
    intro k τ₀ hτ₀
    refine ⟨{t | ∀ j, ‖a j t‖ < ‖a j τ₀‖ + 1}, Filter.eventually_all.2 fun j =>
      ((ha j τ₀ hτ₀).continuousAt.norm).eventually (gt_mem_nhds (lt_add_one _)), ?_⟩
    refine isBounded_iff_forall_norm_le.2 ⟨(1 + ∑ j, (‖a j τ₀‖ + 1)) ^ N * 2 ^ N, ?_⟩
    rintro _ ⟨t, ⟨⟨htV, -⟩, -⟩, rfl⟩
    refine (norm_coeff_rootFactor_le a t (Q t) k).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity))
    gcongr with j
    exact (htV j).le
  have hext : ∀ k, ∃ Fk : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ Fk B ∧
      Set.EqOn Fk (fun t => (rootFactor (fiberPoly a t) (Q t)).coeff k) (B ∩ {t | δ t ≠ 0}) :=
    fun k => RiemannExtensionAnalytic.proof d B δ _ hBo hδ.differentiableOn hdense (hdiff k) (hbdd k)
  choose F hFd hFe using hext
  refine ⟨Multiset.card ((fiberPoly a t₁).roots.filter (Q t₁)), F,
    fun k => RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hBo (hFd k), ?_⟩
  intro t ht hδt
  have hdeg : (rootFactor (fiberPoly a t) (Q t)).natDegree =
      Multiset.card ((fiberPoly a t₁).roots.filter (Q t₁)) := by
    rw [rootFactor_natDegree, hcount t ht hδt]
  conv_lhs => rw [(rootFactor_monic (fiberPoly a t) (Q t)).as_sum, hdeg]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [hFe k ⟨ht, hδt⟩]

theorem eq_zero_of_dense {d : ℕ} {B : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hBo : IsOpen B)
    (hdense : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ B → V.Nonempty → ∃ t ∈ V, δ t ≠ 0)
    {g : (Fin d → ℂ) → ℂ} {t : Fin d → ℂ} (ht : t ∈ B) (hg : ContinuousAt g t)
    (hz : ∀ s ∈ B, δ s ≠ 0 → g s = 0) : g t = 0 := by
  by_contra h
  obtain ⟨W, hW, hWo, htW⟩ := mem_nhds_iff.1 (hg.eventually_ne h)
  obtain ⟨s, ⟨hsW, hsB⟩, hs⟩ := hdense (W ∩ B) (hWo.inter hBo) Set.inter_subset_right ⟨t, htW, ht⟩
  exact hW hsW (hz s hsB hs)

theorem analyticAt_monicEval {d m : ℕ} (F : ℕ → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (T : ℂ)
    (hF : ∀ k, AnalyticAt ℂ (F k) t) :
    AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => u.2 ^ m + ∑ k ∈ Finset.range m, F k u.1 * u.2 ^ k) (t, T) := by
  have h1 : ∀ k, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F k u.1 * u.2 ^ k) (t, T) := fun k =>
    ((hF k).comp_of_eq analyticAt_fst rfl).fun_mul (analyticAt_snd.fun_pow k)
  exact (analyticAt_snd.fun_pow m).fun_add (Finset.analyticAt_fun_sum _ fun k _ => h1 k)

end PolynomialRootPredicateFactor

open PolynomialRootPredicateFactor in

theorem PolynomialRootPredicateFactor.proof : PolynomialRootPredicateFactor.Statement := by
  intro d N B a δ P hBo hBc ha hδ ⟨t₁, ht₁B, ht₁⟩ hsep hbr
  have hdense := exists_ne_zero_of_open hBc hδ ht₁B ht₁
  obtain ⟨m, F, hF, hFe⟩ := extended_factor P hBo hBc ha hδ ht₁B ht₁ hsep hbr
  obtain ⟨n, G, hG, hGe⟩ := extended_factor (fun t τ => ¬ P t τ) hBo hBc ha hδ ht₁B ht₁ hsep
    fun t₀ h₀ hδ₀ τ₀ hτ₀ => by
      obtain ⟨O, r, h1, h2, h3, h4, h5⟩ := hbr t₀ h₀ hδ₀ τ₀ hτ₀
      exact ⟨O, r, h1, h2, h3, h4, fun s hs => ⟨(h5 s hs).1, not_congr (h5 s hs).2⟩⟩
  have hCe : ∀ t ∈ B, δ t ≠ 0 → ∀ T : ℂ,
      T ^ m + ∑ k ∈ Finset.range m, F k t * T ^ k = (rootFactor (fiberPoly a t) (P t)).eval T := by
    intro t ht hδt T
    rw [hFe t ht hδt]
    simp [eval_finsetSum]
  have hEe : ∀ t ∈ B, δ t ≠ 0 → ∀ T : ℂ, T ^ n + ∑ k ∈ Finset.range n, G k t * T ^ k =
      (rootFactor (fiberPoly a t) (fun τ => ¬ P t τ)).eval T := by
    intro t ht hδt T
    rw [hGe t ht hδt]
    simp [eval_finsetSum]
  refine ⟨fun t T => T ^ m + ∑ k ∈ Finset.range m, F k t * T ^ k,
    fun t T => T ^ n + ∑ k ∈ Finset.range n, G k t * T ^ k, fun t ht T =>
      ⟨analyticAt_monicEval F t T fun k => hF k t ht, analyticAt_monicEval G t T fun k => hG k t ht⟩, ?_, ?_⟩
  · intro t ht T
    beta_reduce
    have hpair : AnalyticAt ℂ (fun s : Fin d → ℂ => (s, T)) t := analyticAt_id.prod analyticAt_const
    have hCc : ContinuousAt (fun s => T ^ m + ∑ k ∈ Finset.range m, F k s * T ^ k) t :=
      ((analyticAt_monicEval F t T fun k => hF k t ht).comp_of_eq hpair rfl).continuousAt
    have hEc : ContinuousAt (fun s => T ^ n + ∑ k ∈ Finset.range n, G k s * T ^ k) t :=
      ((analyticAt_monicEval G t T fun k => hG k t ht).comp_of_eq hpair rfl).continuousAt
    have hpc : ContinuousAt (fun s => T ^ N + ∑ j, a j s * T ^ (j : ℕ)) t :=
      (analyticAt_const.fun_add (Finset.analyticAt_fun_sum _ fun j _ =>
          (ha j t ht).fun_mul analyticAt_const)).continuousAt
    have hcont : ContinuousAt (fun s => (T ^ m + ∑ k ∈ Finset.range m, F k s * T ^ k) *
        (T ^ n + ∑ k ∈ Finset.range n, G k s * T ^ k) - (T ^ N + ∑ j, a j s * T ^ (j : ℕ))) t :=
      (hCc.mul hEc).sub hpc
    refine sub_eq_zero.1 (eq_zero_of_dense hBo hdense ht hcont fun s hs hδs => ?_)
    rw [sub_eq_zero, hCe s hs hδs, hEe s hs hδs, ← eval_mul,
      rootFactor_mul_not _ (fiberPoly_monic a s), fiberPoly_eval]
  · intro t ht hδt τ hτ
    beta_reduce
    have hτr : τ ∈ (fiberPoly a t).roots := (mem_roots_fiberPoly a t τ).2 hτ
    rw [hCe t ht hδt, hEe t ht hδt, rootFactor_eval_eq_zero, rootFactor_eval_eq_zero]
    exact ⟨and_iff_right hτr, and_iff_right hτr⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
