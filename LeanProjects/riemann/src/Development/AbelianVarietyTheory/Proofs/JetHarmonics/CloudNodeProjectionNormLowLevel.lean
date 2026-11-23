import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterLeSuccAndSqSumLePow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormEigenLePowMulNormSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasEigenvalueSummand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirResolventCircleBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevSubspaceMono
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumEigenprojectorLeOfResolventBound

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem cloud_node_projector_bound (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (n kk : ℕ) (bv : ℝ)
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : Fin n → H →ₗ[ℂ] H) (lam : Fin n → ℝ)
    (hfd : FiniteDimensional ℂ VV) (hb : 0 < bv)
    (hsum : ∀ x, ∑ i, p i x = x)
    (hp : ∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = (lam i : ℂ) • p i x)
    (hpos : ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ lam a ∧ lam a ≤ bv / 32) ∧
      (kk ≤ a.val + 1 → bv - bv / 32 ≤ lam a ∧ lam a ≤ 2 * bv + bv / 32))
    (hgap : ∀ a c : Fin n, a ≠ c → 1 ≤ |lam a - lam c|)
    (hcard : (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk)
    (hres : ∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → ∀ x ∈ VV, 13 * bv / 32 * ‖x‖ ≤ ‖ζ • x - T x‖)
    (hT : ∀ x ∈ VV, ‖T x‖ ≤ 3 * bv * ‖x‖) :
    ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ ∧
      ∀ s : Fin n, kk ≤ s.val + 1 → ‖p s x‖ ≤ 3 * (6 * bv) ^ (n - kk) * ‖x‖ := by
  have h1 : ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ := by
    intro x hx
    have hnorm : ∀ i, ‖(lam i : ℂ) - (-((bv / 16 : ℝ) : ℂ))‖ = |lam i + bv / 16| := by
      intro i
      rw [sub_neg_eq_add, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    have := GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound H (Fin n) VV T p (fun i => (lam i : ℂ)) (univ.filter (fun a : Fin n => a.val + 1 < kk))
      (-((bv / 16 : ℝ) : ℂ)) (9 * bv / 16) (32 / (13 * bv)) hfd (by positivity) (by positivity)
      (fun x _ => hsum x) hp ?_ ?_ ?_ x hx
    · have e : 9 * bv / 16 * (32 / (13 * bv)) = 18 / 13 := by field_simp; norm_num
      rwa [e] at this
    · intro i hi
      have := (hpos i).1 (mem_filter.1 hi).2
      rw [hnorm, abs_lt]
      constructor <;> linarith [this.1, this.2]
    · intro i hi
      have hi' : kk ≤ i.val + 1 := by
        by_contra h
        exact hi (mem_filter.2 ⟨mem_univ _, not_le.1 h⟩)
      have := (hpos i).2 hi'
      rw [hnorm, lt_abs]
      left
      linarith [this.1, this.2]
    · intro ζ hζ y hy
      rw [sub_neg_eq_add] at hζ
      have h := hres ζ hζ y hy
      have e : ‖y‖ = 32 / (13 * bv) * (13 * bv / 32 * ‖y‖) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
  intro x hx
  refine ⟨h1 x hx, fun s hs => ?_⟩
  have hsN : s ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1) := mem_filter.2 ⟨mem_univ _, hs⟩
  have := GlobalTheory.norm_node_projector_le H (Fin n) VV T p (fun i => (lam i : ℂ))
    (univ.filter (fun a : Fin n => kk ≤ a.val + 1)) s (6 * bv) 3 hsN (by positivity) hp ?_ ?_ ?_ ?_ x hx
  · rw [card_erase_of_mem hsN, hcard] at this
    have e : n + 1 - kk - 1 = n - kk := by omega
    rwa [e] at this
  · intro y hy
    rw [← hsum y, map_sum]
    exact VV.sum_mem fun i _ => by rw [(hp i y hy).2]; exact VV.smul_mem _ (hp i y hy).1
  · intro i hi
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap s i (ne_of_mem_erase hi).symm
  · intro i hi y hy
    have hi' := (hpos i).2 (mem_filter.1 (mem_of_mem_erase hi)).2
    have h2 : |lam i| ≤ 3 * bv := by
      rw [abs_le]; constructor <;> linarith [hi'.1, hi'.2]
    calc ‖T y - (lam i : ℂ) • y‖ ≤ ‖T y‖ + ‖(lam i : ℂ) • y‖ := norm_sub_le _ _
      _ ≤ 3 * bv * ‖y‖ + 3 * bv * ‖y‖ := by
          refine add_le_add (hT y hy) ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = 6 * bv * ‖y‖ := by ring
  · intro y hy
    have h3 := sum_filter_add_sum_filter_not univ (fun a : Fin n => a.val + 1 < kk) (fun i => p i y)
    rw [hsum y] at h3
    simp only [not_lt] at h3
    have h4 : ∑ i ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1), p i y =
        y - ∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h3
    rw [h4]
    have := h1 y hy
    have h5 := norm_sub_le y (∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y)
    linarith [norm_nonneg y]

theorem cloud_node_projection_norm : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hM hF hA hS hj hw c
  obtain ⟨hb, -, hpos⟩ := GlobalTheory.shape_position n kk j ε μ bv hS (by omega)
  obtain ⟨L0, Ladd, Lsmul, -⟩ := GlobalTheory.lev_subspace_mono M n ε E μ hM.1 hM.2.1
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hM.2.1 (fun s => (hF s).2.1) hA hw
  have heig := GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hM hF hA
  have hnb : (n : ℝ) ≤ bv := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by have := hS.2.1; omega : 1 ≤ n)
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ h1 (by norm_num)
    have h3 := hS.2.2.2.2.2
    have h4 : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    linarith
  have hcard := (GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv hS.1 hS.2.1 hnb).1
  let e : PiLp 2 (fun _ : Fin n => M) ≃ₗ[ℂ] (Fin n → M) := WithLp.linearEquiv 2 ℂ (Fin n → M)
  have hn : ∀ x : PiLp 2 (fun _ : Fin n => M), ‖x‖ ^ 2 = ∑ d, ‖e x d‖ ^ 2 := fun x => PiLp.norm_sq_eq_of_L2 _ x
  let T0 : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
    LinearMap.pi fun b => -∑ a, (E b a) ∘ₗ (LinearMap.proj a : (Fin n → M) →ₗ[ℂ] M)
  have hT0 : ∀ x, T0 x = splitCas E x := by
    intro x
    funext b
    simp [T0, splitCas]
  let T : PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := e.symm.toLinearMap ∘ₗ T0 ∘ₗ e.toLinearMap
  have hT : ∀ x, e (T x) = splitCas E (e x) := by
    intro x
    rw [← hT0]
    exact e.apply_symm_apply _
  let p : Fin n → PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := fun s =>
    e.symm.toLinearMap ∘ₗ io s ∘ₗ pr s ∘ₗ e.toLinearMap
  have hp : ∀ s x, e (p s x) = io s (pr s (e x)) := fun s x => e.apply_symm_apply _
  let x₀ : PiLp 2 (fun _ : Fin n => M) := e.symm (Pi.single c w)
  have hx₀ : e x₀ = Pi.single c w := e.apply_symm_apply _
  have hx₀n : ‖x₀‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [hn, hx₀, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [hd]
    · simp
  let VV : Submodule ℂ (PiLp 2 (fun _ : Fin n => M)) := Submodule.span ℂ (Set.range fun s => p s x₀)
  have hfd : FiniteDimensional ℂ VV := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hsum : ∀ x, ∑ i, p i x = x := by
    intro x
    apply e.injective
    rw [map_sum]
    simp only [hp]
    exact hA.sum_io_pr _
  have hx₀V : x₀ ∈ VV := by
    rw [← hsum x₀]
    exact VV.sum_mem fun i _ => Submodule.subset_span ⟨i, rfl⟩
  have hpV : ∀ i, ∀ x ∈ VV, p i x ∈ VV := by
    intro i x hx
    have : VV ≤ VV.comap (p i) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      show p i (p s x₀) ∈ VV
      by_cases h : i = s
      · subst h
        have : p i (p i x₀) = p i x₀ := by
          apply e.injective
          rw [hp, hp, hA.pr_io]
        rw [this]
        exact Submodule.subset_span ⟨i, rfl⟩
      · have : p i (p s x₀) = 0 := by
          apply e.injective
          rw [hp, hp, hA.pr_io_ne i s h, map_zero, map_zero]
        rw [this]
        exact VV.zero_mem
    exact this hx
  have hlev : ∀ x ∈ VV, ∀ d, Lev ε E μ (j + 2) (e x d) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      intro d
      rw [hp, hx₀]
      exact hcomp s c d
    | zero => intro d; rw [map_zero]; exact L0 _
    | add x y _ _ hx hy => intro d; rw [map_add]; exact Ladd _ _ _ (hx d) (hy d)
    | smul a x _ hx => intro d; rw [map_smul]; exact Lsmul _ _ _ (hx d)
  have hres := fun x (hx : x ∈ VV) =>
    GlobalTheory.T.splitCasimir_resolvent_circle_bounds M n ε E μ kk (j + 2) bv (e x) hM hS (by omega) (hlev x hx)
  have key := cloud_node_projector_bound (PiLp 2 (fun _ : Fin n => M)) n kk bv VV T p
    (fun s => -μ s + (1 - (n : ℝ)) / 2) hfd hb hsum ?_ hpos ?_ hcard ?_ ?_ x₀ hx₀V
  · refine ⟨?_, fun s hs => ?_⟩
    · have h := pow_le_pow_left₀ (norm_nonneg _) key.1 2
      rw [mul_pow, hx₀n, hn, map_sum] at h
      simp only [hp, hx₀] at h
      exact h
    · have h := pow_le_pow_left₀ (norm_nonneg _) (key.2 s hs) 2
      rw [mul_pow, hx₀n, hn, hp, hx₀] at h
      exact h
  · intro i x hx
    refine ⟨hpV i x hx, ?_⟩
    apply e.injective
    rw [hT, map_smul, hp, heig]
  · intro a b hab
    rw [le_abs]
    rcases lt_or_gt_of_ne hab with h | h
    · right
      have := hS.2.2.1 a b h
      linarith
    · left
      have := hS.2.2.1 b a h
      linarith
  · intro ζ hζ x hx
    have h := (hres x hx).1 ζ hζ
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, map_sub, map_smul, hT]
    exact h
  · intro x hx
    have h := (hres x hx).2
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, hT]
    exact h

end GlobalTheory
