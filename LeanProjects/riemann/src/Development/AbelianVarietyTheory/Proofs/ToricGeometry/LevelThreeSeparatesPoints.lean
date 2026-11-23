import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaSeparation

open Complex Matrix Filter Topology in
open scoped BigOperators Real in

theorem _root_.GlobalTheory.ThetaSeparation.dense_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (h0 : ∃ x, f x ≠ 0) :
    Dense {x | f x ≠ 0} := by
  by_contra hd
  obtain ⟨x₀, hx₀⟩ := h0
  rw [dense_iff_inter_open] at hd
  simp only [not_forall] at hd
  obtain ⟨U, hUo, hUne, hU⟩ := hd
  have hEq : Set.EqOn f (fun _ => (0 : ℂ)) Set.univ :=
    _root_.GlobalTheory.SCV.eqOn_of_eqOn_open (g := fun _ => (0 : ℂ)) isOpen_univ isPreconnected_univ
      hf.differentiableOn (differentiableOn_const 0) hUo hUne (Set.subset_univ _)
      (fun y hy => by
        by_contra hne
        exact hU ⟨y, hy, hne⟩)
  exact hx₀ (hEq (Set.mem_univ x₀))

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma eC_pow_eq_eC_natCast_mul (m : ℕ) (X : ℂ) : _root_.ReciprocityTheory.PTheta.eC X ^ m = _root_.ReciprocityTheory.PTheta.eC ((m : ℂ) * X) := by
  induction m with
  | zero => simp [_root_.ReciprocityTheory.PTheta.eC_zero]
  | succ m ih =>
    rw [pow_succ, ih, ← _root_.ReciprocityTheory.PTheta.eC_add]
    congr 1
    push_cast
    ring

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma exists_common_ne_zero_of_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f₁ f₂ : E → ℂ} (h₁ : Differentiable ℂ f₁)
    (h₂ : Differentiable ℂ f₂) (e₁ : ∃ x, f₁ x ≠ 0) (e₂ : ∃ x, f₂ x ≠ 0) :
    ∃ x, f₁ x ≠ 0 ∧ f₂ x ≠ 0 := by
  have d₁ := _root_.GlobalTheory.ThetaSeparation.dense_ne_zero h₁ e₁
  have d₂ := _root_.GlobalTheory.ThetaSeparation.dense_ne_zero h₂ e₂
  have o₁ : IsOpen {x | f₁ x ≠ 0} := isOpen_ne_fun h₁.continuous continuous_const
  obtain ⟨x, hx₁, hx₂⟩ := (d₁.inter_of_isOpen_left d₂ o₁).nonempty
  exact ⟨x, hx₁, hx₂⟩

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma exists_multiplier_of_level_sections_lemma {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    {t : (Fin g → ℂ) → ℂ} (ht : Differentiable ℂ t)
    (hq : ∀ (n n' : Fin g → ℤ) x, t (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') =
      _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ x)) * t x)
    (hne : ∃ x, t x ≠ 0) {N : ℕ} (hN : 3 ≤ N) {z z' : Fin g → ℂ} {γ : ℂ}
    (hf : ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) x,
      f (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') =
        _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ x)) * f x) →
      f z = γ * f z') :
    ∃ h : (Fin g → ℂ) → ℂ, Differentiable ℂ h ∧ (∀ x, h x ≠ 0) ∧
      ∀ x, t (x + (z - z')) = h x * t x := by
  have hk : ((N - 3 : ℕ) : ℂ) = (N : ℂ) - 3 := by
    rw [Nat.cast_sub hN]
    norm_num
  obtain ⟨x₀, hx₀⟩ := hne
  have shiftA : ∀ u, ∃ b, t (u + b) ≠ 0 := fun u => ⟨x₀ - u, by rwa [add_sub_cancel]⟩
  have shiftB : ∀ u v, ∃ b, t (u + -(v + b)) ≠ 0 := fun u v =>
    ⟨u - x₀ - v, by convert hx₀ using 2; abel⟩
  have hdA : ∀ u, Differentiable ℂ (fun b => t (u + b)) := fun u => by fun_prop
  have hdB : ∀ u v, Differentiable ℂ (fun b => t (u + -(v + b))) := fun u v => by fun_prop
  have hF : ∀ a b d, t (z + a) * t (z + b) * t (z + -(((N - 3 : ℕ) : ℂ) • d + a + b)) *
      t (z + d) ^ (N - 3) = γ * (t (z' + a) * t (z' + b) *
        t (z' + -(((N - 3 : ℕ) : ℂ) • d + a + b)) * t (z' + d) ^ (N - 3)) := by
    intro a b d
    refine hf (fun y => t (y + a) * t (y + b) * t (y + -(((N - 3 : ℕ) : ℂ) • d + a + b)) *
      t (y + d) ^ (N - 3)) ⟨by fun_prop, ?_⟩
    intro n n' y
    have key : ∀ s, t (y + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' + s) =
        _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + s))) *
          t (y + s) := by
      intro s
      rw [← hq n n' (y + s)]
      congr 1
      abel
    simp only [key, mul_pow, eC_pow_eq_eC_natCast_mul]
    have harg : -(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + a)) +
        -(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + b)) +
        -(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 +
          _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + -(((N - 3 : ℕ) : ℂ) • d + a + b))) +
        ((N - 3 : ℕ) : ℂ) * (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 +
          _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + d))) =
        -(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ y) := by
      simp only [dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
      rw [hk]
      ring
    rw [← harg, _root_.ReciprocityTheory.PTheta.eC_add, _root_.ReciprocityTheory.PTheta.eC_add, _root_.ReciprocityTheory.PTheta.eC_add]
    ring
  obtain ⟨d, hd₁, hd₂⟩ := exists_common_ne_zero_of_differentiable (hdA z) (hdA z') (shiftA z) (shiftA z')
  obtain ⟨a, ha⟩ := shiftA z
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_ne_zero_of_differentiable (hdA z)
    (hdB z (((N - 3 : ℕ) : ℂ) • d + a)) (shiftA z) (shiftB z _)
  have hγ : γ ≠ 0 := by
    intro h0
    have := hF a b d
    rw [h0, zero_mul] at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb₁) hb₂) (pow_ne_zero _ hd₁) this
  set Den : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun b x => t (z + b) *
    t (z + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)) * t (z + d) ^ (N - 3) with hDen
  set Num : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun b x => γ * (t (z' + b) *
    t (z' + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)) * t (z' + d) ^ (N - 3)) with hNum
  have hDenD : ∀ b, Differentiable ℂ (Den b) := by
    intro b
    simp only [hDen]
    fun_prop
  have hNumD : ∀ b, Differentiable ℂ (Num b) := by
    intro b
    simp only [hNum]
    fun_prop
  have hRel : ∀ b x, t (x + (z - z')) * Den b x = t x * Num b x := by
    intro b x
    have h := hF (x - z') b d
    have e₁ : z + (x - z') = x + (z - z') := by abel
    have e₂ : z' + (x - z') = x := by abel
    rw [e₁, e₂] at h
    simp only [hDen, hNum]
    linear_combination h
  have hChoice : ∀ x, ∃ b, Den b x ≠ 0 ∧ Num b x ≠ 0 := by
    intro x
    obtain ⟨b₁, h₁, h₁'⟩ := exists_common_ne_zero_of_differentiable (hdA z) (hdA z') (shiftA z) (shiftA z')
    obtain ⟨b₂, h₂, h₂'⟩ := exists_common_ne_zero_of_differentiable
      (hdB z (((N - 3 : ℕ) : ℂ) • d + (x - z'))) (hdB z' (((N - 3 : ℕ) : ℂ) • d + (x - z')))
      (shiftB z _) (shiftB z' _)
    obtain ⟨b, hb, hb'⟩ := exists_common_ne_zero_of_differentiable
      (f₁ := fun b => t (z + b) * t (z' + b))
      (f₂ := fun b => t (z + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)) *
        t (z' + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)))
      (by fun_prop) (by fun_prop) ⟨b₁, mul_ne_zero h₁ h₁'⟩ ⟨b₂, mul_ne_zero h₂ h₂'⟩
    obtain ⟨hb₁, hb₂⟩ := mul_ne_zero_iff.mp hb
    obtain ⟨hb₁', hb₂'⟩ := mul_ne_zero_iff.mp hb'
    refine ⟨b, ?_, ?_⟩
    · simp only [hDen]
      exact mul_ne_zero (mul_ne_zero hb₁ hb₁') (pow_ne_zero _ hd₁)
    · simp only [hNum]
      exact mul_ne_zero hγ (mul_ne_zero (mul_ne_zero hb₂ hb₂') (pow_ne_zero _ hd₂))
  choose B hB using hChoice
  have hdense := _root_.GlobalTheory.ThetaSeparation.dense_ne_zero ht ⟨x₀, hx₀⟩
  have cross : ∀ b b' x, Num b x * Den b' x = Num b' x * Den b x := by
    intro b b'
    have hfun : (fun x => Num b x * Den b' x) = (fun x => Num b' x * Den b x) :=
      Continuous.ext_on hdense (((hNumD b).mul (hDenD b')).continuous)
        (((hNumD b').mul (hDenD b)).continuous) (by
          intro x hx
          have hx' : t x ≠ 0 := hx
          have r₁ := hRel b x
          have r₂ := hRel b' x
          apply mul_left_cancel₀ hx'
          linear_combination Den b x * r₂ - Den b' x * r₁)
    intro x
    exact congrFun hfun x
  refine ⟨fun x => Num (B x) x / Den (B x) x, ?_, fun x => div_ne_zero (hB x).2 (hB x).1, ?_⟩
  · intro y
    have hev : (fun x => Num (B y) x / Den (B y) x) =ᶠ[𝓝 y]
        (fun x => Num (B x) x / Den (B x) x) := by
      filter_upwards [(hDenD (B y)).continuous.continuousAt.eventually_ne (hB y).1] with x hx
      rw [div_eq_div_iff hx (hB x).1]
      exact cross (B y) (B x) x
    have hquot : DifferentiableAt ℂ (fun x => Num (B y) x / Den (B y) x) y := by
      simp only [div_eq_mul_inv]
      exact (hNumD (B y) y).mul ((hDenD (B y) y).inv (hB y).1)
    exact hquot.congr_of_eventuallyEq hev.symm
  · intro x
    have r := hRel (B x) x
    show t (x + (z - z')) = Num (B x) x / Den (B x) x * t x
    rw [div_mul_eq_mul_div, eq_div_iff (hB x).1]
    linear_combination r

open Complex Matrix Filter Topology in
open scoped BigOperators Real in

theorem _root_.GlobalTheory.ThetaSeparation.level_three_separates_points :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) z) ∧ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, _root_.ReciprocityTheory.PTheta.theta 0 0 (z + w) τ = h z * _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) → w ∈ _root_.ReciprocityTheory.PTheta.periodLattice τ) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z z' : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * f z) → f z = γ * f z') → z - z' ∈ _root_.ReciprocityTheory.PTheta.periodLattice τ) := by
  intro hA hB g τ hτ N hN z z' γ hf
  obtain ⟨⟨htd, hq⟩, hne⟩ := hA g τ hτ
  have hne' : ∃ x, _root_.ReciprocityTheory.PTheta.theta 0 0 x τ ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
    exact ⟨x, hx⟩
  obtain ⟨h, hd, hnz, hrel⟩ :=
    exists_multiplier_of_level_sections_lemma (t := fun x => _root_.ReciprocityTheory.PTheta.theta 0 0 x τ) htd
      hq hne' hN hf
  exact hB g τ hτ (z - z') h hd hnz hrel

end GlobalTheory.ThetaSeparation
