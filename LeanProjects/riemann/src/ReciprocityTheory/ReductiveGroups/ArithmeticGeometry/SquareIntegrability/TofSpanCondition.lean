import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def uMap {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Vsp dim →ₗ[ℝ] Vsp dim :=
  (IR I).starProjection.toLinearMap ∘ₗ
    (((-Complex.I) • LinearMap.id : Vsp dim →ₗ[ℂ] Vsp dim).restrictScalars ℝ)

theorem tof_re_inner_negI {ι : Type} [Fintype ι] (a x : EuclideanSpace ℂ ι) :
    inner ℝ a ((-Complex.I) • x) = (Hf x a).im := by
  simp only [real_inner_eq_re_inner ℂ, PiLp.inner_apply, Hf, Complex.re_sum, Complex.im_sum,
    PiLp.smul_apply, smul_eq_mul, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.mul_im]

theorem isU_uMap {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) :
    IsU I x (uMap I x) := by
  refine ⟨(IR I).starProjection_apply_mem _, fun a ha => ?_⟩
  show inner ℝ ((IR I).starProjection ((-Complex.I) • x)) a = (Hf x a).im
  have h0 := Submodule.starProjection_inner_eq_zero (K := IR I) ((-Complex.I) • x) a ha
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [← h0, real_inner_comm]
  exact tof_re_inner_negI a x

theorem tof_act_add {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  ext i
  simp [act, mul_add]

theorem tof_act_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (c : ℂ) (v : Vsp dim) :
    act α (c • v) = c • act α v := by
  ext i
  simp [act]
  ring

theorem tof_natc_smul {dim : (E →+* ℂ) → ℕ} (n : ℕ) (z : Vsp dim) : (n : ℂ) • z = (n : ℝ) • z := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem tof_fg_div_eq_bot {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (M : Submodule ℤ Q) (hM : M.FG)
    (r : ℕ) (hr : 2 ≤ r) (hdiv : ∀ m ∈ M, ∃ m' ∈ M, m = r • m') : M = ⊥ := by
  obtain ⟨a, ha1, ha⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(r : ℤ)}) M hM (by
      intro m hm
      obtain ⟨m', hm', rfl⟩ := hdiv m hm
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm')
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton] at ha1
    have h1 : (r : ℤ) ∣ 1 := by simpa using ha1
    have h2 := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  rw [eq_bot_iff]
  intro m hm
  have h := ha m hm
  rw [← Int.cast_smul_eq_zsmul ℝ] at h
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast ha0)

theorem tof_span_condition [IsCMField E] {X : PT E} (I : Submodule ℤ (Vsp X.dim)) (r1 : ℕ) (hr1 : 2 ≤ r1)
    (a yb : Fin X.r → Vsp X.dim) (hyb : ∀ j, yb j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) :
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E,
      IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} = IR I := by
  have huniq : ∀ x w, IsU I x w → w = uMap I x := by
    rintro x w ⟨hw, hwa⟩
    have hu := isU_uMap I x
    have hd : w - uMap I x ∈ IR I := (IR I).sub_mem hw hu.1
    have horth : ∀ b ∈ IR I, inner ℝ (w - uMap I x) b = 0 := fun b hb => by
      rw [inner_sub_left, hwa b hb, hu.2 b hb, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero (𝕜 := ℝ).mp (horth _ hd))
  have hset : {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} =
      Set.range (fun p : Fin X.r × 𝓞 E =>
        uMap I (act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1))) := by
    ext w
    constructor
    · rintro ⟨j, α, h⟩
      exact ⟨(j, α), (huniq _ _ h).symm⟩
    · rintro ⟨⟨j, α⟩, rfl⟩
      exact ⟨j, α, isU_uMap I _⟩
  set T : Submodule ℝ (Vsp X.dim) := Submodule.span ℝ (Set.range fun p : Fin X.r × 𝓞 E =>
    act p.2 (((r1 : ℂ) ^ 2) • a p.1 - ((r1 : ℂ) ^ 2) • yb p.1)) with hT
  let f0 : Vsp X.dim →ₗ[ℝ] Vsp X.dim := LinearMap.id - (T.starProjection : Vsp X.dim →ₗ[ℝ] Vsp X.dim)
  have hf0T : ∀ v ∈ T, f0 v = 0 := fun v hv => by
    have h := Submodule.starProjection_mem_subspace_eq_self (K := T) ⟨v, hv⟩
    show v - T.starProjection v = 0
    rw [show ((⟨v, hv⟩ : T) : Vsp X.dim) = v from rfl] at h
    rw [h, sub_self]
  have hf0inv : ∀ v, f0 v = 0 → v ∈ T := fun v hv => by
    have h : v - T.starProjection v = 0 := hv
    rw [sub_eq_zero.mp h]
    exact T.starProjection_apply_mem v
  let f : Vsp X.dim →ₗ[ℤ] Vsp X.dim := f0.toAddMonoidHom.toIntLinearMap
  have hsq : ∀ z : Vsp X.dim, ((r1 : ℂ) ^ 2) • z = r1 • r1 • z := fun z => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul ℂ, sq, mul_smul]
  have hLfg : X.L.FG := Submodule.fg_span (Set.finite_range X.b)
  have hM := tof_fg_div_eq_bot (X.L.map f) (hLfg.map f) r1 hr1 (by
    rintro m ⟨x, hx, rfl⟩
    obtain ⟨c, y, hy, hxe⟩ := hgen x hx
    refine ⟨f (y + ∑ j, r1 • act (c j) (yb j)),
      ⟨_, X.L.add_mem hy (X.L.sum_mem fun j _ => nsmul_mem (X.stable _ _ (hyb j)) r1), rfl⟩, ?_⟩
    have e1 : ∀ j, act (c j) (((r1 : ℂ) ^ 2) • a j) =
        act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j) + r1 • r1 • act (c j) (yb j) := by
      intro j
      rw [← hsq, ← tof_act_smul, ← tof_act_add, sub_add_cancel]
    have hz : ∀ j, f (act (c j) (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) = 0 := fun j =>
      hf0T _ (Submodule.subset_span ⟨(j, c j), rfl⟩)
    rw [hxe]
    simp_rw [e1]
    rw [Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul ℂ]
    simp only [map_add, map_sum, map_nsmul, hz, Finset.sum_const_zero, zero_add, smul_add, Finset.smul_sum]
    abel)
  have hLT : ∀ x ∈ X.L, x ∈ T := fun x hx => hf0inv x (by
    have h : f x ∈ X.L.map f := ⟨x, hx, rfl⟩
    rw [hM] at h
    exact (Submodule.mem_bot ℤ).mp h)
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← X.b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hLT _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hset]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (isU_uMap I _).1
  · intro v hv
    have hv' : uMap I (Complex.I • v) = v := by
      show (IR I).starProjection ((-Complex.I) • Complex.I • v) = v
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      exact Submodule.starProjection_mem_subspace_eq_self (K := IR I) ⟨v, hv⟩
    rw [← hv']
    have hIv : Complex.I • v ∈ T := by rw [hTtop]; exact Submodule.mem_top
    have h2 : uMap I (Complex.I • v) ∈ T.map (uMap I) := ⟨_, hIv, rfl⟩
    rw [hT, Submodule.map_span, ← Set.range_comp] at h2
    exact h2

end

end ReciprocityTheory.ChartRestriction.G.I2
