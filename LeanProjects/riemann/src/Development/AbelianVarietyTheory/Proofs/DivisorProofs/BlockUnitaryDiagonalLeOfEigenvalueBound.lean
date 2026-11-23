import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem re_inner_apply_le_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (R : ℝ)
    (hR : ∀ (x : ℝ) (v : E), v ≠ 0 → T v = (x : ℂ) • v → x ≤ R) (y : E) :
    (inner ℂ y (T y)).re ≤ R * (inner ℂ y y).re := by
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  set b := hT.eigenvectorBasis hn
  set ev := hT.eigenvalues hn
  have hb : ∀ i, T (b i) = ((ev i : ℝ) : ℂ) • b i := fun i => hT.apply_eigenvectorBasis hn i
  have hle : ∀ i, ev i ≤ R := fun i => hR _ _ (b.orthonormal.ne_zero i) (hb i)
  have h3 : ∀ i, inner ℂ y (b i) * inner ℂ (b i) y = ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm (b i) y, Complex.norm_conj]
    first
      | (rw [Complex.mul_conj']; push_cast; rfl)
      | (rw [mul_comm, Complex.conj_mul']; push_cast; rfl)
  have h1 : inner ℂ y (T y) = ∑ i, ((ev i * ‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y (T y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT (b i) y, hb i, inner_smul_left, Complex.conj_ofReal, mul_left_comm, h3 i]
    push_cast; ring
  have h2 : inner ℂ y y = ∑ i, ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y y]
    exact Finset.sum_congr rfl fun i _ => h3 i
  rw [h1, h2, Complex.re_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hle i) (by positivity)

section Block

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def blockSub (s : ι → Bool) (U : Submodule ℂ M) : Submodule ℂ (ι → M) where
  carrier := {y | ∀ c, y c ∈ U ∧ (s c = false → y c = 0)}
  add_mem' {x y} hx hy c := ⟨U.add_mem (hx c).1 (hy c).1, fun h => by simp [(hx c).2 h, (hy c).2 h]⟩
  zero_mem' c := ⟨U.zero_mem, fun _ => rfl⟩
  smul_mem' r x hx c := ⟨U.smul_mem r (hx c).1, fun h => by simp [(hx c).2 h]⟩

def blockOp (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) : blockSub s U →ₗ[ℂ] blockSub s U where
  toFun y := ⟨fun a => if s a = true then ∑ b, F a b (y.1 b) else 0, fun c => by
    refine ⟨?_, fun h => by simp [h]⟩
    show (if s c = true then ∑ b, F c b (y.1 b) else 0) ∈ U
    split_ifs with hc
    · refine U.sum_mem fun b _ => ?_
      by_cases hb : s b = true
      · exact hst c b (hc.trans hb.symm) _ (y.2 b).1
      · rw [(y.2 b).2 (by simpa using hb), map_zero]; exact U.zero_mem
    · exact U.zero_mem⟩
  map_add' y z := by
    ext a
    simp only [Submodule.coe_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
    split_ifs <;> simp
  map_smul' r y := by
    ext a
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
    split_ifs <;> simp [Finset.smul_sum]

theorem blockOp_apply (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) (y : blockSub s U) (a : ι) :
    (blockOp s F U hst y : ι → M) a = if s a = true then ∑ b, F a b (y.1 b) else 0 := rfl

def blockCore (s : ι → Bool) (U : Submodule ℂ M) (ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hsym : ∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) (hpos : ∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) :
    InnerProductSpace.Core ℂ (blockSub s U) where
  inner y z := ∑ c, ip (y.1 c) (z.1 c)
  conj_inner_symm y z := by
    simp only [map_sum, starRingEnd_apply]
    exact Finset.sum_congr rfl fun c _ => hsym _ (z.2 c).1 _ (y.2 c).1
  re_inner_nonneg y := by
    simp only [RCLike.re_to_complex, Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    by_cases h : y.1 c = 0
    · simp [h]
    · exact (hpos _ (y.2 c).1 h).le
  add_left y z w := by simp [Finset.sum_add_distrib]
  smul_left y z r := by simp [Finset.mul_sum]
  definite y h := by
    have h' : ∑ c, (ip (y.1 c) (y.1 c)).re = 0 := by rw [← Complex.re_sum, h]; rfl
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (ip (y.1 c) (y.1 c)).re := fun c _ => by
      by_cases h : y.1 c = 0
      · simp [h]
      · exact (hpos _ (y.2 c).1 h).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h'
    ext c
    by_contra hc
    exact (hpos _ (y.2 c).1 hc).ne' (hz c (Finset.mem_univ c))

end Block

theorem re_diag_le_of_eigen_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  intro ι M _ _ _ _ s F U R hU hR a ha u hu hu0 m hm
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := hU
  let cd := blockCore s U ip hsym hpos
  letI : NormedAddCommGroup (blockSub s U) := cd.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (blockSub s U) := InnerProductSpace.ofCore cd.toCore
  haveI : FiniteDimensional ℂ U := hfd
  haveI : FiniteDimensional ℂ (blockSub s U) := by
    let e : blockSub s U →ₗ[ℂ] (ι → U) :=
      { toFun := fun y c => ⟨y.1 c, (y.2 c).1⟩
        map_add' := fun y z => rfl
        map_smul' := fun r y => rfl }
    exact Module.Finite.of_injective e
      (fun y z h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hinner : ∀ y z : blockSub s U, inner ℂ y z = ∑ c, ip (y.1 c) (z.1 c) := fun _ _ => rfl
  have key : ∀ (y z : blockSub s U) (c b : ι),
      ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) =
        ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
    intro y z c b
    by_cases hc : s c = true
    · by_cases hb : s b = true
      · rw [if_pos hc, if_pos hb]
        exact hadj c b (hc.trans hb.symm) _ (y.2 b).1 _ (z.2 c).1
      · rw [if_pos hc, if_neg hb, (y.2 b).2 (by simpa using hb)]
        simp
    · rw [if_neg hc, (z.2 c).2 (by simpa using hc)]
      simp
  have hT : (blockOp s F U hst).IsSymmetric := by
    intro y z
    rw [hinner, hinner]
    simp only [blockOp_apply]
    have e1 : ∀ c, ip (if s c = true then ∑ b, F c b (y.1 b) else 0) (z.1 c) =
        ∑ b, ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) := by
      intro c; split_ifs <;> simp [map_sum]
    have e2 : ∀ b, ip (y.1 b) (if s b = true then ∑ c, F b c (z.1 c) else 0) =
        ∑ c, ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
      intro b; split_ifs <;> simp [map_sum]
    simp only [e1, e2, key]
    exact Finset.sum_comm
  have hR' : ∀ (x : ℝ) (v : blockSub s U), v ≠ 0 → blockOp s F U hst v = (x : ℂ) • v → x ≤ R := by
    intro x v hv hTv
    refine hR x v.1 (fun h => hv (Subtype.ext h)) (fun c => (v.2 c).1) (fun c => (v.2 c).2) fun c hc => ?_
    have := congrFun (congrArg Subtype.val hTv) c
    rw [blockOp_apply, if_pos hc] at this
    exact this
  have hmem : Pi.single a u ∈ blockSub s U := by
    intro c
    by_cases hc : c = a
    · subst hc; simp only [Pi.single_eq_same]; exact ⟨hu, fun h => by simp [ha] at h⟩
    · rw [Pi.single_eq_of_ne hc]; exact ⟨U.zero_mem, fun _ => rfl⟩
  set y0 : blockSub s U := ⟨Pi.single a u, hmem⟩
  have hy0 : (y0 : ι → M) = Pi.single a u := rfl
  have hTa : (blockOp s F U hst y0 : ι → M) a = m • u := by
    rw [blockOp_apply, if_pos ha, hy0, Finset.sum_eq_single a, Pi.single_eq_same, hm]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  have i1 : inner ℂ y0 (blockOp s F U hst y0) = m * ip u u := by
    rw [hinner, Finset.sum_eq_single a, hTa, hy0, Pi.single_eq_same, map_smul, smul_eq_mul]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have i2 : inner ℂ y0 y0 = ip u u := by
    rw [hinner, Finset.sum_eq_single a, hy0, Pi.single_eq_same]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have hle := re_inner_apply_le_of_eigen hT R hR' y0
  rw [i1, i2] at hle
  have him : (ip u u).im = 0 := by
    have h := hsym u hu u hu
    have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  have hp := hpos u hu hu0
  rw [Complex.mul_re, him, mul_zero, sub_zero] at hle
  exact le_of_mul_le_mul_right hle hp

end GlobalTheory.HoweR
