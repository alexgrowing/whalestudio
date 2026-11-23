import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Grp

open MeasureTheory Matrix
open scoped Pointwise ENNReal

theorem exists_ginv {F V V' : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] (T : V →ₗ[F] V') :
    ∃ s : V' →ₗ[F] V, ∀ v, T (s (T v)) = T v := by
  obtain ⟨r, hr⟩ := T.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict T)
  obtain ⟨s, hs⟩ := r.exists_extend
  refine ⟨s, fun v => ?_⟩
  have h1 := LinearMap.congr_fun hs (T.rangeRestrict v)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hr (T.rangeRestrict v))
  change s (T v) = _ at h1
  rw [h1]
  exact h2

theorem ker_cocompact {F A V V' M M' : Type} [Field F] [CommRing A] [Algebra F A] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    [AddCommGroup M'] [Module A M'] [Module F M'] [IsScalarTower F A M'] [TopologicalSpace A] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul A M] {K : Set A} (hK : IsCompact K) (hc : ∀ a : A, ∃ x : F, a - algebraMap F A x ∈ K)
    {i : V →ₗ[F] M} {i' : V' →ₗ[F] M'} (hb : IsBaseChange A i) (hb' : IsBaseChange A i') (T : V →ₗ[F] V') (TA : M →ₗ[A] M')
    (h : ∀ v, TA (i v) = i' (T v)) :
    ∃ C : Set M, IsCompact C ∧ (∀ x ∈ C, TA x = 0) ∧ ∀ x, TA x = 0 → ∃ v, T v = 0 ∧ x - i v ∈ C := by
  obtain ⟨s, hs⟩ := exists_ginv T
  let b := Module.finBasis F (LinearMap.ker T)
  let w : Fin _ → M := fun j => i (b j)
  have key : ∀ x, x - hb'.lift (i ∘ₗ s) (TA x) ∈ Submodule.span A (Set.range w) := fun x => by
    induction x using hb.inductionOn with
    | zero => simp
    | tmul v =>
      rw [h, hb'.lift_eq, LinearMap.comp_apply, ← map_sub]
      have hv : v - s (T v) ∈ LinearMap.ker T := by simp [hs]
      rw [show v - s (T v) = ((⟨_, hv⟩ : LinearMap.ker T) : V) from rfl, ← b.sum_repr ⟨_, hv⟩]
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    | smul a x hx =>
      rw [map_smul, map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hx
    | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
  refine ⟨(fun a : Fin _ → A => ∑ j, a j • w j) '' Set.univ.pi fun _ => K,
    (isCompact_univ_pi fun _ => hK).image (by fun_prop), ?_, fun x hx => ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    simp only [map_sum, map_smul, w, h, show ∀ j, T (b j) = 0 from fun j => (b j).2, map_zero, smul_zero, Finset.sum_const_zero]
  · have := key x
    rw [hx, map_zero, sub_zero] at this
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 this
    choose r hr using fun j => hc (a j)
    refine ⟨∑ j, r j • (b j : V), by simp [show ∀ j, T (b j) = 0 from fun j => (b j).2], _, fun j _ => hr j, ?_⟩
    simp only [map_sum, map_smul, sub_smul, algebraMap_smul, Finset.sum_sub_distrib, w]

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ : Subgroup G} [Countable Γ]

theorem fd_fin {C : Set G} (hC : IsCompact C) [T2Space G] (hc : ∀ u, ∃ γ ∈ Γ, γ * u ∈ C) (μ : Measure G) [μ.IsHaarMeasure]
    {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  have hm := hC.measurableSet
  calc μ 𝓕 ≤ μ (⋃ γ : Γ, γ • C ∩ 𝓕) := measure_mono fun u hu => by
        obtain ⟨γ, h1, h2⟩ := hc u
        exact Set.mem_iUnion.2 ⟨⟨γ, h1⟩⁻¹, Set.mem_smul_set_iff_inv_smul_mem.2 (by simpa using h2), hu⟩
    _ ≤ ∑' γ : Γ, μ (γ • C ∩ 𝓕) := measure_iUnion_le _
    _ = μ C := (h.measure_eq_tsum C).symm
    _ < ⊤ := hC.measure_lt_top

theorem right_of_fd [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G}
    (hm : MeasurableSet 𝓕) (h : IsFundamentalDomain Γ 𝓕 μ) (hf : μ 𝓕 < ⊤) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  set c := Measure.haarScalarFactor (μ.map (· * g)) μ
  have q : Measure.QuasiMeasurePreserving (· * g) μ μ :=
    ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
  have h2 : IsFundamentalDomain Γ ((Equiv.mulRight g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv q Function.bijective_id fun γ x => by
      change _ * x * g = _ * (x * g)
      rw [mul_assoc]; rfl
  have h3 : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := h2.measure_eq h
  rw [← Measure.map_apply (measurable_mul_const g) hm, e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
  have h4 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hf.ne).1 (h3.trans (one_mul _).symm)
  rw [e, ENNReal.coe_eq_one.1 h4, one_smul]

end Lat

section Nil

variable {A R n : Type} [CommRing A] [Invertible (2 : A)] [CommRing R] [Algebra A R] [Fintype n] [DecidableEq n]
  {c : R →ₐ[A] R} {J e f : Matrix n n R}

structure Tri (e f x : Matrix n n R) : Prop where
  h1 : x * e = 0
  h2 : e * (x * f) = x * f
  h3 : f * x = x

def ex (A : Type) [CommRing A] [Invertible (2 : A)] [Algebra A R] (x : Matrix n n R) : Matrix n n R := 1 + x + (⅟2 : A) • (x * x)

theorem Tri.mf {x y : Matrix n n R} (hx : Tri e f x) (hy : Tri e f y) : x * y * f = 0 := by
  rw [Matrix.mul_assoc, ← hy.h2, ← Matrix.mul_assoc, hx.h1, Matrix.zero_mul]

theorem Tri.three {x y z : Matrix n n R} (hx : Tri e f x) (hy : Tri e f y) (hz : Tri e f z) : x * y * z = 0 := by
  rw [← hz.h3, ← Matrix.mul_assoc, hx.mf hy, Matrix.zero_mul]

theorem Tri.mul {x y : Matrix n n R} (hx : Tri e f x) (hy : Tri e f y) : Tri e f (x * y) :=
  ⟨by rw [Matrix.mul_assoc, hy.h1, Matrix.mul_zero], by rw [hx.mf hy, Matrix.mul_zero], by rw [← Matrix.mul_assoc, hx.h3]⟩

theorem Tri.add {x y : Matrix n n R} (hx : Tri e f x) (hy : Tri e f y) : Tri e f (x + y) :=
  ⟨by rw [Matrix.add_mul, hx.h1, hy.h1, add_zero], by rw [Matrix.add_mul, Matrix.mul_add, hx.h2, hy.h2],
    by rw [Matrix.mul_add, hx.h3, hy.h3]⟩

theorem Tri.smul {x : Matrix n n R} (hx : Tri e f x) (a : A) : Tri e f (a • x) :=
  ⟨by rw [Matrix.smul_mul, hx.h1, smul_zero], by rw [Matrix.smul_mul, Matrix.mul_smul, hx.h2], by rw [Matrix.mul_smul, hx.h3]⟩

theorem Tri.neg {x : Matrix n n R} (hx : Tri e f x) : Tri e f (-x) :=
  ⟨by rw [Matrix.neg_mul, hx.h1, neg_zero], by rw [Matrix.neg_mul, Matrix.mul_neg, hx.h2], by rw [Matrix.mul_neg, hx.h3]⟩

theorem Tri.ex {x : Matrix n n R} (hx : Tri e f x) : Tri e f (ex A x - 1) := by
  rw [Grp.ex, add_assoc, add_sub_cancel_left]
  exact hx.add ((hx.mul hx).smul _)

theorem half (y : Matrix n n R) : (⅟2 : A) • y + (⅟2 : A) • y = y := by rw [← add_smul, invOf_two_add_invOf_two, one_smul]

theorem ex_neg {x : Matrix n n R} (h : x * x * x = 0) : ex A x * ex A (-x) = 1 := by
  have h' : x * (x * x) = 0 := by rw [← Matrix.mul_assoc, h]
  have h'' : x * x * (x * x) = 0 := by rw [← Matrix.mul_assoc, h, Matrix.zero_mul]
  simp only [ex, Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, h, h', h'', smul_zero]
  nth_rw 2 [← half (A := A) (x * x)]
  abel

theorem map_ex (x : Matrix n n R) : (ex A x).map c = ex A (x.map c) := by
  have := (c.mapMatrix (m := n))
  change c.mapMatrix (ex A x) = ex A (c.mapMatrix x)
  simp only [ex, map_add, map_one, map_smul, map_mul]

theorem ex_unit {x : Matrix n n R} (h : x * x * x = 0) (hs : xᵀ * J + J * x.map c = 0) : (ex A x)ᵀ * J * (ex A x).map c = J := by
  have h1 : xᵀ * J = J * (-x.map c) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hs
  have h2 : (ex A x)ᵀ * J = J * ex A (-x.map c) := by
    simp only [ex, transpose_add, transpose_one, transpose_smul, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h3 : (-x.map c) * (-x.map c) * (-x.map c) = 0 := by
    have := congrArg c.mapMatrix h
    simp only [map_mul, map_zero, AlgHom.mapMatrix_apply] at this
    simp [this]
  have h4 := ex_neg (A := A) h3
  rw [neg_neg] at h4
  rw [h2, map_ex, Matrix.mul_assoc, h4, Matrix.mul_one]

theorem log_skew {x : Matrix n n R} (h : x * x * x = 0) (hu : (1 + x)ᵀ * J * (1 + x).map c = J) :
    (x - (⅟2 : A) • (x * x))ᵀ * J + J * (x - (⅟2 : A) • (x * x)).map c = 0 := by
  have e0 : (1 + x).map c = 1 + x.map c := by
    change c.mapMatrix _ = 1 + c.mapMatrix x
    rw [map_add, map_one]
  have e1 : (x - (⅟2 : A) • (x * x)).map c = x.map c - (⅟2 : A) • (x.map c * x.map c) := by
    change c.mapMatrix _ = c.mapMatrix x - _ • (c.mapMatrix x * c.mapMatrix x)
    rw [map_sub, map_smul, map_mul]
  have h3 : x.map c * x.map c * x.map c = 0 := by
    have := congrArg c.mapMatrix h
    simpa only [map_mul, map_zero, AlgHom.mapMatrix_apply] using this
  rw [e0] at hu
  rw [e1]
  generalize x.map c = y at *
  have h4 : (1 + y) * (1 - y + y * y) = 1 := by
    rw [show (1 + y) * (1 - y + y * y) = 1 + y * y * y by noncomm_ring, h3, add_zero]
  have h5 : xᵀ * J = J * (-y + y * y) := by
    have : (1 + x)ᵀ * J = J * (1 - y + y * y) := by
      conv_rhs => rw [← hu, Matrix.mul_assoc, h4, Matrix.mul_one]
    rw [transpose_add, transpose_one] at this
    rw [show xᵀ * J = (1 + xᵀ) * J - J by noncomm_ring, this]
    noncomm_ring
  have h6 : (-y + y * y) * (-y + y * y) = y * y := by
    have : (-y + y * y) * (-y + y * y) = y * y - 2 * (y * y * y) + y * y * y * y := by noncomm_ring
    rw [this, h3]; simp
  rw [transpose_sub, transpose_smul, transpose_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, h5, ← Matrix.mul_assoc, h5,
    Matrix.mul_assoc, h6, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_neg]
  nth_rw 1 [← half (A := A) (J * (y * y))]
  abel

variable (c J e f) in

def eqs (p : Matrix n n R) : Matrix n n R →ₗ[A] Matrix n n R × Matrix n n R × Matrix n n R × Matrix n n R × Matrix n n R where
  toFun x := (xᵀ * J + J * x.map c, x * e, e * (x * f) - x * f, f * x - x, x * p)
  map_add' x y := by
    have : (x + y).map c = x.map c + y.map c := map_add c.mapMatrix x y
    simp only [this, transpose_add, Matrix.add_mul, Matrix.mul_add, Prod.mk_add_mk]
    congr 1
    · abel
    congr 2
    · abel
    congr 1
    abel
  map_smul' a x := by
    have : (a • x).map c = a • x.map c := map_smul c.mapMatrix a x
    simp only [this, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Prod.smul_mk, smul_add, smul_sub, RingHom.id_apply]

theorem eqs_zero {p x : Matrix n n R} : eqs c J e f p x = 0 ↔ xᵀ * J + J * x.map c = 0 ∧ Tri e f x ∧ x * p = 0 := by
  simp only [eqs, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero, sub_eq_zero]
  exact ⟨fun h => ⟨h.1, ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩, fun h => ⟨h.1, h.2.1.1, h.2.1.2, h.2.1.3, h.2.2⟩⟩

theorem Tri.grp {x y : Matrix n n R} (hx : Tri e f (x - 1)) (hy : Tri e f (y - 1)) :
    Tri e f (x * y - 1) ∧ (x * y - 1) * f = (x - 1) * f + (y - 1) * f := by
  rw [show x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) by noncomm_ring]
  exact ⟨(hx.add hy).add (hx.mul hy), by rw [Matrix.add_mul, hx.mf hy, add_zero, Matrix.add_mul]⟩

theorem Tri.inv {x y : Matrix n n R} (hx : Tri e f (x - 1)) (h : y * x = 1) : Tri e f (y - 1) := by
  have h3 := hx.three hx hx
  have : y - 1 = -(x - 1) + (x - 1) * (x - 1) := by
    have h4 : x * (1 - (x - 1) + (x - 1) * (x - 1)) = 1 := by
      rw [show x * (1 - (x - 1) + (x - 1) * (x - 1)) = 1 + (x - 1) * (x - 1) * (x - 1) by noncomm_ring, h3, add_zero]
    have h5 : y = 1 - (x - 1) + (x - 1) * (x - 1) := by
      exact left_inv_eq_right_inv h h4
    rw [h5]; abel
  rw [this]
  exact hx.neg.add (hx.mul hx)

theorem Tri.ex_f {x : Matrix n n R} (hx : Tri e f x) : (Grp.ex A x - 1) * f = x * f := by
  rw [Grp.ex, add_assoc, add_sub_cancel_left, Matrix.add_mul, Matrix.smul_mul, hx.mf hx, smul_zero, add_zero]

theorem Tri.log {x : Matrix n n R} (hx : Tri e f x) :
    Tri e f (x - (⅟2 : A) • (x * x)) ∧ (x - (⅟2 : A) • (x * x)) * f = x * f := by
  refine ⟨?_, by rw [Matrix.sub_mul, Matrix.smul_mul, hx.mf hx, smul_zero, sub_zero]⟩
  rw [sub_eq_add_neg]
  exact hx.add ((hx.mul hx).smul _).neg

theorem Tri.zero_mul {x y : Matrix n n R} (hx : x * f = 0) (hy : Tri e f y) : x * y = 0 := by
  rw [← hy.h3, ← Matrix.mul_assoc, hx, Matrix.zero_mul]

end Nil

end PositivityTheory.ThKEnd.Grp

end
