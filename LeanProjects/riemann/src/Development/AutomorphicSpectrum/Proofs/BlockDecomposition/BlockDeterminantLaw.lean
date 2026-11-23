import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_eq_sum_set {S : Type} [AddCommMonoid S] (s : Set ι) [Fintype s] (f : ι → S)
    (h : ∀ m, m ∉ s → f m = 0) : ∑ m, f m = ∑ m : s, f m := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ s)) (by simp) f]
  exact (Finset.sum_filter_of_ne fun m _ hm => by_contra fun hs => hm (h m hs)).symm

theorem blk_mul {S : Type} [CommRing S] (s : Set ι) [Fintype s] (x y : Matrix ι ι S)
    (hy : ∀ r, r ∉ s → ∀ c ∈ s, y r c = 0) :
    (x * y).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      x.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) *
        y.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) := by
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact sum_eq_sum_set s _ fun m hm => by rw [hy m hm c c.2, mul_zero]

open Classical in
theorem det_blk_mul (s : Set ι) (p : GL ι R) {q : GL ι R} (hq : q ∈ stab R s) :
    (((p * q : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
        ((q : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [Units.val_mul, blk_mul s _ _ fun r hr c hc => (hq r hr c hc).1, Matrix.det_mul]

open Classical in
theorem det_blk_mul_inv (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
      (((p⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det = 1 := by
  rw [← det_blk_mul s p (inv_mem hp), mul_inv_cancel, Units.val_one,
    Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

open Classical in
theorem isUnit_det_blk (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    IsUnit ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det :=
  IsUnit.of_mul_eq_one _ (det_blk_mul_inv s hp)

open Classical in
theorem bdet_val (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((bdet s p : Rˣ) : R) = ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [bdet, dif_pos (isUnit_det_blk s hp), IsUnit.unit_spec]

theorem bdet_mul (s : Set ι) {p q : GL ι R} (hp : p ∈ stab R s) (hq : q ∈ stab R s) :
    bdet s (p * q) = bdet s p * bdet s q := by
  classical
  apply Units.ext
  rw [Units.val_mul, bdet_val s (mul_mem hp hq), bdet_val s hp, bdet_val s hq]
  exact det_blk_mul s p hq

theorem bdet_inv (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) : (bdet s p)⁻¹ = bdet s p⁻¹ := by
  classical
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  apply Units.ext
  rw [Units.val_mul, bdet_val s hp, bdet_val s (inv_mem hp), Units.val_one]
  exact det_blk_mul_inv s hp

theorem bdet_univ (g : GL ι R) : bdet (Set.univ : Set ι) g = Matrix.GeneralLinearGroup.det g := by
  classical
  have hs : g ∈ stab R (Set.univ : Set ι) := fun r hr => absurd (Set.mem_univ r) hr
  apply Units.ext
  rw [bdet_val _ hs]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  convert Matrix.det_submatrix_equiv_self (Equiv.Set.univ ι) (g : Matrix ι ι R)
  all_goals (funext x; rfl)

section Top

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isClosed_stab [T2Space R] (s : Set ι) : IsClosed (stab R s : Set (GL ι R)) := by
  have e : (stab R s : Set (GL ι R)) = ⋂ (r : ι) (_ : r ∉ s) (c : ι) (_ : c ∈ s),
      ({g : GL ι R | (g : Matrix ι ι R) r c = 0} ∩
        {g : GL ι R | ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun c =>
    isClosed_iInter fun _ => IsClosed.inter ?_ ?_
  · exact isClosed_eq (Units.continuous_val.matrix_elem r c) continuous_const
  · exact isClosed_eq ((Units.continuous_val.comp continuous_inv).matrix_elem r c) continuous_const

theorem continuousOn_bdet (s : Set ι) :
    ContinuousOn (bdet s) (stab R s : Set (GL ι R)) := by
  classical
  have hm (p : (stab R s : Set (GL ι R))) : (p : GL ι R) ∈ stab R s := p.2
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  constructor
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      (((p : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      ((Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => (bdet_val s (hm p)).symm
  · refine Continuous.congr (f := fun p : (stab R s : Set (GL ι R)) =>
      ((((p : GL ι R)⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det)
      (((Units.continuous_val.comp continuous_inv).comp continuous_subtype_val).matrix_submatrix _ _ |>.matrix_det)
      fun p => ?_
    show _ = (((bdet s (p : GL ι R))⁻¹ : Rˣ) : R)
    rw [bdet_inv s (hm p), bdet_val s (inv_mem (hm p))]

end Top

section Places

variable {E : Type} [Field E]

open Classical in

theorem bdet_rat (A : Ad E R) (hi : Function.Injective A.i) (s : Set ι) {p : GL ι R}
    (hp : p ∈ stab R s) (hr : p ∈ A.ratGL ι) : ∃ x, bdet s p = Units.map A.i.toMonoidHom x := by
  obtain ⟨g, rfl⟩ := hr
  set d : E := ((g : Matrix ι ι E).submatrix (Subtype.val : s → ι) Subtype.val).det with hd
  have hval : ((bdet s (Matrix.GeneralLinearGroup.map A.i g) : Rˣ) : R) = A.i d := by
    rw [bdet_val s hp, hd, RingHom.map_det]
    congr 1
  have hd0 : d ≠ 0 := by
    intro h0
    have hu := (bdet s (Matrix.GeneralLinearGroup.map A.i g)).isUnit
    rw [hval, h0, map_zero] at hu
    have h10 : (0 : R) = 1 := by
      have := isUnit_zero_iff.1 hu
      exact this
    exact zero_ne_one (hi (by rw [map_zero, map_one, h10]) : (0 : E) = 1)
  refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
  rw [hval]
  rfl

open Classical in

theorem norm_det_blk (M : Matrix ι ι ℂ) (hM : M ∈ Matrix.unitaryGroup ι ℂ) (s : Set ι)
    (h0 : ∀ r, r ∉ s → ∀ c ∈ s, M r c = 0) :
    ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ = 1 := by
  have h1 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.1 hM
  have h2 : ((star M * M).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det = 1 := by
    rw [h1, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
  rw [blk_mul s _ _ h0, Matrix.det_mul, Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_submatrix,
    Matrix.det_conjTranspose] at h2
  have h3 : ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ ^ 2 = 1 := by
    have := congrArg norm h2
    rw [norm_mul, norm_star, norm_one] at this
    rw [sq]; exact this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

theorem det_mem_subring {κ : Type} [Fintype κ] [DecidableEq κ] (O : Subring R) (m : Matrix κ κ R)
    (h : ∀ r c, m r c ∈ O) : m.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem lg_eq_zero (A : Ad E R) (hA : A.GoodL) (u : Rˣ) (h1 : (u : R) ∈ A.O)
    (h2 : ((u⁻¹ : Rˣ) : R) ∈ A.O) (hw : ∀ w, ‖A.φ w (u : R)‖ = 1) : A.lg u = 0 := by
  let j : Rˣ →* GL Unit R := Units.map (Matrix.scalar Unit : R →+* Matrix Unit Unit R).toMonoidHom
  have hj : j u ∈ A.kGL Unit := by
    refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
    · simpa [j] using h1
    · have : ((j u)⁻¹ : GL Unit R) = j u⁻¹ := (map_inv j u).symm
      rw [this]
      simpa [j] using h2
    · rw [Matrix.mem_unitaryGroup_iff]
      ext r c
      simp [j, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw w]
  have hdet : Continuous fun g : GL Unit R => (Matrix.GeneralLinearGroup.det g : Rˣ) := by
    rw [Units.continuous_iff]
    constructor
    · exact Units.continuous_val.matrix_det
    · have : (fun g : GL Unit R => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R)) =
          fun g => ((g⁻¹ : GL Unit R) : Matrix Unit Unit R).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [this]
      exact (Units.continuous_val.comp continuous_inv).matrix_det
  have hc : Continuous fun g : GL Unit R => A.lg (Matrix.GeneralLinearGroup.det g) :=
    hA.lgcont.comp hdet
  obtain ⟨C, hC⟩ := (hA.kcpt Unit).exists_bound_of_continuousOn hc.continuousOn
  have hone : A.lg 1 = 0 := by
    have := hA.lgmul 1 1
    rw [mul_one] at this
    linarith
  have hpow : ∀ n : ℕ, A.lg (u ^ n) = n * A.lg u := by
    intro n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hA.lgmul, ih]; push_cast; ring
  have hdj : Matrix.GeneralLinearGroup.det (j u) = u := by
    apply Units.ext
    simp [j, Matrix.GeneralLinearGroup.val_det_apply]
  have hb : ∀ n : ℕ, (n : ℝ) * |A.lg u| ≤ C := by
    intro n
    have := hC (j u ^ n) (pow_mem hj n)
    rw [map_pow, hdj, hpow, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
    exact this
  by_contra hne
  have hpos : 0 < |A.lg u| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |A.lg u|)
  have := hb n
  rw [div_lt_iff₀ hpos] at hn
  linarith

open Classical in

theorem lg_bdet (A : Ad E R) (hA : A.GoodL) (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s)
    (hk : p ∈ A.kGL ι) : A.lg (bdet s p) = 0 := by
  refine lg_eq_zero A hA _ ?_ ?_ fun w => ?_
  · rw [bdet_val s hp]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).1
  · rw [bdet_inv s hp, bdet_val s (inv_mem hp)]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).2
  · rw [bdet_val s hp, RingHom.map_det]
    refine (congrArg norm (congrArg Matrix.det ?_)).trans
      (norm_det_blk _ (hk.2 w) s fun r hr c hc => ?_)
    · ext r c; rfl
    · simp [(hp r hr c hc).1]

end Places

theorem bdetLaw : BdetLaw := by
  intro E R _ _ _ _ _ _ _ A hA ι _ _ s
  exact ⟨isClosed_stab s, fun p hp q hq => bdet_mul s hp hq, continuousOn_bdet s,
    fun p hp hr => bdet_rat A hA.iinj s hp hr, fun p hp hk => lg_bdet A hA s hp hk, bdet_univ⟩

end GlobalTheory.CompanionTheory.RgEis
