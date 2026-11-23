import Mathlib
import Formalism.HermitianLattices.StatementTheta

open scoped BigOperators
open Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

lemma thetaSummable_gauss {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℤ => Real.exp (-δ * (n : ℝ) ^ 2)) := by
  have hr1 : Real.exp (-δ) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hg : Summable (fun n : ℕ => Real.exp (-δ) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr1
  have key : ∀ n : ℕ, Real.exp (-δ * (n : ℝ) ^ 2) ≤ Real.exp (-δ) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hδ.le]
  apply Summable.of_nat_of_neg
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
    simpa using key n
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
    simpa [neg_sq] using key n

lemma thetaSummable_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ℤ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hg : Summable g) : Summable (fun c : ι → ℤ => ∏ i, g (c i)) := by
  refine summable_of_sum_le (c := ∏ i : ι, ∑' n, g n)
    (fun c => Finset.prod_nonneg (fun i _ => hg0 (c i))) (fun u => ?_)
  let S : ι → Finset ℤ := fun i => u.image (fun c => c i)
  have hsub : u ⊆ Fintype.piFinset S := by
    intro c hc
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hc
  calc ∑ c ∈ u, ∏ i, g (c i)
      ≤ ∑ c ∈ Fintype.piFinset S, ∏ i, g (c i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun c _ _ => Finset.prod_nonneg (fun i _ => hg0 (c i)))
    _ = ∏ i, ∑ n ∈ S i, g n := (Finset.prod_univ_sum S (fun _ n => g n)).symm
    _ ≤ ∏ i : ι, ∑' n, g n :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun n _ => hg0 n))
          (fun i _ => hg.sum_le_tsum _ (fun n _ => hg0 n))

section Alg

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

lemma thetaSummable_parallelogram (h : V →ₗ⋆[K] V →ₗ[K] K) (u v : V) :
    h (u + v) (u + v) + h (u - v) (u - v) = h u u + h u u + (h v v + h v v) := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

lemma thetaSummable_trpara (h : V →ₗ⋆[K] V →ₗ[K] K) (u v : V) :
    Algebra.trace ℚ K (h (u + v) (u + v)) + Algebra.trace ℚ K (h (u - v) (u - v)) =
      2 * Algebra.trace ℚ K (h u u) + 2 * Algebra.trace ℚ K (h v v) := by
  have e := congrArg (Algebra.trace ℚ K) (thetaSummable_parallelogram h u v)
  rw [map_add (Algebra.trace ℚ K), map_add (Algebra.trace ℚ K), map_add (Algebra.trace ℚ K),
    map_add (Algebra.trace ℚ K)] at e
  linarith

lemma thetaSummable_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (x : V) :
    0 ≤ Algebra.trace ℚ K (h x x) := by
  by_cases hx : x = 0
  · subst hx
    simp
  · exact (hpos x hx).le

lemma thetaSummable_shift (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (γ x : V) :
    Algebra.trace ℚ K (h x x) ≤
      2 * Algebra.trace ℚ K (h (γ + x) (γ + x)) + 2 * Algebra.trace ℚ K (h γ γ) := by
  have e := thetaSummable_trpara h (γ + x) (-γ)
  have n0 := thetaSummable_nonneg h hpos (γ + x - -γ)
  have e1 : γ + x + -γ = x := by abel
  have e2 : h (-γ) (-γ) = h γ γ := by simp
  rw [e1, e2] at e
  linarith

lemma thetaSummable_expand (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} [Fintype ι] (e : ι → V) (c : ι → ℤ) :
    Algebra.trace ℚ K (h (∑ i, c i • e i) (∑ i, c i • e i)) =
      ∑ i, ∑ j, (c i : ℚ) * (c j : ℚ) * Algebra.trace ℚ K (h (e i) (e j)) := by
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Alg

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma thetaSummable_sq_le (v : ι → ℝ) :
    ∑ i, v i ^ 2 ≤ (Fintype.card ι + 1 : ℝ) * ‖v‖ ^ 2 := by
  have h1 : ∀ i, v i ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    have hi := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at hi
    nlinarith [abs_nonneg (v i), sq_abs (v i)]
  calc ∑ i, v i ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum (fun i _ => h1 i)
    _ = (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card ι + 1 : ℝ) * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]

lemma thetaSummable_coercive (G : Matrix ι ι ℚ)
    (hG : ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w)) :
    ∃ l : ℝ, 0 < l ∧ ∀ v : ι → ℝ, l * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ v) := by
  set M : Matrix ι ι ℝ := (G + Gᵀ).map (Rat.cast : ℚ → ℝ) with hM
  have hcf : ∀ w : ι → ℚ, (fun i => (w i : ℝ)) ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) =
      2 * ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by
    intro w
    have h1 : ((G + Gᵀ).map (Rat.cast : ℚ → ℝ)) = G.map (Rat.cast : ℚ → ℝ) + (G.map (Rat.cast : ℚ → ℝ))ᵀ := by
      ext i j
      simp
    have h2 : ∀ M : Matrix ι ι ℝ, ∀ v : ι → ℝ, v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
      intro M v
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 : (((w ⬝ᵥ (G *ᵥ w)) : ℚ) : ℝ) =
        (fun i => (w i : ℝ)) ⬝ᵥ (G.map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
      push_cast
      try rfl
    rw [h1, Matrix.add_mulVec, dotProduct_add, h2, ← h3]
    ring
  have hcont : Continuous fun v : ι → ℝ => v ⬝ᵥ (M *ᵥ v) := by
    first
    | fun_prop
    | exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hGnn : ∀ w : ι → ℚ, 0 ≤ w ⬝ᵥ (G *ᵥ w) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      simp
    · exact (hG w hw).le
  have hd := DenseRange.piMap (X := fun _ : ι => ℚ) (Y := fun _ : ι => ℝ)
    (fun _ => Rat.denseRange_cast)
  have hpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v
    refine hd.induction_on v (isClosed_le continuous_const hcont) (fun w => ?_)
    show 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (w i : ℝ))
    rw [hM, hcf]
    exact mul_nonneg zero_le_two (by exact_mod_cast hGnn w)
  have hPSD : M.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · unfold Matrix.IsHermitian
      ext i j
      simp [hM, add_comm]
    · rw [star_trivial]
      exact hpsd x
  have hdef : ∀ v : ι → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v) := by
    intro v hv
    rcases (hpsd v).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hSv : M *ᵥ v = 0 := by
        refine (hPSD.dotProduct_mulVec_zero_iff v).mp ?_
        rw [star_trivial]
        exact heq.symm
      have hdetS : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hSv⟩
      have hdet : (((G + Gᵀ).det : ℚ) : ℝ) = 0 := by
        rw [← hdetS]
        exact RingHom.map_det (Rat.castHom ℝ) (G + Gᵀ)
      have hdetQ : (G + Gᵀ).det = 0 := by exact_mod_cast hdet
      obtain ⟨w, hw, hGw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetQ
      have h0 : w ⬝ᵥ ((G + Gᵀ) *ᵥ w) = 0 := by rw [hGw, dotProduct_zero]
      rw [Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose,
        dotProduct_comm w (Matrix.vecMul w G), ← Matrix.dotProduct_mulVec] at h0
      have := hG w hw
      linarith
  by_cases hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ :=
      (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hu
      exact zero_ne_one hu
    refine ⟨u ⬝ᵥ (M *ᵥ u), hdef u hu0, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
      have hm := isMinOn_iff.mp hmin _ hmem
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hm
      have hc2 : ‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ (M *ᵥ v))) * ‖v‖ ^ 2 = v ⬝ᵥ (M *ᵥ v) := by
        field_simp
      calc u ⬝ᵥ (M *ᵥ u) * ‖v‖ ^ 2
          ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ (M *ᵥ v))) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hm (sq_nonneg _)
        _ = v ⬝ᵥ (M *ᵥ v) := hc2
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · exfalso
      apply hne
      have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      refine ⟨‖v‖⁻¹ • v, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']

end Mat

section Mat2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma thetaSummable_ratpos (G : Matrix ι ι ℚ)
    (hZ : ∀ c : ι → ℤ, c ≠ 0 → 0 < (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ))) :
    ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w) := by
  intro w hw
  have hdpos' : 0 < ∏ i, (w i).den := Finset.prod_pos (fun i _ => (w i).den_pos)
  have hdpos : (0 : ℚ) < ((∏ i, (w i).den : ℕ) : ℚ) := by exact_mod_cast hdpos'
  have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = ((∏ i, (w i).den : ℕ) : ℚ) * w i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun i => (w i).den) (Finset.mem_univ i)
    refine ⟨(w i).num * k, ?_⟩
    rw [hk]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose c hc using hint
  have hc0 : c ≠ 0 := by
    intro h0
    apply hw
    funext i
    have hci := hc i
    rw [h0, Pi.zero_apply, Int.cast_zero] at hci
    have := (mul_eq_zero.mp hci.symm).resolve_left hdpos.ne'
    simpa using this
  have hcw : (fun i => (c i : ℚ)) = ((∏ i, (w i).den : ℕ) : ℚ) • w := by
    funext i
    rw [hc i, Pi.smul_apply, smul_eq_mul]
  have hpos := hZ c hc0
  rw [hcw, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hpos
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_pos hdpos hdpos]

lemma thetaSummable_castform (G : Matrix ι ι ℚ) (w : ι → ℚ) :
    (fun i => (w i : ℝ)) ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) =
      2 * ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by
  have h1 : ((G + Gᵀ).map (Rat.cast : ℚ → ℝ)) = G.map (Rat.cast : ℚ → ℝ) + (G.map (Rat.cast : ℚ → ℝ))ᵀ := by
    ext i j
    simp
  have h2 : ∀ M : Matrix ι ι ℝ, ∀ v : ι → ℝ, v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
    intro M v
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : (((w ⬝ᵥ (G *ᵥ w)) : ℚ) : ℝ) =
      (fun i => (w i : ℝ)) ⬝ᵥ (G.map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
    push_cast
    try rfl
  rw [h1, Matrix.add_mulVec, dotProduct_add, h2, ← h3]
  ring

lemma thetaSummable_coercive_rat (G : Matrix ι ι ℚ)
    (hG : ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w)) :
    ∃ l : ℝ, 0 < l ∧ ∀ w : ι → ℚ, l * ∑ i, ((w i : ℚ) : ℝ) ^ 2 ≤ ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by
  obtain ⟨l, hl, hcoer⟩ := thetaSummable_coercive G hG
  have hN : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  refine ⟨l / (2 * (Fintype.card ι + 1)), by positivity, fun w => ?_⟩
  have h1 := hcoer (fun i => (w i : ℝ))
  rw [thetaSummable_castform] at h1
  have h2 := thetaSummable_sq_le (fun i => (w i : ℝ))
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hl.le, mul_le_mul_of_nonneg_left h1 hN.le]

end Mat2

section Main

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

lemma isAddTorsionFree_ringOfIntegers_submodule (L : Submodule (NumberField.RingOfIntegers K) V) :
    IsAddTorsionFree L := by
  constructor
  intro n hn a b hab
  apply Subtype.ext
  have hab' : n • (a : V) = n • (b : V) := by
    have := congrArg (fun y : L => (y : V)) hab
    simpa using this
  have h1 : (n : K) • ((a : V) - (b : V)) = 0 := by
    rw [smul_sub, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul K, hab', sub_self]
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hnK)

lemma thetaSummable_main (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L]
    (γ : V) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun x : L => Complex.exp (Real.pi * Complex.I * τ *
        ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ))) := by
  classical
  haveI : Module.Finite (NumberField.RingOfIntegers K) L :=
    Module.Finite.iff_fg.mpr (Submodule.IsLattice.fg (A := K))
  haveI : Module.Finite ℤ L := Module.Finite.trans (NumberField.RingOfIntegers K) L
  haveI : IsAddTorsionFree L := isAddTorsionFree_ringOfIntegers_submodule L
  haveI : Module.IsTorsionFree ℤ L := by
    first
    | infer_instance
    | (constructor
       intro r hr a b hab
       have hr0 : r ≠ 0 := hr.ne_zero
       apply Subtype.ext
       have hab' : r • (a : V) = r • (b : V) := by
         have := congrArg (fun y : L => (y : V)) hab
         simpa using this
       have h1 : (r : K) • ((a : V) - (b : V)) = 0 := by
         rw [smul_sub, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul K, hab', sub_self]
       have hrK : (r : K) ≠ 0 := Int.cast_ne_zero.mpr hr0
       exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hrK))
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  obtain ⟨ι, _, _, ⟨b⟩⟩ : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι),
      Nonempty (Module.Basis ι ℤ L) :=
    ⟨_, inferInstance, inferInstance, ⟨Module.Free.chooseBasis ℤ L⟩⟩
  let e : ι → V := fun i => ((b i : L) : V)
  let G : Matrix ι ι ℚ := fun i j => Algebra.trace ℚ K (h (e i) (e j))
  have hcoe : ∀ c : ι → ℤ, ((b.equivFun.symm c : L) : V) = ∑ i, c i • e i := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    simp [e]
  have hQ : ∀ c : ι → ℤ,
      Algebra.trace ℚ K (h ((b.equivFun.symm c : L) : V) ((b.equivFun.symm c : L) : V)) =
        (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c
    rw [hcoe c, thetaSummable_expand h e c]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, G]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hZ : ∀ c : ι → ℤ, c ≠ 0 → 0 < (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c hc
    rw [← hQ c]
    apply hpos
    intro h0
    apply hc
    have h1 : b.equivFun.symm c = 0 := by
      apply Subtype.ext
      simpa using h0
    exact b.equivFun.symm.injective (h1.trans (map_zero _).symm)
  obtain ⟨l, hl, hcoer⟩ := thetaSummable_coercive_rat G (thetaSummable_ratpos G hZ)
  have hP : 0 < Real.pi * τ.im := mul_pos Real.pi_pos hτ
  have hδ : 0 < Real.pi * τ.im * l / 2 := by positivity
  have hre : ∀ q : ℚ, ((Real.pi : ℂ) * Complex.I * τ * (q : ℂ)).re = -(Real.pi * τ.im * (q : ℝ)) := by
    intro q
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im]
    ring
  have hsum : Summable (fun c : ι → ℤ =>
      Real.exp (Real.pi * τ.im * ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℝ)) *
        ∏ i, Real.exp (-(Real.pi * τ.im * l / 2) * ((c i : ℤ) : ℝ) ^ 2)) :=
    (thetaSummable_pi (fun n => (Real.exp_pos _).le) (thetaSummable_gauss hδ)).mul_left _
  refine (Equiv.summable_iff b.equivFun.symm.toEquiv).mp ?_
  refine Summable.of_norm_bounded hsum (fun c => ?_)
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv]
  rw [Complex.norm_exp, hre, ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := thetaSummable_shift h hpos γ ((b.equivFun.symm c : L) : V)
  have hs' := (Rat.cast_le (K := ℝ)).mpr hs
  push_cast at hs'
  have hc := hcoer (fun i => (c i : ℚ))
  rw [← hQ c] at hc
  simp only [Rat.cast_intCast] at hc
  rw [← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hs' hP.le, mul_le_mul_of_nonneg_left hc hP.le]

end Main

end Formalism.HermitianLatticesTheory
