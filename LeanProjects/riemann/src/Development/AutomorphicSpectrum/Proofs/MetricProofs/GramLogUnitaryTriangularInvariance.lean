import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinorsStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix Topology
open scoped ComplexOrder

theorem posDef_eventually_of_continuous {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (A : X → Matrix n n ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  set K : Set (n → ℂ) := Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := isCompact_sphere 0 1
  have hQ : Continuous fun z : X × (n → ℂ) => (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    simp only [dotProduct, mulVec]
    refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
    exact (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul
      (continuous_finsetSum _ fun j _ =>
        ((hc i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (n → ℂ) in 𝓝 (x0, y),
      0 < (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp [hKdef] at hy
    have h := h0.dotProduct_mulVec_pos hy0
    rw [Complex.lt_def] at h
    exact (hQ.tendsto (x0, y)).eventually_const_lt (by simpa using h.1)
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x y => 0 < (star y ⬝ᵥ (A x *ᵥ y)).re) hP] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hH x) fun y hy => ?_
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hyK : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ K := by
    simp [hKdef, norm_smul, hn.ne']
  have h1 := hx _ hyK
  have e : star (((‖y‖⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ (A x *ᵥ (((‖y‖⁻¹ : ℝ) : ℂ) • y)) =
      ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (A x *ᵥ y)) := by
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  rw [e, Complex.re_ofReal_mul] at h1
  have him : (star y ⬝ᵥ (A x *ᵥ y)).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
      Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := (hH x).apply i j
    rw [Complex.star_def] at h
    rw [h]; ring
  rw [Complex.lt_def]
  refine ⟨?_, by simpa using him.symm⟩
  have := pos_of_mul_pos_right h1 (by positivity)
  simpa using this

theorem gramOf_isHermitian {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd g).IsHermitian := by
  unfold gramOf
  refine isHermitian_conjTranspose_mul_mul g ?_
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [diagonal_apply, h, Ne.symm h]

theorem continuous_gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) :
    Continuous fun g : Matrix (Fin N) (Fin N) ℂ => gramHead hd k g := by
  unfold gramHead gramOf
  exact (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_id).matrix_submatrix _ _

theorem isOpen_inFlagDomain (N j : ℕ) :
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} := by
  have h1 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | IsUnit g.det} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have h2 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | (-gramHead (sigForm N j) (N - j) g).PosDef} := by
    refine isOpen_iff_mem_nhds.2 fun g0 hg0 => ?_
    refine posDef_eventually_of_continuous (fun g => -gramHead (sigForm N j) (N - j) g) (fun a b => ?_)
      (fun g => ?_) g0 hg0
    · exact ((continuous_gramHead _ _).neg).matrix_elem a b
    · exact ((gramOf_isHermitian _ g).submatrix _).neg
  exact h1.inter h2

theorem gramOf_mul_of_preserves {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ)
    (hu : gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ))) :
    gramOf hd (u * g) = gramOf hd g := by
  unfold gramOf at hu ⊢
  rw [conjTranspose_mul]
  calc gᴴ * uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * (u * g)
      = gᴴ * (uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * u) * g := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem gramHead_of_triangular {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (b : Matrix (Fin N) (Fin N) ℂ)
    (hb : b.BlockTriangular id) :
    gramHead hd k b = (b.submatrix Subtype.val Subtype.val)ᴴ *
      diagonal (fun a : {a : Fin N // (a : ℕ) < k} => ((hd a : ℝ) : ℂ)) *
      b.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [gramHead, gramOf, submatrix_apply]
  rw [mul_apply, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, submatrix_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun a : Fin N => (a : ℕ) < k) (by simp)
    (fun l => star (b l i.1) * ((hd l : ℝ) : ℂ) * b l j.1)]
  rw [Finset.sum_filter_of_ne]
  intro l _ hl
  by_contra hlk
  apply hl
  have : b l i.1 = 0 := hb (by
    show i.1 < l
    have := i.2
    exact Fin.lt_def.2 (by omega))
  simp [this]

theorem sigForm_apply_ne_zero (N j : ℕ) (a : Fin N) : sigForm N j a ≠ 0 := by
  unfold sigForm; split_ifs <;> norm_num

theorem gramHead_det_ne_zero_of_triangular {N : ℕ} (hd : Fin N → ℝ) (hd0 : ∀ a, hd a ≠ 0) (k : ℕ)
    (b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) :
    (gramHead hd k b).det ≠ 0 := by
  have hbd : ∀ i, b i i ≠ 0 := by
    have h := (isUnit_iff_ne_zero.1 hu)
    rw [det_of_upperTriangular hb] at h
    exact fun i => (Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ i)
  have hs : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).det ≠ 0 := by
    have ht : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).BlockTriangular id :=
      fun i j hij => hb hij
    rw [det_of_upperTriangular ht]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hbd i.1
  rw [gramHead_of_triangular hd k b hb, det_mul, det_mul, det_conjTranspose, det_diagonal]
  refine mul_ne_zero (mul_ne_zero (star_ne_zero.2 hs) ?_) hs
  exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (hd0 a)

theorem gramHead_det_ne_zero (N j : ℕ) (hj : j ≤ N) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : InFlagDomain N j g) (k : ℕ) : (gramHead (sigForm N j) k g).det ≠ 0 := by
  obtain ⟨u, b, hu, hb, hbu, hug⟩ := GlobalTheory.T.flag_domain_unitary_triangular N j hj g hg
  have e : gramHead (sigForm N j) k g = gramHead (sigForm N j) k b := by
    unfold gramHead
    rw [← hug, gramOf_mul_of_preserves _ _ _ hu]
  rw [e]
  exact gramHead_det_ne_zero_of_triangular _ (sigForm_apply_ne_zero N j) k b hb hbu

theorem flagDomain_open_and_minors : ∀ (N j : ℕ), j ≤ N →
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧
      ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k,
        (gramHead (sigForm N j) k g).det ≠ 0 :=
  fun N j hj => ⟨isOpen_inFlagDomain N j, fun g hg k => gramHead_det_ne_zero N j hj g hg k⟩

end GlobalTheory.CompanionTheory.Ar.PB
