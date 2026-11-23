import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitA

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {ι : Type} [Fintype ι]

theorem Hf_add_l (v v' w : EuclideanSpace ℂ ι) : Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem Hf_sub_l (v v' w : EuclideanSpace ℂ ι) : Hf (v - v') w = Hf v w - Hf v' w := by
  simp only [Hf, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem Hf_smul_l (c : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (c • v) w = c * Hf v w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem Hf_add_r (v w w' : EuclideanSpace ℂ ι) : Hf v (w + w') = Hf v w + Hf v w' := by
  simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem Hf_sub_r (v w w' : EuclideanSpace ℂ ι) : Hf v (w - w') = Hf v w - Hf v w' := by
  simp only [Hf, PiLp.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem Hf_smul_r (c : ℂ) (v w : EuclideanSpace ℂ ι) : Hf v (c • w) = (starRingEnd ℂ) c * Hf v w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem Hf_rsmul_r (r : ℝ) (v w : EuclideanSpace ℂ ι) : Hf v (r • w) = r * Hf v w := by
  simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem Hf_rsmul_l (r : ℝ) (v w : EuclideanSpace ℂ ι) : Hf (r • v) w = r * Hf v w := by
  simp only [Hf, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem Hf_sum_l {κ : Type} (s : Finset κ) (f : κ → EuclideanSpace ℂ ι) (w : EuclideanSpace ℂ ι) :
    Hf (∑ k ∈ s, f k) w = ∑ k ∈ s, Hf (f k) w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Hf]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Hf_add_l, ih]

theorem Hf_sum_r {κ : Type} (s : Finset κ) (v : EuclideanSpace ℂ ι) (f : κ → EuclideanSpace ℂ ι) :
    Hf v (∑ k ∈ s, f k) = ∑ k ∈ s, Hf v (f k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Hf]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Hf_add_r, ih]

theorem Hf_swap (v w : EuclideanSpace ℂ ι) : Hf w v = (starRingEnd ℂ) (Hf v w) := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Hf_self_re (v : EuclideanSpace ℂ ι) : (Hf v v).re = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Hf, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem Hf_self (v : EuclideanSpace ℂ ι) : Hf v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Hf_self_re, Complex.ofReal_re]
  · rw [Complex.ofReal_im]
    simp only [Hf, Complex.im_sum, Complex.mul_conj, Complex.ofReal_im, Finset.sum_const_zero]

variable (K : Submodule ℝ (EuclideanSpace ℂ ι))

abbrev dK : ℕ := Module.finrank ℝ K

def ob : OrthonormalBasis (Fin (dK K)) ℝ K := stdOrthonormalBasis ℝ K

def e (k : Fin (dK K)) : EuclideanSpace ℂ ι := (ob K k : EuclideanSpace ℂ ι)

def z (k : Fin (dK K)) (v : EuclideanSpace ℂ ι) : ℂ := Hf v (e K k)

def p1 (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := ∑ k, z K k v • e K k

def p2 (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := v - p1 K v

def uc (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := ∑ k, (z K k v).im • e K k

def S (v : EuclideanSpace ℂ ι) : ℂ := ∑ k, z K k v ^ 2

theorem e_mem (k : Fin (dK K)) : e K k ∈ K := (ob K k).2

theorem inner_e (k l : Fin (dK K)) : ⟪e K k, e K l⟫_ℝ = if k = l then 1 else 0 := by
  show ⟪((ob K k : K) : EuclideanSpace ℂ ι), ((ob K l : K) : EuclideanSpace ℂ ι)⟫_ℝ = _
  rw [← Submodule.coe_inner]
  exact orthonormal_iff_ite.1 (ob K).orthonormal k l

section iso

variable {K}
variable (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK

theorem Hf_e (k l : Fin (dK K)) : Hf (e K k) (e K l) = if k = l then 1 else 0 := by
  apply Complex.ext
  · rw [← real_inner_eq_Hf, inner_e]
    by_cases h : k = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  · rw [hK _ (e_mem K k) _ (e_mem K l)]
    by_cases h : k = l <;> simp [h]

theorem z_e (k l : Fin (dK K)) : z K l (e K k) = if k = l then 1 else 0 := Hf_e hK k l

theorem coord_proj_one (l : Fin (dK K)) (v : EuclideanSpace ℂ ι) : z K l (p1 K v) = z K l v := by
  simp only [z, p1, Hf_sum_l, Hf_smul_l, Hf_e hK, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem coord_proj_two (l : Fin (dK K)) (v : EuclideanSpace ℂ ι) : z K l (p2 K v) = 0 := by
  have h := coord_proj_one hK l v
  show Hf (v - p1 K v) (e K l) = 0
  rw [Hf_sub_l]
  unfold z at h
  rw [h, sub_self]

theorem herm_proj_two_one (v w : EuclideanSpace ℂ ι) : Hf (p2 K v) (p1 K w) = 0 := by
  rw [p1, Hf_sum_r]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Hf_smul_r]
  have h := coord_proj_two hK k v
  unfold z at h
  rw [h, mul_zero]

theorem herm_proj_one_two (v w : EuclideanSpace ℂ ι) : Hf (p1 K v) (p2 K w) = 0 := by
  rw [Hf_swap, herm_proj_two_one hK, map_zero]

theorem herm_proj_one_one (v w : EuclideanSpace ℂ ι) :
    Hf (p1 K v) (p1 K w) = ∑ k, z K k v * (starRingEnd ℂ) (z K k w) := by
  rw [show p1 K w = ∑ k, z K k w • e K k from rfl, Hf_sum_r]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_smul_r, show Hf (p1 K v) (e K k) = z K k (p1 K v) from rfl, coord_proj_one hK, mul_comm]

theorem Hf_decomp (v w : EuclideanSpace ℂ ι) :
    Hf v w = ∑ k, z K k v * (starRingEnd ℂ) (z K k w) + Hf (p2 K v) (p2 K w) := by
  have hv : v = p1 K v + p2 K v := by
    rw [p2]
    abel
  have hw : w = p1 K w + p2 K w := by
    rw [p2]
    abel
  conv_lhs => rw [hv, hw]
  rw [Hf_add_l, Hf_add_r, Hf_add_r, herm_proj_one_one hK, herm_proj_one_two hK, herm_proj_two_one hK]
  ring

theorem norm_sq_decomp (v : EuclideanSpace ℂ ι) :
    ‖v‖ ^ 2 = ∑ k, ‖z K k v‖ ^ 2 + ‖p2 K v‖ ^ 2 := by
  have h := congrArg Complex.re (Hf_decomp hK v v)
  rw [Hf_self_re, Complex.add_re, Hf_self_re, Complex.re_sum] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem norm_proj_two_le (v : EuclideanSpace ℂ ι) : ‖p2 K v‖ ≤ ‖v‖ := by
  have h := norm_sq_decomp hK v
  have h0 : 0 ≤ ∑ k, ‖z K k v‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith [norm_nonneg (p2 K v), norm_nonneg v]

end iso

theorem uc_mem (v : EuclideanSpace ℂ ι) : uc K v ∈ K := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (e_mem K k)

theorem inner_uc (v : EuclideanSpace ℂ ι) (a : EuclideanSpace ℂ ι) (ha : a ∈ K) :
    ⟪uc K v, a⟫_ℝ = (Hf v a).im := by
  have ha' : ∑ k, ⟪e K k, a⟫_ℝ • e K k = a := by
    have h2 := congrArg (fun x : K => (x : EuclideanSpace ℂ ι)) ((ob K).sum_repr' ⟨a, ha⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, e] using h2
  conv_rhs => rw [← ha']
  rw [Hf_sum_r, Complex.im_sum, uc, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_rsmul_r, Complex.im_ofReal_mul, real_inner_smul_left, z, mul_comm]

theorem Hf_eq_inner (v w : EuclideanSpace ℂ ι) : Hf v w = ⟪w, v⟫_ℂ := by
  simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]

section V2

def span1 : Submodule ℂ (EuclideanSpace ℂ ι) := Submodule.span ℂ (Set.range (e K))

def V2 : Submodule ℂ (EuclideanSpace ℂ ι) := (span1 K)ᗮ

abbrev gB : ℕ := Module.finrank ℂ (V2 K)

def ob2 : OrthonormalBasis (Fin (gB K)) ℂ (V2 K) := stdOrthonormalBasis ℂ (V2 K)

def jj (t : EuclideanSpace ℂ (Fin (gB K))) : EuclideanSpace ℂ ι := ((ob2 K).repr.symm t : V2 K)

def wmap : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ (Fin (gB K)) :=
  (ob2 K).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L (V2 K).orthogonalProjectionOnto

theorem jj_mem (t : EuclideanSpace ℂ (Fin (gB K))) : jj K t ∈ V2 K := ((ob2 K).repr.symm t).2

theorem jj_wmap (v : EuclideanSpace ℂ ι) : jj K (wmap K v) = (V2 K).starProjection v := by
  unfold jj wmap Submodule.starProjection
  simp

theorem Hf_jj (t t' : EuclideanSpace ℂ (Fin (gB K))) : Hf (jj K t) (jj K t') = Hf t t' := by
  rw [Hf_eq_inner, Hf_eq_inner, jj, jj, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]

theorem norm_jj (t : EuclideanSpace ℂ (Fin (gB K))) : ‖jj K t‖ = ‖t‖ := by
  unfold jj
  rw [show ‖(((ob2 K).repr.symm t : V2 K) : EuclideanSpace ℂ ι)‖ = ‖(ob2 K).repr.symm t‖ from rfl,
    LinearIsometryEquiv.norm_map]

theorem jj_add (t t' : EuclideanSpace ℂ (Fin (gB K))) : jj K (t + t') = jj K t + jj K t' := by
  simp [jj]

theorem coord_of_mem_complement {v : EuclideanSpace ℂ ι} (hv : v ∈ V2 K) (k : Fin (dK K)) : z K k v = 0 := by
  rw [z, Hf_eq_inner]
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self k) : e K k ∈ span1 K) hv

theorem z_jj (t : EuclideanSpace ℂ (Fin (gB K))) (k : Fin (dK K)) : z K k (jj K t) = 0 := coord_of_mem_complement K (jj_mem K t) k

theorem wmap_jj (t : EuclideanSpace ℂ (Fin (gB K))) : wmap K (jj K t) = t := by
  unfold wmap jj
  simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

variable {K}
variable (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK

theorem p2_mem_Z2_of_mem_Z2 (v : EuclideanSpace ℂ ι) : p2 K v ∈ V2 K := by
  show p2 K v ∈ (span1 K)ᗮ
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [← Hf_eq_inner]
    exact coord_proj_two hK k v
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

theorem starProj_eq (v : EuclideanSpace ℂ ι) : (V2 K).starProjection v = p2 K v := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (p2_mem_Z2_of_mem_Z2 hK v) fun w hw => ?_
  have h1 : v - p2 K v = p1 K v := by
    rw [p2]
    abel
  have h2 : p1 K v ∈ span1 K :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  rw [h1]
  exact Submodule.inner_right_of_mem_orthogonal h2 hw

theorem jj_wmap' (v : EuclideanSpace ℂ ι) : jj K (wmap K v) = p2 K v := by
  rw [jj_wmap, starProj_eq hK]

theorem norm_wmap (v : EuclideanSpace ℂ ι) : ‖wmap K v‖ = ‖p2 K v‖ := by
  rw [← norm_jj K (wmap K v), jj_wmap' hK]

theorem Hf_wmap (v w : EuclideanSpace ℂ ι) : Hf (wmap K v) (wmap K w) = Hf (p2 K v) (p2 K w) := by
  rw [← Hf_jj K, jj_wmap' hK, jj_wmap' hK]

end V2

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
