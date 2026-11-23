import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Detlow
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hadam
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private def thB {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) :
    VR L N →ₗ[ℝ] VR L N →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ w, (star (x w) ⬝ᵥ (mat h w *ᵥ y w)).re)
    (fun x x' y => by simp [add_dotProduct, Finset.sum_add_distrib])
    (fun c x y => by simp [smul_dotProduct, Finset.mul_sum])
    (fun x y y' => by simp [mulVec_add, dotProduct_add, Finset.sum_add_distrib])
    (fun c x y => by simp [mulVec_smul, dotProduct_smul, Finset.mul_sum])

private theorem thB_self {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) (x : VR L N) :
    thB h x x = qR h x := rfl

private theorem th_qsmul {L : Type} [Field L] [NumberField L] {N : ℕ} (t : ℝ) (k : HS L N)
    (v : Lat L N) : q (t • k) v = t * q k v :=
  (UpperTheory.V.KT.ev v).map_smul t k

private def thKB {L : Type} [Field L] [NumberField L] {N : ℕ} (c C' : ℝ)
    (B : Matrix (Fin N) (Fin N) (𝓞 L)) : Set (HS L N) :=
  {k | (∀ v : Lat L N, v ≠ 0 → c ≤ q k v) ∧ ∀ a, q k (fun i => B i a) ≤ C'}

private theorem star_dotProduct_mulVec_swap_of_isHermitian {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (x y : Fin N → ℂ) :
    star y ⬝ᵥ (K *ᵥ x) = star (star x ⬝ᵥ (K *ᵥ y)) := by
  rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec]
  congr 2
  exact congrArg (· *ᵥ y) hK.eq

private theorem norm_dotProduct_mulVec_le_re_add_re_of_posSemidef {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.PosSemidef) (x y : Fin N → ℂ) :
    ‖star x ⬝ᵥ (K *ᵥ y)‖ ≤ (star x ⬝ᵥ (K *ᵥ x)).re + (star y ⬝ᵥ (K *ᵥ y)).re := by
  have h1 := hK.re_dotProduct_nonneg (x + y)
  have h2 := hK.re_dotProduct_nonneg (x - y)
  have h3 := hK.re_dotProduct_nonneg (x + Complex.I • y)
  have h4 := hK.re_dotProduct_nonneg (x - Complex.I • y)
  have hs := star_dotProduct_mulVec_swap_of_isHermitian hK.1 x y
  simp only [RCLike.re_to_complex, star_add, star_sub, star_smul, mulVec_add, mulVec_sub, mulVec_smul,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hs] at h1 h2 h3 h4
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1 h2 h3 h4
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : |(star x ⬝ᵥ (K *ᵥ y)).re| ≤ ((star x ⬝ᵥ (K *ᵥ x)).re + (star y ⬝ᵥ (K *ᵥ y)).re) / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have e2 : |(star x ⬝ᵥ (K *ᵥ y)).im| ≤ ((star x ⬝ᵥ (K *ᵥ x)).re + (star y ⬝ᵥ (K *ᵥ y)).re) / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

private theorem smul_mem_pos_of_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {k : HS L N}
    (hk : k ∈ Pos L N) {t : ℝ} (ht : 0 < t) : t • k ∈ Pos L N := by
  intro w
  have : mat (t • k) w = t • mat k w := by ext i j; simp [mat]
  rw [this]
  exact (hk w).smul ht

private theorem re_dotProduct_mat_mulVec_le_qR {L : Type} [Field L] [NumberField L] {N : ℕ} {k : HS L N}
    (hk : k ∈ Pos L N) (z : VR L N) (w : InfinitePlace L) :
    (star (z w) ⬝ᵥ (mat k w *ᵥ z w)).re ≤ qR k z := by
  unfold qR
  exact Finset.single_le_sum (f := fun w => (star (z w) ⬝ᵥ (mat k w *ᵥ z w)).re)
    (fun w _ => (hk w).posSemidef.re_dotProduct_nonneg (z w)) (Finset.mem_univ w)

private theorem qR_nonneg_of_mem_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {k : HS L N}
    (hk : k ∈ Pos L N) (z : VR L N) : 0 ≤ qR k z :=
  Finset.sum_nonneg fun w _ => (hk w).posSemidef.re_dotProduct_nonneg (z w)

private theorem thKB_subset_pos {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {N : ℕ}
    {c C' : ℝ} (hc : 0 < c) (B : Matrix (Fin N) (Fin N) (𝓞 L)) : thKB c C' B ⊆ Pos L N := by
  intro k hk
  have hR : c⁻¹ • k ∈ Ry L N := by
    intro y hy
    rw [th_qsmul]
    have := hk.1 y hy
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    linarith
  have := smul_mem_pos_of_pos (rypos L N hR) hc
  rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at this

private theorem exists_injective_linearMap_gram_of_det_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ}
    (B : Matrix (Fin N) (Fin N) (𝓞 L)) (hB : B.det ≠ 0) :
    ∃ Φ : HS L N →ₗ[ℝ] (InfinitePlace L → Fin N → Fin N → ℂ), Function.Injective Φ ∧
      ∀ k w a b, Φ k w a b = star (toR (fun i => B i a) w) ⬝ᵥ (mat k w *ᵥ toR (fun i => B i b) w) := by
  let Φ : HS L N →ₗ[ℝ] (InfinitePlace L → Fin N → Fin N → ℂ) :=
    { toFun := fun k w a b => star (toR (fun i => B i a) w) ⬝ᵥ (mat k w *ᵥ toR (fun i => B i b) w)
      map_add' := fun k k' => by
        ext w a b
        have : mat (k + k') w = mat k w + mat k' w := rfl
        simp only [this, add_mulVec, dotProduct_add, Pi.add_apply]
      map_smul' := fun t k => by
        ext w a b
        have : mat (t • k) w = (t : ℂ) • mat k w := by ext i j; simp [mat]
        simp only [this, smul_mulVec, dotProduct_smul, Pi.smul_apply, RingHom.id_apply]
        simp [Complex.real_smul] }
  refine ⟨Φ, ?_, fun _ _ _ _ => rfl⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro k hk
  have hw : ∀ w, mat k w = 0 := by
    intro w
    set P : Matrix (Fin N) (Fin N) ℂ := B.map (embO w) with hP
    have hdet : IsUnit P.det := by
      rw [hP, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      refine isUnit_iff_ne_zero.mpr fun h0 => hB ?_
      have hinj : Function.Injective (embO (L := L) w) := fun x y hxy =>
        RingOfIntegers.coe_injective (w.embedding.injective hxy)
      exact hinj (by rw [h0, map_zero])
    have hdetH : IsUnit Pᴴ.det := by
      rw [det_conjTranspose]; exact hdet.star
    have h0 : Pᴴ * mat k w * P = 0 := by
      ext a b
      have := congrFun (congrFun (congrFun hk w) a) b
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc,
        conjTranspose_apply, Matrix.zero_apply]
      rw [Finset.sum_comm]
      simpa [Φ, toR, hP, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using this
    calc mat k w = (Pᴴ)⁻¹ * (Pᴴ * mat k w * P) * P⁻¹ := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul,
            Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = 0 := by rw [h0]; simp
  apply Subtype.ext
  funext w i j
  have := congrFun (congrFun (hw w) i) j
  simpa [mat] using this

private theorem isCompact_thKB_of_det_ne_zero {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {N : ℕ}
    {c D : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (B : Matrix (Fin N) (Fin N) (𝓞 L)) (hB : B.det ≠ 0) :
    IsCompact (thKB c D B) := by
  obtain ⟨Φ, hinj, hΦ⟩ := exists_injective_linearMap_gram_of_det_ne_zero B hB
  let e := LinearEquiv.ofInjective Φ hinj
  have hcont : Continuous e.symm :=
    LinearMap.continuous_of_finiteDimensional (e.symm : LinearMap.range Φ →ₗ[ℝ] HS L N)
  have hq : ∀ v : Lat L N, Continuous fun k : HS L N => q k v := fun v =>
    (UpperTheory.V.KT.ev v).continuous_of_finiteDimensional
  have hcl : IsClosed (thKB c D B) := by
    have h1 : IsClosed {k : HS L N | ∀ v : Lat L N, v ≠ 0 → c ≤ q k v} := by
      have : {k : HS L N | ∀ v : Lat L N, v ≠ 0 → c ≤ q k v} = ⋂ v : Lat L N, ⋂ (_ : v ≠ 0), {k | c ≤ q k v} := by
        ext; simp
      rw [this]
      exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_le continuous_const (hq v)
    have h2 : IsClosed {k : HS L N | ∀ a, q k (fun i => B i a) ≤ D} := by
      have : {k : HS L N | ∀ a, q k (fun i => B i a) ≤ D} = ⋂ a, {k | q k (fun i => B i a) ≤ D} := by
        ext; simp
      rw [this]
      exact isClosed_iInter fun a => isClosed_le (hq _) continuous_const
    exact h1.inter h2
  refine ((isCompact_closedBall (0 : LinearMap.range Φ) (2 * D)).image hcont).of_isClosed_subset hcl ?_
  intro k hk
  have hkP := thKB_subset_pos (C' := D) hc B hk
  refine ⟨e k, ?_, e.symm_apply_apply k⟩
  rw [mem_closedBall_zero_iff]
  show ‖Φ k‖ ≤ 2 * D
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun w => ?_
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun b => ?_
  rw [hΦ]
  refine (norm_dotProduct_mulVec_le_re_add_re_of_posSemidef (hK := (hkP w).posSemidef) _ _).trans ?_
  have ha : q k (fun i => B i a) ≤ D := hk.2 a
  have hb : q k (fun i => B i b) ≤ D := hk.2 b
  have ha' := re_dotProduct_mat_mulVec_le_qR hkP (toR fun i => B i a) w
  have hb' := re_dotProduct_mat_mulVec_le_qR hkP (toR fun i => B i b) w
  change qR k _ ≤ D at ha hb
  linarith

private theorem star_dotProduct_mulVec_inv_mulVec_of_posDef {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.PosDef) (b x : Fin N → ℂ) :
    star (K⁻¹ *ᵥ b) ⬝ᵥ (K *ᵥ x) = star b ⬝ᵥ x ∧ star x ⬝ᵥ (K *ᵥ (K⁻¹ *ᵥ b)) = star x ⬝ᵥ b := by
  have hu : IsUnit K.det := (isUnit_iff_isUnit_det K).mp hK.isUnit
  constructor
  · rw [star_mulVec, hK.isHermitian.inv.eq, ← dotProduct_mulVec, mulVec_mulVec, nonsing_inv_mul _ hu,
      one_mulVec]
  · rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

private theorem spans_setOf_q_le_ten_mul_of_covering {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hh : h ∈ Pos L N) {ρ : ℝ} (hρ : 0 < ρ) (hT : ∀ z : VR L N, ∃ v : Lat L N, qR h (z - toR v) ≤ ρ) :
    Spans {v : Lat L N | q h v ≤ 10 * ρ} := by
  by_contra hne
  unfold Spans at hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set a : Fin N → L := fun i => f (fun j => if i = j then 1 else 0) with ha
  have hfv : ∀ x, f x = ∑ i, x i * a i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [ha, smul_eq_mul]
  have ha0 : ∃ i, a i ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hf0 (LinearMap.ext fun x => by simp [hfv, h0])
  obtain ⟨i0, hi0⟩ := ha0
  let b : VR L N := fun w i => star (w.embedding (a i))
  let z : VR L N := fun w => (mat h w)⁻¹ *ᵥ b w
  have hB : ∀ x y : VR L N, thB h x y = ∑ w, (star (x w) ⬝ᵥ (mat h w *ᵥ y w)).re := fun _ _ => rfl
  have hlat : ∀ v : Lat L N, f (toL v) = 0 → thB h z (toR v) = 0 ∧ thB h (toR v) z = 0 := by
    intro v hv
    have he : ∀ w : InfinitePlace L, ∑ i, w.embedding (a i) * toR v w i = 0 := by
      intro w
      have := congrArg w.embedding hv
      rw [hfv, map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [toR, embO, toL, mul_comm]
    constructor
    · rw [hB]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [(star_dotProduct_mulVec_inv_mulVec_of_posDef (hh w) (b w) (toR v w)).1]
      simp [b, dotProduct, he w]
    · rw [hB]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [(star_dotProduct_mulVec_inv_mulVec_of_posDef (hh w) (b w) (toR v w)).2]
      have : star (toR v w) ⬝ᵥ b w = star (∑ i, w.embedding (a i) * toR v w i) := by
        simp [b, dotProduct, star_sum, mul_comm]
      rw [this, he w]
      simp
  have hzpos : 0 < thB h z z := by
    rw [thB_self]
    obtain w0 : InfinitePlace L := Classical.arbitrary _
    have hbw : b w0 ≠ 0 := by
      intro h0
      have := congrFun h0 i0
      simp [b] at this
      exact hi0 this
    have hzw : z w0 ≠ 0 := by
      intro h0
      apply hbw
      have hu : IsUnit (mat h w0).det := (isUnit_iff_isUnit_det _).mp (hh w0).isUnit
      have : mat h w0 *ᵥ z w0 = b w0 := by
        simp only [z, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
      rw [← this, h0, mulVec_zero]
    have h1 := (hh w0).re_dotProduct_pos hzw
    have h2 := re_dotProduct_mat_mulVec_le_qR hh z w0
    rw [RCLike.re_to_complex] at h1
    linarith
  set R := thB h z z with hRdef
  set t := Real.sqrt (4 * ρ / R) with htdef
  have ht2 : t * t = 4 * ρ / R := Real.mul_self_sqrt (by positivity)
  have htt : t * t * R = 4 * ρ := by rw [ht2]; field_simp
  obtain ⟨v, hv⟩ := hT (t • z)
  have hx := qR_nonneg_of_mem_pos hh (toR v)
  have hfv0 : f (toL v) ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := hlat v h0
    have : qR h (t • z - toR v) = t * t * R + qR h (toR v) := by
      rw [← thB_self, ← thB_self, hRdef]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2]
      ring
    linarith
  apply hfv0
  have hmem : toL v ∈ spanL {v : Lat L N | q h v ≤ 10 * ρ} := by
    apply Submodule.subset_span
    refine ⟨v, ?_, rfl⟩
    show qR h (toR v) ≤ 10 * ρ
    have hpar : qR h (toR v) + qR h (t • z + (t • z - toR v)) =
        2 * (t * t * R) + 2 * qR h (t • z - toR v) := by
      rw [← thB_self, ← thB_self, ← thB_self, hRdef]
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      ring
    have := qR_nonneg_of_mem_pos hh (t • z + (t • z - toR v))
    linarith
  exact hfk hmem

private theorem normSq_det_mul_re_det_le_pow_of_posDef {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.PosDef)
    (P : Matrix (Fin N) (Fin N) ℂ) {D : ℝ} (hD : 0 < D)
    (hdiag : ∀ a, (star (fun i => P i a) ⬝ᵥ (K *ᵥ fun i => P i a)).re ≤ D) :
    Complex.normSq P.det * K.det.re ≤ D ^ N := by
  have hG : (Pᴴ * K * P).PosSemidef := hK.posSemidef.conjTranspose_mul_mul_same P
  have hentry : ∀ a b, (Pᴴ * K * P) a b = star (fun i => P i a) ⬝ᵥ (K *ᵥ fun i => P i b) := by
    intro a b
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hG' : (D⁻¹ • (Pᴴ * K * P)).PosSemidef := hG.smul (inv_nonneg.mpr hD.le)
  have hd : ∀ a, ((D⁻¹ • (Pᴴ * K * P)) a a).re ≤ 1 := by
    intro a
    rw [Matrix.smul_apply, hentry, Complex.real_smul, Complex.re_ofReal_mul]
    rw [← div_eq_inv_mul, div_le_one hD]
    exact hdiag a
  have h1 := (hadam N _ hG' hd).2.1
  have hs : D⁻¹ • (Pᴴ * K * P) = ((D⁻¹ : ℝ) : ℂ) • (Pᴴ * K * P) := by
    ext i j; simp [Complex.real_smul]
  rw [hs, det_smul, Fintype.card_fin, det_mul, det_mul, det_conjTranspose] at h1
  have : (star P.det * K.det * P.det) = ((Complex.normSq P.det : ℝ) : ℂ) * K.det := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [this, ← mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul] at h1
  rw [inv_pow, mul_assoc, inv_mul_le_iff₀ (by positivity), mul_one] at h1
  exact h1

private theorem prod_normSq_embedding_eq_abs_norm_of_isTotallyComplex {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] (x : L) :
    ∏ w : InfinitePlace L, Complex.normSq (w.embedding x) = |(Algebra.norm ℚ x : ℝ)| := by
  have := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∀ w : InfinitePlace L, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  simp only [h2] at this
  rw [← Rat.cast_abs, ← this]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]

private theorem nrmDet_le_mul_div_pow_of_q_le {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {N : ℕ}
    (h : HS L N) (hh : h ∈ Pos L N) {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (hlam : ∀ v : Lat L N, v ≠ 0 → c ≤ q h v) (A : Matrix (Fin N) (Fin N) (𝓞 L))
    (hA : ∀ a, q h (fun i => A i a) ≤ D) :
    (nrmDet A : ℝ) ≤ I0 L N * (D / c) ^ (N * Fintype.card (InfinitePlace L)) := by
  set r := Fintype.card (InfinitePlace L) with hr
  have hw : ∀ w : InfinitePlace L,
      Complex.normSq (w.embedding (A.det : L)) * (mat h w).det.re ≤ D ^ N := by
    intro w
    have hdet : (A.map (embO w)).det = w.embedding (A.det : L) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    have := normSq_det_mul_re_det_le_pow_of_posDef (hh w) (A.map (embO w)) hD (fun a =>
      (re_dotProduct_mat_mulVec_le_qR hh (toR fun i => A i a) w).trans (hA a))
    rwa [hdet] at this
  have hpos : ∀ w, 0 < (mat h w).det.re := fun w => (Complex.pos_iff.mp (hh w).det_pos).1
  have hprod : (∏ w : InfinitePlace L, Complex.normSq (w.embedding (A.det : L))) * ∏ w, (mat h w).det.re ≤ (D ^ N) ^ r := by
    rw [← Finset.prod_mul_distrib, hr, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun w _ => mul_nonneg (Complex.normSq_nonneg _) (hpos w).le)
      (fun w _ => hw w)
  have hRy : c⁻¹ • h ∈ Ry L N := by
    intro y hy
    rw [th_qsmul]
    have := hlam y hy
    rw [← div_eq_inv_mul, le_div_iff₀ hc]
    linarith
  have hdl := detlow L N _ hRy
  have hmat : ∀ w, (mat (c⁻¹ • h) w).det.re = (c⁻¹) ^ N * (mat h w).det.re := by
    intro w
    have : mat (c⁻¹ • h) w = ((c⁻¹ : ℝ) : ℂ) • mat h w := by ext i j; simp [mat, Complex.real_smul]
    rw [this, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  simp only [hmat, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hdl
  rw [← hr] at hdl
  set PK := ∏ w, (mat h w).det.re with hPKdef
  have hPK : 0 < PK := Finset.prod_pos fun w _ => hpos w
  rw [prod_normSq_embedding_eq_abs_norm_of_isTotallyComplex] at hprod
  have hn : (nrmDet A : ℝ) = |(Algebra.norm ℚ (A.det : L) : ℝ)| := by
    unfold nrmDet
    rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.cast_intCast, Algebra.coe_norm_int]
  rw [hn]
  set X := |(Algebra.norm ℚ (A.det : L) : ℝ)|
  have hX : 0 ≤ X := abs_nonneg _
  set Y := (I0 L N : ℝ) * ((c⁻¹) ^ N) ^ r
  have hY : 0 ≤ Y := by positivity
  have h1 : 1 ≤ Y * PK := by simp only [Y, mul_assoc]; exact hdl
  calc X ≤ X * (Y * PK) := le_mul_of_one_le_right hX h1
    _ = Y * (X * PK) := by ring
    _ ≤ Y * (D ^ N) ^ r := mul_le_mul_of_nonneg_left hprod hY
    _ = I0 L N * (D / c) ^ (N * r) := by
      simp only [Y]; rw [div_eq_mul_inv, mul_pow, pow_mul, pow_mul]; ring

theorem pf_GThick : GThick := by
  classical
  intro hB hT L _ _ hL N hN c hc
  obtain ⟨C, hC, hTr⟩ := hT L hL N hN
  obtain ⟨hB1, hB2, -⟩ := hB L N hN
  set ρ := C / c with hρdef
  have hρ : 0 < ρ := div_pos hC hc
  have hD : 0 < 10 * ρ := by positivity
  set J := ⌈(I0 L N : ℝ) * ((10 * ρ) / c) ^ (N * Fintype.card (InfinitePlace L))⌉₊
  obtain ⟨S, -, hS⟩ := hnf L N J
  refine ⟨⋃ B ∈ S.filter (fun B => B.det ≠ 0), thKB c (10 * ρ) B, ?_, ?_, ?_⟩
  · exact (S.filter _).isCompact_biUnion fun B hB =>
      isCompact_thKB_of_det_ne_zero hc hD.le B (Finset.mem_filter.mp hB).2
  · exact Set.iUnion₂_subset fun B _ => thKB_subset_pos hc B
  · intro h hh hlh hlD
    have hlam : ∀ v : Lat L N, v ≠ 0 → c ≤ q h v := fun v hv => hlh.trans ((hB1 h hh).2.1 v hv)
    have hcov : ∀ z : VR L N, ∃ v : Lat L N, qR h (z - toR v) ≤ ρ := by
      intro z
      obtain ⟨v, hv⟩ := hTr h hh z
      exact ⟨v, hv.trans (div_le_div_of_nonneg_left hC.le hc hlD)⟩
    obtain ⟨A, hA0, hAM⟩ := exbasis L N _ (spans_setOf_q_le_ten_mul_of_covering h hh hρ hcov)
    have hAn := nrmDet_le_mul_div_pow_of_q_le h hh hc hD hlam A hAM
    have hJ : nrmDet A ≤ J := by
      have := hAn.trans (Nat.le_ceil _)
      exact_mod_cast this
    obtain ⟨g, hg⟩ := hS A hA0 hJ
    have hcol : ∀ a, g⁻¹ • (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) = fun i => A i a := by
      intro a
      have : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) =
          (g : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ (fun i => A i a) := by
        ext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this]
      show ((g⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ ((g : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ _) = _
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
    refine ⟨g, Set.mem_biUnion (Finset.mem_filter.mpr ⟨hg, ?_⟩) ⟨?_, ?_⟩⟩
    · rw [det_mul]
      refine mul_ne_zero ?_ hA0
      exact (Matrix.isUnit_det_of_invertible _).ne_zero
    · intro v hv
      rw [hB2]
      refine hlam _ ?_
      intro h0
      apply hv
      have : g • (g⁻¹ • v) = v := smul_inv_smul g v
      rw [← this, h0, smul_zero]
    · intro a
      rw [hB2, hcol]
      exact hAM a

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
