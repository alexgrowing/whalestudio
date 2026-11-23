import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StMajorantTransport

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped MatrixOrder ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MajorantTransport

theorem exists_conjTranspose_mul_self {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ X : Matrix ι ι ℂ, Xᴴ * X = P := by
  refine ⟨CFC.sqrt P, ?_⟩
  rw [(CFC.sqrt_nonneg P).posSemidef.isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg

theorem measurePreserving_mulVec {A : Matrix ι ι ℂ} (hA : Complex.normSq A.det = 1) :
    MeasurePreserving (fun z : ι → ℂ => A *ᵥ z) volume volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' A).restrictScalars ℝ
  have hdet : LinearMap.det f = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hA]
  have hcoe : (⇑f) = fun z : ι → ℂ => A *ᵥ z := by
    funext z; simp [f]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (ι → ℂ)))
    (f := f) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, hcoe] at hmap
  have hm := (LinearMap.continuous_of_finiteDimensional f).measurable
  rw [hcoe] at hm
  refine ⟨hm, ?_⟩
  simpa using hmap

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem normSq_det (h : HermitianForm F E W) (v : Basis ι E W) (g : archUnitary h v)
    (w : InfinitePlace E) : Complex.normSq ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ).det = 1 := by
  have hg := mem_archUnitary.mp g.2 w
  have hH : (gramAt h v w).det ≠ 0 := by
    simp only [gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact ((isUnit_det_gram h v).map w.embedding).ne_zero
  set G : Matrix ι ι ℂ := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  rw [show (G.map ⇑(starRingEnd ℂ))ᵀ = Gᴴ from rfl] at hg
  have h1 := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose, show star G.det = starRingEnd ℂ G.det from rfl] at h1
  have h2 : starRingEnd ℂ G.det * G.det = 1 := by
    apply mul_right_cancel₀ hH
    linear_combination h1
  have h3 : (Complex.normSq G.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self, h2]
  exact_mod_cast h3

def sqrtMap (Q : InfinitePlace E → Matrix ι ι ℂ) :
    (InfinitePlace E → ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (InfinitePlace E × ι) where
  toFun y := WithLp.toLp 2 (fun p => (Q p.1 *ᵥ y p.1) p.2)
  map_add' y z := by ext p; simp [mulVec_add]
  map_smul' c y := by ext p; simp [mulVec_smul]

omit [IsTotallyComplex E] [DecidableEq ι] in

theorem norm_sq_sqrtMap (Q : InfinitePlace E → Matrix ι ι ℂ) (y : InfinitePlace E → ι → ℂ) :
    ‖sqrtMap Q y‖ ^ 2 = ∑ w, (star (y w) ⬝ᵥ (((Q w)ᴴ * Q w) *ᵥ y w)).re := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [sqrtMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, dotProduct, Pi.star_apply,
    Complex.re_sum, Complex.star_def, Complex.conj_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_cast

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem exists_isometry {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v) :
    ∃ (d : ℕ) (S : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d)),
      ∀ y, ‖S y‖ = M.len y := by
  choose Q hQ using fun w => exists_conjTranspose_mul_self (M.posDef w)
  have hnorm : ∀ y, ‖sqrtMap Q y‖ = M.len y := by
    intro y
    rw [Majorant.len, ← Real.sqrt_sq (norm_nonneg (sqrtMap Q y)), norm_sq_sqrtMap]
    simp only [hQ]
  have hinj : Function.Injective (sqrtMap Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re = 0 := by
      have := norm_sq_sqrtMap Q y
      simp only [hQ, hy, norm_zero] at this
      linarith
    have hnn : ∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re := fun w =>
      (Complex.nonneg_iff.mp ((M.posDef w).posSemidef.dotProduct_mulVec_nonneg (y w))).1
    funext w
    by_contra hw
    have hpos := (Complex.lt_def.mp ((M.posDef w).dotProduct_mulVec_pos hw)).1
    have := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hnn w).mp h0 w (Finset.mem_univ _)
    simp only [Complex.zero_re] at hpos
    linarith
  have hdim : finrank ℂ (InfinitePlace E → ι → ℂ) =
      finrank ℂ (EuclideanSpace ℂ (InfinitePlace E × ι)) := by
    simp [Module.finrank_pi_fintype, finrank_euclideanSpace, Fintype.card_prod]
  let e : (InfinitePlace E → ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (InfinitePlace E × ι) :=
    LinearEquiv.ofBijective (sqrtMap Q)
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℂ (InfinitePlace E × ι))
  refine ⟨_, (e.restrictScalars ℝ).toContinuousLinearEquiv.trans b.repr.toContinuousLinearEquiv,
    fun y => ?_⟩
  simp only [ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map]
  exact hnorm y

def invApplyEquiv {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v) :
    (InfinitePlace E → ι → ℂ) ≃L[ℝ] (InfinitePlace E → ι → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := invApply g
      invFun := invApply g⁻¹
      map_add' := fun y z => by funext w; simp [invApply, mulVec_add]
      map_smul' := fun c y => by funext w; simp [invApply, mulVec_smul]
      left_inv := fun y => by funext w; simp [invApply, mulVec_mulVec]
      right_inv := fun y => by funext w; simp [invApply, mulVec_mulVec] }

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem measurePreserving_invApply {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) : MeasurePreserving (invApply g) volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume)
    (fun w => measurePreserving_mulVec (normSq_det h v g⁻¹ w))

end MajorantTransport

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem MajorantTransport.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantTransport.Statement h v := by
  intro M
  have : (volume : Measure (InfinitePlace E → ι → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  obtain ⟨d, S, hS⟩ := MajorantTransport.exists_isometry M
  set c := Measure.addHaarScalarFactor (Measure.map S.symm volume)
    (volume : Measure (InfinitePlace E → ι → ℂ))
  have hc : Measure.map S.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul (Measure.map S.symm volume) volume
  refine ⟨d, c, fun g => ⟨(MajorantTransport.invApplyEquiv g).trans S, fun y => hS _,
    fun L _ _ => ?_⟩⟩
  set T := (MajorantTransport.invApplyEquiv g).trans S
  have hT : MeasurePreserving T.symm volume (Measure.map T.symm volume) :=
    T.symm.continuous.measurable.measurePreserving _
  rw [ZLattice.covolume_comap L (Measure.map T.symm volume) volume hT]
  have hsymm : ⇑(MajorantTransport.invApplyEquiv g).symm = invApply g⁻¹ := rfl
  have hmap : Measure.map T.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) := by
    have hcomp : ⇑T.symm = (MajorantTransport.invApplyEquiv g).symm ∘ S.symm := rfl
    rw [hcomp, ← Measure.map_map (MajorantTransport.invApplyEquiv g).symm.continuous.measurable
      S.symm.continuous.measurable, hc, Measure.map_smul, hsymm,
      (MajorantTransport.measurePreserving_invApply g⁻¹).map_eq]
  let b := Module.Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L _ (ZLattice.isAddFundamentalDomain b _),
    ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume), hmap, measureReal_nnreal_smul_apply]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
