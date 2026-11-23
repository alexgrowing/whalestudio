import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

open MeasureTheory Filter Topology Matrix NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.OrthBridge

def headEquiv {r k : ℕ} (hk : k ≤ r) : Fin k ≃ {a : Fin r // (a : ℕ) < k} where
  toFun a := ⟨Fin.castLE hk a, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem submatrix_neg_transpose {r k : ℕ} (hk : k ≤ r) (s : Fin r → ℝ) (n : Matrix (Fin r) (Fin r) ℂ) :
    (-(gramOf s n)ᵀ).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      ((-gramHead s k n).submatrix (headEquiv hk) (headEquiv hk))ᵀ := by
  ext a b; rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Gw_eq (X : Data E r) {j : ℕ} (hp : X.p0 = r - j) (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) :
    PoinPf.Gw X w τ = -(gramOf (sigForm r j) (mat (nmat X w) τ))ᵀ := by
  have hs : PoinPf.Jd X = -diagonal (fun i => ((sigForm r j i : ℝ) : ℂ)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [PoinPf.Jd, sgn, sigForm, hp]
      split_ifs <;> simp
    · simp [PoinPf.Jd, hab]
  have hc : ((mat (nmat X w) τ)ᴴ)ᵀ = (mat (nmat X w) τ).map (starRingEnd ℂ) := by
    ext a b; rfl
  rw [PoinPf.Gw, hs, gramOf, Matrix.transpose_mul, Matrix.transpose_mul, diagonal_transpose, hc]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem gram_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (cpt X x w) τ) = PoinPf.Gw X w τ := by
  show gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ) = _
  rw [FrameDegreeData.gram_mul, hx τ]
  rfl

theorem norm_dmin_eq (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {j : ℕ} (hp : X.p0 = r - j)
    (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (cpt X x w) τ i‖ = ‖(gramHead (sigForm r j) i (mat (nmat X w) τ)).det‖ := by
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  rw [PoinPf.dmin_cpt_orth X hx, lminor, Gw_eq X hp, submatrix_neg_transpose hi, det_transpose,
    det_submatrix_equiv_self, Matrix.det_neg]
  simp

theorem gramPos_iff (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {j : ℕ} (hp : X.p0 = r - j)
    (w : ReciprocityTheory.L2DbarEstimates.V (nd X)) (τ : X.Ψ) :
    (X.gramPos (cpt X x w) τ).PosDef ↔ (-gramHead (sigForm r j) X.p0 (mat (nmat X w) τ)).PosDef := by
  have h : X.gramPos (cpt X x w) τ =
      ((-gramHead (sigForm r j) X.p0 (mat (nmat X w) τ)).submatrix (headEquiv X.p0_le) (headEquiv X.p0_le))ᵀ := by
    rw [← submatrix_neg_transpose, ← Gw_eq X hp, ← gram_cpt X hx]
    rfl
  rw [h]
  constructor
  · intro hP
    have h1 := hP.transpose
    rw [transpose_transpose] at h1
    have h2 := h1.submatrix (e := (headEquiv X.p0_le).symm) (headEquiv X.p0_le).symm.injective
    simpa using h2
  · intro hP
    exact (hP.submatrix (e := headEquiv X.p0_le) (headEquiv X.p0_le).injective).transpose

section Coord

variable {Ψ : Type} [Fintype Ψ] {e : ℕ}

def sig (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) : Fin (nd X) ≃ Fin e :=
  ((Fintype.equivFin (Ent X)).symm.trans (Equiv.prodCongr lab (Equiv.refl _)).symm).trans q

def toChart (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) :
    (Fin e → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V (nd X) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (nd X) => ℂ) (sig X lab q).symm).trans
    (MeasurableEquiv.toLp 2 (Fin (nd X) → ℂ))

theorem toChart_apply (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) (z : Fin e → ℂ) :
    toChart X lab q z = (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm
      ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) := by
  ext i
  simp [toChart, sig, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem toChart_preserving (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) :
    MeasurePreserving (toChart X lab q) volume volume := by
  have hl : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (nd X) → ℂ)).symm :=
    GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))
  exact hl.symm.comp (volume_measurePreserving_piCongrLeft (fun _ : Fin (nd X) => ℂ) (sig X lab q).symm)

theorem mat_nmat_toChart (X : Data E r) (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) (z : Fin e → ℂ) (t : Ψ) :
    mat (nmat X (toChart X lab q z)) (lab t) = lowMat q z t := by
  ext a b
  rw [toChart_apply]
  simp only [mat, nmat, lowMat, Matrix.of_apply]
  split_ifs with h
  · simp [PiLp.toLp_apply]
  · rfl
  · rfl

theorem mem_iff (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {j : ℕ} (hp : X.p0 = r - j)
    (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) (z : Fin e → ℂ) :
    z ∈ cellDom j q ↔ toChart X lab q z ∈ OmF X x0 := by
  constructor
  · intro hz
    show cpt X x0 _ ∈ X.dom
    refine ExF.mem_dom_of_gramPos X fun τ => ?_
    obtain ⟨t, rfl⟩ := lab.surjective τ
    have h := hz t
    rw [InFlagDomain, ← mat_nmat_toChart X lab q z t, ← hp] at h
    refine ⟨?_, (gramPos_iff X ho hp _ _).2 h.2⟩
    show (mat x0 _ * mat (nmat X _) _).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (KU.orth_dom X ho _).1 h.1.ne_zero
  · intro hz t
    have hz' : cpt X x0 (toChart X lab q z) ∈ X.dom := hz
    have hd : (mat x0 (lab t) * mat (nmat X (toChart X lab q z)) (lab t)).det ≠ 0 := (hz' (lab t)).1
    have hP := (gramPos_iff X ho hp _ _).1 (X.gramPos_posDef hz' (lab t))
    rw [det_mul] at hd
    rw [mat_nmat_toChart] at hP hd
    rw [InFlagDomain, ← hp]
    exact ⟨isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hd), hP⟩

theorem dens_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {j : ℕ} (hp : X.p0 = r - j)
    (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) {z : Fin e → ℂ} (hz : toChart X lab q z ∈ OmF X x0) :
    densF X x0 (toChart X lab q z) = cellDens j q z := by
  unfold densF cellDens
  rw [← Equiv.prod_comp lab]
  refine Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => ?_
  have hz' : cpt X x0 (toChart X lab q z) ∈ X.dom := hz
  have hne : dmin X.Gm (cpt X x0 (toChart X lab q z)) (lab t) i.castSucc ≠ 0 := by
    intro h0
    have h1 := (hz' (lab t)).2 i.castSucc
    rw [h0] at h1
    simp at h1
  have hn := norm_dmin_eq X ho hp (toChart X lab q z) (lab t) i.castSucc
  rw [mat_nmat_toChart, Fin.val_castSucc] at hn
  have hd : 0 < ‖(gramHead (sigForm r j) i (lowMat q z t)).det‖ := by
    rw [← hn]; exact norm_pos_iff.2 hne
  rw [hn, gramLog, show (-4 : ℝ) * (1 / 2 * Real.log ‖(gramHead (sigForm r j) i (lowMat q z t)).det‖) =
      Real.log ‖(gramHead (sigForm r j) i (lowMat q z t)).det‖ * ((-2 : ℤ) : ℝ) by push_cast; ring,
    ← Real.rpow_def_of_pos hd, Real.rpow_intCast]

theorem muF_eq (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {j : ℕ} (hp : X.p0 = r - j)
    (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) {FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))}
    (hFF : MeasurableSet FF) (hsub : FF ⊆ OmF X x0) :
    muF X x0 FF = cellVol j q (toChart X lab q ⁻¹' FF) := by
  have hM := toChart_preserving X lab q
  rw [muF, withDensity_apply _ hFF, Measure.restrict_restrict hFF, Set.inter_eq_left.2 hsub, cellVol,
    ← hM.setLIntegral_comp_preimage_emb (toChart X lab q).measurableEmbedding]
  refine setLIntegral_congr_fun ((toChart X lab q).measurable hFF) fun z hz => ?_
  simp only [dens_eq X ho hp lab q (hsub hz)]

end Coord

end GlobalTheory.CompanionTheory.Ar.Cmp.OrthBridge

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem muF_orth_eq_cellVol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j e : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (Ψ : Type) [Fintype Ψ] (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e), IsOrth X x0 → j ≤ r → X.p0 = r - j → (∀ z : Fin e → ℂ, z ∈ cellDom j q ↔ (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ OmF X x0) ∧ ∀ FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X)), MeasurableSet FF → FF ⊆ OmF X x0 → muF X x0 FF = cellVol j q {z | (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ FF} := by
  intro E _ _ _ r j e X x0 Ψ _ lab q ho _ hp
  refine ⟨fun z => ?_, fun FF hFF hsub => ?_⟩
  · rw [← OrthBridge.toChart_apply]
    exact OrthBridge.mem_iff X ho hp lab q z
  · have h : {z : Fin e → ℂ | (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ FF} = OrthBridge.toChart X lab q ⁻¹' FF := by
      ext z
      rw [Set.mem_preimage, OrthBridge.toChart_apply]
      rfl
    rw [h]
    exact OrthBridge.muF_eq X ho hp lab q hFF hsub

end GlobalTheory.CompanionTheory.Ar.Cmp
