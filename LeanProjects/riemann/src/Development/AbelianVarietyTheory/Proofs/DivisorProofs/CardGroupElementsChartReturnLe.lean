import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThickPointHyperbolic
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSelfDualLatticeBoundedMajorantLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantChartPointCentreFactorTwoStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartMult

open Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def blk (X : Data E r) (b : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun k a => b τ (Fin.castLE X.p0_le k) (Fin.castLE X.p0_le a)

theorem colP_rmul_eq (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    X.colP (rmul y b) τ a = ∑ k, blk X b τ k a • X.colP y τ k := by
  classical
  funext i
  have e1 : X.colP (rmul y b) τ a i = ∑ j, y τ i j * b τ j (Fin.castLE X.p0_le a) := by
    show (mat y τ * mat b τ : Matrix (Fin r) (Fin r) ℂ) i (Fin.castLE X.p0_le a) = _
    rw [Matrix.mul_apply]; rfl
  rw [e1, Finset.sum_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) ((Fin.castLE_injective _).injOn)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun j _ hj => ?_) (fun c _ => ?_)
  · have hj' : X.p0 ≤ (j : ℕ) := by
      by_contra h
      exact hj ⟨⟨j, not_le.mp h⟩, by simp, by ext; simp⟩
    rw [(hb τ).2 j _ (by
      show ((Fin.castLE X.p0_le a : Fin r) : ℕ) < j
      have := a.isLt
      simp only [Fin.val_castLE]; omega), mul_zero]
  · show blk X b τ c a * y τ i _ = _
    simp only [blk, Matrix.of_apply]
    rw [mul_comm]

theorem blk_det_ne (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    (blk X b τ).det ≠ 0 := by
  have hup : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular hup] at hd
  have hup' : (blk X b τ).BlockTriangular id := fun a c h => by
    simp only [blk, Matrix.of_apply]
    exact (hb τ).2 _ _ (by rw [Fin.lt_def]; simp only [Fin.val_castLE]; exact h)
  rw [Matrix.det_of_upperTriangular hup', Finset.prod_ne_zero_iff]
  intro k _
  rw [Finset.prod_ne_zero_iff] at hd
  exact hd _ (Finset.mem_univ _)

end GlobalTheory.ChartMult

namespace GlobalTheory.ChartMult

open Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gramPos_rmul (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    X.gramPos (rmul y b) τ = (blk X b τ)ᵀ * X.gramPos y τ * (blk X b τ).map (starRingEnd ℂ) := by
  ext a c
  rw [Data.gramPos_apply, colP_rmul_eq X y hb, colP_rmul_eq X y hb, hermC_sum_left]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Data.gramPos_apply,
    hermC_smul_left, hermC_sum_right, hermC_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem posPart_eq_dot (X : Data E r) (y : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.posPart y τ v = ((fun a => hermC τ.1 X.Gm v (X.colP y τ a)) ⬝ᵥ
      ((X.gramPos y τ)⁻¹ *ᵥ (fun a => conj (hermC τ.1 X.Gm v (X.colP y τ a))))).re := by
  unfold Data.posPart
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc]; rfl

theorem maj_rmul_any (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj (rmul y b) τ v = X.maj y τ v := by
  unfold Data.maj
  congr 2
  rw [posPart_eq_dot, posPart_eq_dot]
  set B := blk X b τ
  have hB := blk_det_ne X hb τ
  have hc : (fun a => hermC τ.1 X.Gm v (X.colP (rmul y b) τ a)) =
      (fun a => hermC τ.1 X.Gm v (X.colP y τ a)) ᵥ* B.map (starRingEnd ℂ) := by
    funext a
    rw [colP_rmul_eq X y hb, hermC_sum_right]
    simp only [vecMul, dotProduct, hermC_smul_right, Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hw : (fun a => conj (hermC τ.1 X.Gm v (X.colP (rmul y b) τ a))) =
      Bᵀ *ᵥ (fun a => conj (hermC τ.1 X.Gm v (X.colP y τ a))) := by
    funext a
    rw [colP_rmul_eq X y hb, hermC_sum_right]
    simp only [mulVec, dotProduct, hermC_smul_right, Matrix.transpose_apply, map_sum, map_mul,
      Complex.conj_conj]
    rfl
  have hB1 : IsUnit (B.map (starRingEnd ℂ)).det := by
    rw [show B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix B from rfl, ← RingHom.map_det]
    exact (Ne.isUnit hB).map _
  have hB2 : IsUnit Bᵀ.det := by rw [Matrix.det_transpose]; exact Ne.isUnit hB
  rw [hc, hw, gramPos_rmul X y hb, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB1,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB2, Matrix.mul_one]

end GlobalTheory.ChartMult

namespace GlobalTheory.ChartMult

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_mulVec' {r : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (M *ᵥ v) = (M.map τ) *ᵥ Data.emb τ v := by
  funext a
  simp [Data.emb, Matrix.mulVec, dotProduct, map_sum]

theorem maj_le_four {r : ℕ} (X : DataX E r) {x : Frame X.Ψ r} (hx : IsOrth X.toData x) {ρ : ℝ}
    (hρ : (r : ℝ) ^ 2 * ρ ≤ 1 / 100) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {z z' : V (nd X.toData)}
    (hz : ‖z‖ ≤ ρ) (hz' : ‖z'‖ ≤ ρ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (heq : lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b) (v : Fin r → E) :
    ∑ τ, X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) ≤
      4 * ∑ τ, X.maj x τ (Data.emb τ.1 v) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  have hs : ∀ w : V (nd X.toData), ‖w‖ ≤ ρ → (r : ℝ) ^ 2 * ‖w‖ ≤ 1 / 100 := fun w hw =>
    (mul_le_mul_of_nonneg_left hw hr2).trans hρ
  have h1 := (GlobalTheory.T.majorant_chart_point_centre_factor_two E r X.toData x z' hx (hs z' hz') τ
    (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v))).2
  have h2 := (GlobalTheory.T.majorant_chart_point_centre_factor_two E r X.toData x z hx (hs z hz) τ (Data.emb τ.1 v)).1
  have e1 : X.maj (cpt X.toData x z') τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) =
      X.maj (cpt X.toData x z) τ (Data.emb τ.1 v) := by
    rw [← maj_rmul_any X.toData _ hb, ← heq, emb_mulVec',
      GlobalTheory.MajInv.maj_lact X.toData (X.Γ_stab γ hγ)]
  rw [e1] at h1
  linarith

end GlobalTheory.ChartMult

namespace GlobalTheory

open Matrix

theorem chart_mult_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε ρ : ℝ), 0 < r → IsOrth X.toData x → 0 < ε → (r : ℝ) ^ 2 * ρ ≤ 1 / 100 → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}.encard : ℝ≥0∞) ≤ ENNReal.ofReal (multBd E r ε) := by
  intro E _ _ _ r X x ε ρ hr hx hε hρ hL hmin
  classical
  have hdom : x ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X.toData hx
  obtain ⟨w, hwL, hli, hwB⟩ := exists_short_basis_at X x hdom ε hε hmin
  set Bd : ℝ := (2 * fdeg E * r : ℝ) ^ 4 * dE E ^ 2 / (4 * ε) with hBd
  have hd : 0 ≤ dE E := abs_nonneg _
  have hBd0 : 0 ≤ Bd := by positivity
  set T : Set (Fin r → E) := {v | v ∈ X.L' ∧ ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ 4 * Bd} with hT
  have hTc := GlobalTheory.T.encard_selfDualLattice_bounded_majorant_le E r X x ε (4 * Bd) hdom hε (by positivity) hmin
  have hTfin : T.Finite := by
    rw [← Set.encard_ne_top_iff]
    intro htop
    rw [htop] at hTc
    simp at hTc
  set Tf := hTfin.toFinset
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}
  let f : GL (Fin r) E → Fin r → Fin r → E := fun γ i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i
  have hmaps : Set.MapsTo f S (↑(Fintype.piFinset fun _ : Fin r => Tf)) := by
    rintro γ ⟨hγ, z, z', hz, hz', b, hb, heq⟩
    rw [Fintype.coe_piFinset]
    intro i _
    simp only [Tf, Set.Finite.coe_toFinset]
    refine ⟨hL γ hγ _ (hwL i), ?_⟩
    have := ChartMult.maj_le_four X hx hρ hγ hz hz' hb heq (w i)
    have := hwB i
    show ∑ τ, X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w i)) ≤ 4 * Bd
    linarith
  have hinj : Set.InjOn f S := by
    intro γ _ γ' _ h
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let bw := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hlin : Matrix.toLin' (γ : Matrix (Fin r) (Fin r) E) = Matrix.toLin' (γ' : Matrix (Fin r) (Fin r) E) :=
      bw.ext fun i => by
        simp only [bw, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.toLin'_apply]
        exact congrFun h i
    exact Units.ext (Matrix.toLin'.injective hlin)
  have hS := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_coe_eq_coe_finsetCard, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hS
  have hTe : T.encard = (Tf.card : ℕ∞) := hTfin.encard_eq_coe_toFinset_card
  rw [hTe, ENat.toENNReal_coe] at hTc
  set a : ℝ := (1 + 2 * Real.sqrt (4 * Bd / ε)) ^ (2 * fdeg E * r) with ha
  have ha0 : 0 ≤ a := by positivity
  have hsq : Real.sqrt (4 * Bd / ε) = 2 * fdeg E * r * (2 * fdeg E * r) * dE E / ε := by
    rw [show 4 * Bd / ε = (2 * fdeg E * r * (2 * fdeg E * r) * dE E / ε) ^ 2 by
      rw [hBd]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hmult : a ^ r = multBd E r ε := by
    rw [ha, hsq, multBd, ← pow_mul]
    congr 1
    · ring
    · ring
  calc (S.encard : ℝ≥0∞) ≤ ((Tf.card ^ r : ℕ) : ℕ∞) := ENat.toENNReal_le.mpr hS
    _ = (Tf.card : ℝ≥0∞) ^ r := by rw [ENat.toENNReal_coe]; push_cast; rfl
    _ ≤ ENNReal.ofReal a ^ r := pow_le_pow_left₀ zero_le hTc r
    _ = ENNReal.ofReal (multBd E r ε) := by rw [← ENNReal.ofReal_pow ha0, hmult]

end GlobalTheory
