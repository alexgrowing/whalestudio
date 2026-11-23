import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteMchartCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NonemptyLift
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombinationStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieIntegral
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularInvOfDiagNe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverModelChart
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.EqCharGood

theorem existsUnique_mulVec_of_inCell {V K : Type} [CommRing V] [CommRing K] (φ : V →+* K)
    (hφ : Function.Injective φ) {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V)
    (hc : GlobalTheory.Reg.InCell ix u) (cv : Fin n → V) (aK : Fin r → K)
    (h : (u.map φ).mulVec aK = fun i => φ (cv i)) : ∃! a, u.mulVec a = cv := by
  let A : Matrix (Fin r) (Fin r) V := u.submatrix ix id
  have hlow : A.BlockTriangular OrderDual.toDual := fun i j hij => hc.1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A hlow]
    exact Finset.prod_eq_one fun i _ => hc.2 i
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hAK : IsUnit (A.map φ).det := by
    have e : (A.map φ).det = φ A.det := (RingHom.map_det φ A).symm
    rw [e, hdet, map_one]; exact isUnit_one
  have hinjA : ∀ v w : Fin r → V, A.mulVec v = A.mulVec w → v = w := fun v w hvw => by
    have := congrArg (A⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hinjAK : ∀ v w : Fin r → K, (A.map φ).mulVec v = (A.map φ).mulVec w → v = w := fun v w hvw => by
    have := congrArg ((A.map φ)⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAK, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hrow : ∀ (v : Fin r → V), A.mulVec v = fun i => u.mulVec v (ix i) := fun v => rfl
  let a : Fin r → V := A⁻¹.mulVec (fun i => cv (ix i))
  have ha : A.mulVec a = fun i => cv (ix i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
  have hmap : ∀ (M : Matrix (Fin n) (Fin r) V) (v : Fin r → V),
      (M.map φ).mulVec (fun i => φ (v i)) = fun i => φ (M.mulVec v i) := fun M v => by
    funext i
    exact (RingHom.map_mulVec φ M v i).symm
  have haK : (fun i => φ (a i)) = aK := by
    refine hinjAK _ _ ?_
    have e1 : (A.map φ).mulVec (fun i => φ (a i)) = fun i => φ (cv (ix i)) := by
      funext i
      exact (congrFun (hmap u a) (ix i)).trans (congrArg φ (congrFun ha i))
    rw [e1]
    funext i
    exact (congrFun h (ix i)).symm
  refine ⟨a, ?_, fun a' ha' => hinjA _ _ ((hrow a').trans ((funext fun i => congrFun ha' (ix i)).trans ha.symm))⟩
  funext i
  apply hφ
  have := congrFun (hmap u a) i
  rw [haK, h] at this
  exact this.symm

end GlobalTheory.EqCharGood

namespace GlobalTheory.EqCharGood

set_option maxHeartbeats 2000000 in

theorem inV_of_extIn_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, (letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) → evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c a n f hf la Y hP T io hio y hy
  classical
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  obtain ⟨k, hk⟩ := exists_factor T io hio
  obtain ⟨y', z, h1, h2, h3, h4⟩ := hy
  have hs : y' ≫ Y.s = spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
    have e1 : spMap (algebraMap T.V T.Fr) ≫ (y' ≫ Y.s) =
        spMap (algebraMap T.V T.Fr) ≫ spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
      rw [← Category.assoc, ← h3, Category.assoc, GlobalTheory.TraitDataIntrinsic.j_s, ← Category.assoc, h2, sp_comp,
        sp_comp, ← RingHom.comp_assoc, hk]
    obtain ⟨φ, hφ⟩ : ∃ φ : (la.valuation c.F).valuationSubring →+* T.V, y' ≫ Y.s = spMap φ :=
      ⟨(Spec.preimage (y' ≫ Y.s)).hom, by simp [spMap]⟩
    rw [hφ, sp_comp, sp_comp] at e1
    rw [hφ]
    congr 1
    have e2 := CommRingCat.hom_ext_iff.1 (Spec.map_injective e1)
    exact RingHom.ext fun x => hinj (RingHom.congr_fun e2 x)
  let _ : Algebra c.F T.V := k.toAlgebra
  let _ : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨zV, hzV1, hzV2⟩ := exists_lift Y y' k hs h4
  obtain ⟨J, _, M, hM⟩ := GlobalTheory.Reg.exists_finite_mchart_cover E H Dw l Xo c (la.valuation c.F).valuationSubring _ Y hP
  obtain ⟨j, hj⟩ := hM (y' (IsLocalRing.closedPoint T.V))
  obtain ⟨-, -, h3'⟩ := GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y
  obtain ⟨-, -, -, h4'⟩ := h3' (M j).U (M j).hU
  obtain ⟨f₀, hf₀, -⟩ := h4' T.V y' hj
  obtain ⟨ΛV⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.V f₀ zV hzV2 (hzV1.trans hf₀.symm)
  have hzj : z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp f₀) ≫ (M j).hU.fromSpec := by
    rw [h3, ← hf₀, ← Category.assoc, sp_comp]
  have hK := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.Fr _ z h2 hzj
  rw [h1] at hK
  obtain ⟨ΛK⟩ := hK
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.Reg.MChart.Lift.exists_coordinates E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 ΛK
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W → InV T x := fun x h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h
  choose ix u b huW hu0 hu1 hbt hbd hgub using
    fun τ => GlobalTheory.exists_integral_pivot_decomposition T.Fr W _ _ (g τ) (hgi τ)
  choose u₀' hu₀' using fun τ i j => hW _ (huW τ i j)
  let u₀ : ∀ τ : E →+* ℂ, Matrix (Fin (M j).n) (Fin (Dw.mult τ)) T.V := fun τ => Matrix.of fun i j' => u₀' τ i j'
  have hu₀ : ∀ τ i j', algebraMap T.V T.Fr (u₀ τ i j') = u τ i j' := hu₀'
  have hcell : ∀ τ, GlobalTheory.Reg.InCell (ix τ) (u₀ τ) := fun τ =>
    ⟨fun i j hij => hinj (by rw [hu₀, map_zero]; exact hu0 τ i j hij),
     fun i => hinj (by rw [hu₀, map_one]; exact hu1 τ i)⟩

  have heigMap : ∀ τ (cv : Fin (M j).n → T.V),
      (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun i => algebraMap T.V T.Fr (cv i)) ↔ (M j).Eig f₀ τ cv := by
    intro τ cv
    refine forall_congr' fun a' => ?_
    have key : ∀ i, algebraMap T.V T.Fr ((((M j).ρ a').map f₀).mulVec cv i) =
        ((((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀)).mulVec (fun i => algebraMap T.V T.Fr (cv i))) i :=
      fun i => by rw [RingHom.map_mulVec]; rfl
    have key2 : ∀ i, algebraMap T.V T.Fr ((algebraMap c.F T.V (embK c τ a') • cv) i) =
        (algebraMap c.F T.Fr (embK c τ a') • fun i => algebraMap T.V T.Fr (cv i)) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      exact congrArg (· * _) (RingHom.congr_fun hk _)
    constructor
    · intro h
      funext i
      apply hinj
      rw [key, key2]
      exact congrFun h i
    · intro h
      funext i
      rw [← key, ← key2, h]
  have humap : ∀ τ, (u₀ τ).map (algebraMap T.V T.Fr) = u τ := fun τ => Matrix.ext fun i j' => hu₀ τ i j'
  have heigK : ∀ τ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => u τ j' i) := by
    intro τ i a'
    have hgc : ∀ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => g τ j' i) := fun i =>
      (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ (hg τ i)).mp (y.1.eig τ i)
    have hG := (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols (((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀))
      (algebraMap c.F T.Fr (embK c τ a')) (g τ)).mpr fun i => hgc i a'
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hbt τ)]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd τ i).isUnit
    have hU : ((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀) * u τ = algebraMap c.F T.Fr (embK c τ a') • u τ := by
      have e : u τ = g τ * (b τ)⁻¹ := by rw [hgub τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      rw [e, ← Matrix.mul_assoc, hG, Matrix.smul_mul]
    exact (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols _ _ _).mp hU i
  have heigV : ∀ τ i, (M j).Eig f₀ τ (fun j' => u₀ τ j' i) := fun τ i =>
    (heigMap τ _).mp (by simpa only [hu₀] using heigK τ i)
  obtain ⟨hv1, hv2, hv3⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK
  have hbasis : ∀ τ cv, (M j).Eig f₀ τ cv → ∃! a, (u₀ τ).mulVec a = cv := by
    intro τ cv hcv
    have hcvK := (heigMap τ cv).mpr hcv
    obtain ⟨w, hw, -⟩ := hv1 (fun i => algebraMap T.V T.Fr (cv i))
    have htan := hv2 _ _ hw
    have heig := (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ hw).mpr hcvK
    obtain ⟨a0, ha0, -⟩ := y.1.basis τ w htan heig
    have hv := (GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK _ (fun i j' => g τ j' i) (y.1.u τ) a0 w
      (hg τ)).mp ha0
    have heq : (∑ i, a0 i • fun j' => g τ j' i) = fun i => algebraMap T.V T.Fr (cv i) := (hv3 w htan).unique hv hw
    refine GlobalTheory.EqCharGood.existsUnique_mulVec_of_inCell (algebraMap T.V T.Fr) hinj (ix τ) (u₀ τ) (hcell τ) cv
      ((b τ).mulVec a0) ?_
    rw [humap, Matrix.mulVec_mulVec, ← hgub τ, ← heq]
    funext j'
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨yV, -, hyV⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c _ _ Y (M j) T.V f₀ _ ΛV u₀ heigV hbasis
  let φ : T.V →ₐ[c.F] T.Fr := ⟨algebraMap T.V T.Fr, fun x => RingHom.congr_fun hk x⟩
  obtain ⟨zK, hzK⟩ := hE.bc _ _ φ yV
  have htK := GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c _ _ Y (M j) T.V T.Fr f₀ φ u₀ yV zK hyV hzK
  have hint : Integral T io zK := GlobalTheory.Reg.tie_integral hS E H Dw l Xo c _ _ Y (M j) hP T io f₀ ix u₀ hcell zK
    (GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun _ _ _ => rfl))
  have htu : (M j).Comparison₂ ((algebraMap T.V T.Fr).comp f₀) u zK :=
    GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun τ i j' => hu₀ τ i j')
  obtain ⟨t, ht⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 zK ΛK u b
    (GlobalTheory.Reg.CellChart.lift_point_unique htu.choose ΛK) (fun τ => ⟨hbt τ, hbd τ⟩)
    (by rw [show (fun τ => u τ * b τ) = g from funext fun τ => (hgub τ).symm]; exact hg) htu
  show InV T (evI y f)
  rw [inV_of_frBor hf y ⟨zK, hE.test _ zK, hint⟩ t ht]
  show InV T (evR Xo c f zK)
  rw [(GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf T.V).1 T.Fr φ yV zK hzK]
  exact ⟨_, rfl⟩

end GlobalTheory.EqCharGood
