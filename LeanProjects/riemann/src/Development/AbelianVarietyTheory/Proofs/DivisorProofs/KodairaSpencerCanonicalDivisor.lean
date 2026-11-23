import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellChartFrameEigenbasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellFramedPointsTriangularFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalTangentFrameJacobianDetOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerDetEqConstMulHorizontalStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem exists_unit_mul {Y : Scheme.{0}} {V : Y.Opens} (y : Y) (hy : y ∈ V) [IsDomain (Y.presheaf.stalk y)]
    (t d : Γ(Y, V)) (h0 : ger y hy t ≠ 0) (h1 : ger y hy t ∣ ger y hy d) (h2 : ger y hy d ∣ ger y hy t) :
    ∃ (V' : Y.Opens) (_ : y ∈ V') (h : V' ≤ V) (b : Γ(Y, V')), (∀ z hz, IsUnit (ger z hz b)) ∧
      resG Y h t = b * resG Y h d := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hu : IsUnit b := by
    refine IsUnit.of_mul_eq_one a (mul_left_cancel₀ h0 ?_)
    calc ger y hy t * (b * a) = (ger y hy t * a) * b := by ring
      _ = ger y hy t * 1 := by rw [← ha, ← hb, mul_one]
  obtain ⟨O, hO, s, rfl⟩ := Y.presheaf.exists_germ_eq b
  have hm : y ∈ V ⊓ O := ⟨hy, hO⟩
  have e : ger y hm (resG Y inf_le_left t) = ger y hm (resG Y inf_le_right s * resG Y inf_le_left d) := by
    rw [map_mul, ger_resG, ger_resG, ger_resG, hb, mul_comm]
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y _ _ _ _ e
  have l₁ : O' ⊓ Y.basicOpen s ≤ V ⊓ O := inf_le_left.trans i₁.le
  refine ⟨O' ⊓ Y.basicOpen s, ⟨hO', (Y.mem_basicOpen s y hO).2 hu⟩, l₁.trans inf_le_left,
    resG Y (l₁.trans inf_le_right) s, fun z hz => ?_, fun_ext_ger fun z hz => ?_⟩
  · rw [ger_resG]
    exact (Y.mem_basicOpen s z _).1 hz.2
  · have e₂ := congrArg (ger z hz.1) e'
    have a₁ := ger_resG i₁.le z hz.1 (resG Y (inf_le_left : V ⊓ O ≤ V) t)
    have a₂ := ger_resG i₂.le z hz.1 (resG Y (inf_le_right : V ⊓ O ≤ O) s * resG Y (inf_le_left : V ⊓ O ≤ V) d)
    have e₃ := a₁.symm.trans (e₂.trans a₂)
    simp only [map_mul, ger_resG] at e₃ ⊢
    exact e₃

theorem ger_ne_zero {Y : Scheme.{0}} {V O : Y.Opens} (hO : Dense (O : Set Y)) (t : Γ(Y, V))
    (h : ∀ z (hz : z ∈ V), z ∈ O → IsUnit (ger z hz t)) (y : Y) (hy : y ∈ V) : ger y hy t ≠ 0 := by
  intro h0
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y hy hy t 0 (h0.trans (map_zero _).symm)
  obtain ⟨z, hz, hzO⟩ := hO.inter_open_nonempty O' O'.isOpen ⟨y, hO'⟩
  have e₂ := congrArg (ger z hz) e'
  have a₁ := ger_resG i₁.le z hz t
  have a₂ := ger_resG i₂.le z hz (0 : Γ(Y, V))
  have e₃ := a₁.symm.trans (e₂.trans a₂)
  rw [map_zero] at e₃
  exact (h z _ hzO).ne_zero e₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem chartFr_congr {TF : TorFlag Xo c} {K : Type} [Field K] [Algebra c.F K] {k : TF.X.F.J} {z z' : Sp K ⟶ TF.X.YY}
    (e : z = z') {hz : ⊤ ≤ z ⁻¹ᵁ TF.X.F.U k} (hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k) {Q : FrPt Xo c K}
    (h : TF.X.F.ChartFr k z hz Q) : TF.X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem det_block {K : Type} [Field K] {m : ℕ} (o : Fin m ≃ HIx Dw (psiSet H))
    (G : (Fin m ⊕ VIx Dw) → TIx Dw (psiSet H) → K) (h0 : ∀ i b, G (.inl i) (.inr b) = 0)
    (h1 : (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b)).det = 1) :
    (Matrix.of fun a b => G (((tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl _))) a) (tanOrd Dw b)).det =
      (Matrix.of fun i j => G (.inl i) (.inl (o j))).det := by
  let e := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let A : Matrix (Fin m ⊕ VIx Dw) (Fin m ⊕ VIx Dw) K := Matrix.fromBlocks
    (Matrix.of fun i j => G (.inl i) (.inl (o j))) 0 (Matrix.of fun a j => G (.inr a) (.inl (o j)))
    (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b))
  have : (Matrix.of fun a b => G (e a) (tanOrd Dw b)) = A.submatrix e e := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    have hb : tanOrd Dw b = Equiv.sumCongr o (Equiv.refl (VIx Dw)) (e b) := by
      simp only [e, Equiv.trans_apply]
      rcases tanOrd Dw b with k | k <;> simp
    rw [hb]
    rcases e a with i | i <;> rcases e b with j | j <;> simp [A, h0]
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, h1, mul_one]

def diagUnit {R : Type} [CommRing R] (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R)
    (h : ∀ σ i, IsUnit (L σ i i)) : Rˣ :=
  ∏ q : Σ σ : E →+* ℂ, Fin (Dw.mult σ), (h q.1 q.2).unit⁻¹ ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 (some q)

theorem map_diagUnit {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R) (h : ∀ σ i, IsUnit (L σ i i)) (t : Ix Dw → Kˣ)
    (ht : ∀ σ i, (t (some ⟨σ, i⟩) : K) * φ (L σ i i) = 1) :
    (∏ ix, t ix ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 ix).val = φ (diagUnit L h).val := by
  change _ = (Units.map (φ : R →* K) (diagUnit L h)).val
  congr 1
  rw [diagUnit, map_prod, Fintype.prod_option, FlagMod.exOf_none, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [map_zpow, map_inv]
  congr 1
  exact eq_inv_of_mul_eq_one_left (Units.ext (ht q.1 q.2))

set_option maxHeartbeats 1600000 in

theorem exists_pole (hP : GlobalTheory.CovTop.Hypotheses₂) (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed Xo c)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z)
    (V : (Y₀ TF.X Z).Opens) (hy : y ∈ V) :
    ∃ (W : (Y₀ TF.X Z).Opens) (_ : y ∈ W) (_ : W ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι)
      (k : TF.X.F.J) (δ u : Γ(Y₀ TF.X Z, W)),
      W ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧ IsUnit u ∧
      (∀ z (hz : z ∈ W), IsUnit (ger z hz δ) ↔ z ∈ U₀ TF.X Z) ∧
      (∀ (W' : (Y₀ TF.X Z).Opens) (hW' : W' ≤ W) (f : Γ(Y₀ TF.X Z, W')), (∀ z (hz : z ∈ W'), z ∉ U₀ TF.X Z →
        ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) →
        ∀ z (hz : z ∈ W'), ger z (hW' hz) δ ∣ ger z hz f) ∧
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) ho hi,
        ev z W hz δ * H0.val (B := LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle
          ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) z
          (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k) ho hi ω₀.ω = ev z W hz u := by
  obtain ⟨i, hi⟩ := exists_chart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB y
  obtain ⟨U, n, e₀, v, hyU, hv₀⟩ := GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point E H Dw l Xo c TF Z hF y
  obtain ⟨e, W, k, L, N, hv, hyW, hWV, hc⟩ := GlobalTheory.T.exists_bigCell_chartFrame_eigenbasis E H Dw l Xo c TF Z U n e₀ v hv₀ y hyU V hy
  obtain ⟨ε, b, hb⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v _ hv.1 hv.2.1 hv.2.2
  obtain ⟨x, U', hU', hyU', hx, hbd⟩ := GlobalTheory.T.exists_coordinates_logVectorFields_determinant E H Dw l Xo c TF U b _ hyU
  have het := GlobalTheory.T.etale_bigCellCoordinates_flagSpace E H Dw l Xo c TF Z hF U n e v hv W k L N hc
  obtain ⟨s, hs, hcmp⟩ := GlobalTheory.T.kodaira_spencer_comparison hP E H Dw l Xo c TF
  let o : Fin Dw.dim ≃ HIx Dw (psiSet H) :=
    (Fintype.equivFinOfCardEq (FlagTan.card_HIx (FlagTan.isHalf_psiSet H))).symm
  obtain ⟨a, ha, hhor⟩ := GlobalTheory.T.logKodairaSpencer_det_eq_const_mul_horizontal E H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨W', hW'a, hyW', hW'⟩ := Opens.isBasis_iff_nbhd.1 (Y₀ TF.X Z).isBasis_affineOpens
    (show y ∈ W ⊓ (toBase TF Z ⁻¹ᵁ U'.1 ⊓ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i) from ⟨hyW, hyU', hi⟩)
  have hW'W : W' ≤ W := hW'.trans inf_le_left
  have hW'U : W' ≤ toBase TF Z ⁻¹ᵁ U'.1 := hW'.trans (inf_le_right.trans inf_le_left)
  have hW'i : W' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i := hW'.trans (inf_le_right.trans inf_le_right)
  let O := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let G : Fin Dw.dim ⊕ VIx Dw → Γ(Y₀ TF.X Z, W) :=
    Sum.elim (fun i => ((toBase TF Z).appLE U.1 W hc.2.1).hom (x i)) (cellCoord N)
  let g : Fin (FlagTan.dimFlag Dw) → Γ(Y₀ TF.X Z, W') := fun a => resG _ hW'W (G (O a))
  have hfr := GlobalTheory.T.isTopFormFrame_base_coordinates_add_variables_etale c.F TF.Y.X (Y₀ TF.X Z) TF.Y.s (toBase TF Z) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str
    ((Category.assoc _ _ _).trans (Category.id_comp _).symm) Dw.dim (FlagTan.dimFlag Dw) TF.smooth (VIx Dw) O U.1 U'.1 hU'
    U.2 W W' hW'W hc.1 hW'a hc.2.1 hW'U (cellCoord N) het x hx
  have hJ : IsUnit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g) :=
    ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isUnit_jacobian_iff i hW'a hW'i g).2 hfr
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : IsLocallyNoetherian TF.Y.X := LocallyOfFiniteType.isLocallyNoetherian TF.Y.s
  obtain ⟨r₁, r₂⟩ := GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing TF.Y.X (Y₀ TF.X Z) (toBase TF Z) (VIx Dw) (LogKS.interior TF.Y) U U' hU' W hc.1 hc.2.1
    (cellCoord N) het _ hbd
  let ac : Γ(Y₀ TF.X Z, W') := algX (str₀ TF.X Z) W' (a : c.F)
  have hac : IsUnit ac := (Ne.isUnit (Rat.cast_ne_zero.2 ha)).map _
  refine ⟨W', hyW', hW'W.trans hWV, i, k,
    resG _ hW'W (((toBase TF Z).appLE U.1 W hc.2.1).hom (logDet (fun j => (b j).1) x)),
    ac * resG _ hW'W (diagUnit L hc.2.2.2.2.1).val * (show Γ(Y₀ TF.X Z, W') from
      (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g), hW'i, hW'W.trans hc.2.2.1,
    (hac.mul ((Units.isUnit _).map _)).mul hJ, fun z hz => ?_, fun W'' hW'' f hf z hz => ?_, fun K _ z hz ho hi => ?_⟩
  · rw [ger_resG]
    exact r₁ z (hW'W hz) (hW'U hz)
  · rw [ger_resG]
    exact r₂ W'' (hW''.trans hW'W) (hW''.trans hW'U) f hf z hz
  have eM : toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = inc₀ TF.X Z := Category.id_comp _
  have hzW := FlagMod.le_preimage_mono hW'W hz
  have hU₀ : ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z := fun p hp => by
    have := ho hp
    rw [Modif.off_eq] at this
    exact this
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_map _ hc.2.2.1 hzW
  obtain ⟨_, hch⟩ := exists_chartFr (z ≫ inc₀ TF.X Z) hU₀
  obtain ⟨Q, hQ⟩ := hch k hk
  obtain ⟨P₀, P, t, hU, hQP, ht, hP₀, hB⟩ := GlobalTheory.T.exists_bigCell_framedPoints_triangular_frameChange E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW hk Q hQ
  have ez : z ≫ inc₀ TF.X Z = TF.X.ptY P := FlagMod.FlagCover.eq_ptY (hQ.lies.frBor hQP)
  obtain ⟨w, hw⟩ := (hKS K P).exists_isTanFrame
  have ezM : z ≫ toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = z ≫ inc₀ TF.X Z := by rw [eM]
  choose zw hzw hzO using fun b => exists_tanLift (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) (hw.isDef b)
    (ezM.trans ez) ho
  have hzw' : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ inc₀ TF.X Z = TF.X.ptY (w b) := fun b => by
    exact (congrArg (zw b ≫ ·) eM).symm.trans (hzw b)
  have hkM := ezM ▸ hk
  have key := ω₀.isKS K P Q t w z zw i k W' hW'i g hz (fun b => hzO b W' hz) hkM ho hi (chartFr_congr ezM.symm hkM hQ)
    hQP hw hzw
  obtain ⟨v₁, v₂⟩ := GlobalTheory.T.vertical_tangentFrame_jacobian_det_one E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW P₀ P hU ez hP₀ hB (fun b => w (.inr b))
    (fun b => zw (.inr b)) (fun b => hzO _ W hzW) hw.2 (fun b => hzw' _)
  have eb : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ toBase TF Z = frX (w b) ≫ TF.Y.j := fun b => by
    rw [← Category.assoc, hzw', (TF.X.lies_ptY _).1]
  have hwU : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1 := fun b =>
    eb b ▸ FlagMod.le_preimage_map _ hc.2.1 (hzO b W hzW)
  have hdet : ∀ σ, ((N σ).map (ev z W hzW)).det = 1 := fun σ => by
    rw [Matrix.det_of_upperTriangular fun i j hij => by rw [Matrix.map_apply, hc.2.2.2.2.2.1 σ i j hij, map_zero]]
    simp [hc.2.2.2.2.2.2.1]
  have hh := hhor x K P₀ P hU _ hdet hP₀ hB (fun b => w (.inl b)) (fun b => hwU _) hw.1
  have eP : z ≫ toBase TF Z = frX P₀ ≫ TF.Y.j := by
    rw [← Category.assoc, ez, (TF.X.lies_ptY _).1,
      FlagMod.eq_frX P₀ ((FlagMod.frX_fst P).trans hP₀.1) (FlagMod.frX_snd P)]
  have hblock := det_block o (fun a b => (ev (zw b) W (hzO b W hzW) (G a)).snd) (fun i b => v₂ b _) v₁
  have e₁ : (Matrix.of fun a b => (TangentOrigin.evalPt (zw (tanOrd Dw b)) W' (hzO _ W' hz) (g a)).snd) =
      Matrix.of fun a b => (ev (zw (tanOrd Dw b)) W (hzO _ W hzW) (G (O a))).snd := by
    ext a b
    exact congrArg TrivSqZeroExt.snd (FlagMod.ev_res _ hW'W _ _ _)
  have e₂ : (Matrix.of fun i j => (ev (zw (.inl (o j))) W (hzO _ W hzW) (G (.inl i))).snd) =
      Matrix.of fun i j => (ev (frX (w (.inl (o j))) ≫ TF.Y.j) U.1 (hwU _) (x i)).snd := by
    ext i j
    exact congrArg TrivSqZeroExt.snd ((FlagMod.ev_appLE _ _ hc.2.1 _ (eb _ ▸ hwU _) _).trans
      (congrArg (· (x i)) (FlagMod.ev_congr (eb _) _ _ _)))
  rw [e₁, hblock, e₂, map_diagUnit (ev z W hzW) L hc.2.2.2.2.1 t ht] at key
  have hca : ev z W' hz ac = (a : K) := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
    exact map_ratCast ((ev z W' hz).comp (algX (str₀ TF.X Z) W')) a
  rw [FlagMod.ev_res _ hW'W hz hzW, FlagMod.ev_appLE _ _ hc.2.1 _ (eP ▸ hU), FlagMod.ev_congr eP _ _ hU, hh,
    map_mul, map_mul, hca, FlagMod.ev_res _ hW'W hz hzW, mul_assoc, mul_assoc]
  exact congrArg _ ((mul_comm _ _).trans key)

section Main

open ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 800000 in

theorem simple_pole : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ y _ V hy t ht₁ ht₂
  obtain ⟨W, hyW, hWV, i, k, δ, u, hi, hk, hu, h₁, h₂, h₃⟩ := exists_pole hP TF Z hF hKS hV ω₀ y V hy
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) :=
    haveI := (TF.X.normal (inc₀ TF.X Z y)).1
    MulEquiv.isDomain _ (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  obtain ⟨V', hyV', hV', b, hb, e⟩ := exists_unit_mul y hyW (resG _ hWV t) δ
    (by rw [ger_resG]; exact ger_ne_zero (dense_U₀ TF.X Z) t (fun z hz h => (ht₁ z hz).2 h) y _)
    (by rw [ger_resG]; exact ht₂ W hWV δ (fun z hz h hu => h ((h₁ z hz).1 hu)) y hyW)
    (h₂ W le_rfl _ (fun z hz h hu => h ((ht₁ z (hWV hz)).1 (by rwa [ger_resG] at hu))) y hyW)
  refine ⟨V', hyV', hV'.trans hWV, i, k, b * resG _ hV' u, hV'.trans hi, hV'.trans hk, fun z hz => ?_,
    fun z hz ho hc => ?_⟩
  · rw [map_mul]
    exact (hb z hz).mul ((hu.map _).map _)
  let O : (Y₀ TF.X Z).Opens := ksOpen (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) i k
  let ω : Γ(Y₀ TF.X Z, O) := ω₀.ω.loc (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k)
  have e₁ : resG _ (inf_le_left : W ⊓ O ≤ W) δ * resG _ inf_le_right ω = resG _ inf_le_left u := by
    refine FlagMod.ext_ev_field fun K _ p hp => ?_
    have a₁ := FlagMod.le_preimage_mono inf_le_left hp
    have a₂ := FlagMod.le_preimage_mono inf_le_right hp
    rw [map_mul, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₂]
    exact h₃ K p a₁ (FlagMod.le_preimage_mono inf_le_left a₂) (FlagMod.le_preimage_mono inf_le_right a₂)
  have hzO : z ∈ O := ⟨ho, hc⟩
  have hm : z ∈ W ⊓ O := ⟨hV' hz, hzO⟩
  have e₂ := congrArg (ger z hm) e₁
  have e₃ := congrArg (ger z hz) e
  simp only [map_mul, ger_resG] at e₂ e₃
  change ger (Y := Y₀ TF.X Z) z _ t * ger (Y := Y₀ TF.X Z) z hzO ω = ger (Y := Y₀ TF.X Z) z hz _
  rw [map_mul, ger_resG, e₃, mul_assoc, e₂]

end Main

end GlobalTheory.LogPole
