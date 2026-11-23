import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurve
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.CxPts

namespace GlobalTheory.CoverHodge

theorem g_eq {S S' : Scheme.{0}} [Nonempty S'] {P : PPAS S} {P' : PPAS S'} {f : S' ⟶ S}
    {φ : P'.A.left ⟶ P.A.left} (h : P'.IsPull P f φ) : P'.g = P.g := by
  have hm := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1.1 P.smoothDim
  exact H1.dim_unique P'.A.hom P'.smoothDim hm (LieVB.unitSec P'.A (Classical.arbitrary S'))

theorem eq_deg_mul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]
    (C : RegCover p) {E : X.Modules} {E' : C.Y.Modules} {r : ℕ} {h : VMetric p E r}
    {h' : VMetric (C.ρ ≫ p) E' r} {α : (Scheme.Modules.pullback C.ρ).obj E ≅ E'}
    (H : (h.pull C.ρ rfl).IsIsometry h' α) {a c : ℝ} (hc : h.IsCh2Deg c) (ha : h'.IsCh2Deg a) :
    a = C.deg * c := by
  obtain ⟨⟨M'⟩, ha⟩ := ha
  have w₁ : (M'.ρ ≫ C.ρ) ≫ p = M'.ρ ≫ (C.ρ ≫ p) := Category.assoc _ _ _
  have I := IsometryPullback.isIsometry_trans (IsometryPullback.isIsometry_symm (IsometryPullback.isIsometry_pull H M'.ρ rfl))
    ((VMetric.isIsometry_pull_id_comp k X p E r h).2 C.Y M'.Y (C.ρ ≫ p) _ C.ρ M'.ρ rfl rfl w₁)
  have hC : (h.pull (M'.ρ ≫ C.ρ) w₁).IsCInf := by
    rw [(VMetric.isIsometry_iff _).1 I]
    exact M'.cInf.map _
  have hd : (M'.ρ ≫ C.ρ).residueDegree (genericPoint M'.Y) = M'.deg * C.deg := by
    rw [CurveDegreesCompare.residueDegree_comp, M'.generic]
    simp [RegCover.deg, mul_comm]
  obtain ⟨M, h₁, h₂⟩ := IsometryPullback.exists_flagModel_of_eq (M'.ρ ≫ C.ρ) w₁ M'.reg
    (by rw [Scheme.Hom.comp_apply, M'.generic, C.generic])
    (hd.trans_ne (Nat.mul_ne_zero M'.deg_pos.ne' C.deg_pos.ne')) hC (M'.flag.ofIso _)
  have e₁ := (h₂ _).1 (hc.2 M)
  have e₂ := (VMetric.isFlagCh2_ofIso k _ _ _ _ r _ _ _ M'.cInf hC M'.flag _ I).2 e₁
  have e₃ := (ha M').unique M'.reg.toIsArithVar e₂
  rw [RegCover.deg, h₁, hd] at e₃
  push_cast at e₃
  have hpos : (M'.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M'.deg_pos.ne'
  have := mul_left_cancel₀ hpos (e₃.trans (mul_assoc _ _ _))
  exact this

open GlobalTheory.RatFibreDeg in

theorem ratDeg_pull_of_isFinite {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k)
    [IsIntegral X] [IsIntegral Y] (ν : Y ⟶ X) [IsFinite (ratFibre.map p ν)]
    (hX : IsProjCurve ℚ (ratFibre p)) (hY : IsProjCurve ℚ (ratFibre (ν ≫ p)))
    (hν : ν (genericPoint Y) = genericPoint X) (L : LB X) (hL : L.IsLB) :
    ratDeg (ν ≫ p) (L.pull ν) = (ν.residueDegree (genericPoint Y) : ℤ) * ratDeg p L := by
  have := hX.isIntegral
  have := hY.isIntegral
  have := flat_fst p
  have := flat_fst (ν ≫ p)
  have := isPreimmersion_fst p
  have := isPreimmersion_fst (ν ≫ p)
  have e := ratFibre.map_fst p ν
  have gX := apply_genericPoint_of_flat (ratFibre.fst p)
  have gY := apply_genericPoint_of_flat (ratFibre.fst (ν ≫ p))
  have hg : ratFibre.map p ν (genericPoint _) = genericPoint _ := by
    refine (ratFibre.fst p).isEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, gY, hν, gX]
  have hr : (ratFibre.map p ν).residueDegree (genericPoint _) =
      ν.residueDegree (genericPoint Y) := by
    have h₁ := CurveDegreesCompare.residueDegree_comp (ratFibre.map p ν) (ratFibre.fst p)
      (genericPoint _)
    rw [e, CurveDegreesCompare.residueDegree_comp, gY] at h₁
    simpa only [residueDegree_of_surjectiveOnStalks, mul_one, one_mul] using h₁.symm
  have hf (r : ℚ) : (ratFibre.map p ν).appTop (algebraMap ℚ Γ(ratFibre p, ⊤) r) =
      algebraMap ℚ Γ(ratFibre (ν ≫ p), ⊤) r :=
    RingHom.congr_fun (RingHom.ext_rat ((ratFibre.map p ν).appTop.hom.comp (algebraMap ℚ _))
      (algebraMap ℚ _)) r
  have hN := Semi.LB.isLB_pull hL (ratFibre.fst p)
  have hM := Semi.LB.isLB_pull hL ν
  have h₁ := ProjFin.interNumOn_eq_residueDegree_mul ℚ _ _ (ratFibre.map p ν) hX.isProjOver
    hX.dim_eq hg _ hN
  have h₂ := interNumOn_eq_interNum_pull (k := ℚ) (L := ![L.pull (ratFibre.fst p)]) hf
    (fun i => by fin_cases i; exact hN)
  have hM' := Semi.LB.isLB_pull hM (ratFibre.fst (ν ≫ p))
  rw [ratDeg_eq_degLB hM, ratDeg_eq_degLB hL, hX.degLB_eq_interNum hN, hY.degLB_eq_interNum hM',
    ← hr, ← h₁, h₂]
  refine interNum_congr_cls _ _ (fun i => by fin_cases i; exact hM')
    (fun i => by fin_cases i; exact Semi.LB.isLB_pull hN _) fun i => ?_
  fin_cases i
  refine (CechPic.cls_pull hM _ _).trans (Eq.trans ?_ (CechPic.cls_pull hN _ _).symm)
  rw [CechPic.cls_pull hL ν hM, CechPic.cls_pull hL _ hN, ← CechPic.pull_comp, ← CechPic.pull_comp, e]

open GlobalTheory.RatFibreDeg in

theorem isFinite_ratFibre_map {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    [IsIntegral X] (hX : IsArithVar p 1) (C : RegCover p) : IsFinite (ratFibre.map p C.ρ) := by
  have hY : IsArithVar (C.ρ ≫ p) 1 := C.reg.toIsArithVar
  have cX := GlobalTheory.T.rational_fibre_projective_curve k X p hX
  have cY := GlobalTheory.T.rational_fibre_projective_curve k C.Y (C.ρ ≫ p) hY
  have := cX.isIntegral
  have := cY.isIntegral
  have hPX : IsProper (ratFibre.snd p) :=
    ratFibre.strHom_eq p ▸ (isProper_and_exists_isAmpleLB_of_isProjOver cX.isProjOver).1
  have hPY : IsProper (ratFibre.snd (C.ρ ≫ p)) :=
    ratFibre.strHom_eq (C.ρ ≫ p) ▸ (isProper_and_exists_isAmpleLB_of_isProjOver cY.isProjOver).1
  have : IsProper (ratFibre.map p C.ρ ≫ ratFibre.snd p) := by rw [ratFibre.map_snd]; exact hPY
  have : IsProper (ratFibre.map p C.ρ) := .of_comp _ (ratFibre.snd p)
  have := cY.isProperCurve.isNoetherian
  have := flat_fst p
  have := flat_fst (C.ρ ≫ p)
  have := isPreimmersion_fst p
  have e := ratFibre.map_fst p C.ρ
  have gX := apply_genericPoint_of_flat (ratFibre.fst p)
  have gY := apply_genericPoint_of_flat (ratFibre.fst (C.ρ ≫ p))
  have hg : ratFibre.map p C.ρ (genericPoint _) = genericPoint _ := by
    refine (ratFibre.fst p).isEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, gY, C.generic, gX]
  obtain ⟨x₀, hx₀⟩ := ProperCurve.exists_ne_genericPoint cY.dim_eq
  have : LocallyQuasiFinite (ratFibre.map p C.ρ) :=
    ProperCurve.locallyQuasiFinite_of_ne cY.dim_eq _ (x₀ := x₀) (by
      rw [hg]
      intro he
      have hc : IsClosed ({genericPoint (ratFibre p)} : Set (ratFibre p)) := by
        rw [← he, ← Set.image_singleton]
        exact (ratFibre.map p C.ρ).isClosedMap _ (ProperCurve.isClosed_singleton cY.dim_eq hx₀)
      obtain ⟨y, hy⟩ := ProperCurve.exists_ne_genericPoint cX.dim_eq
      exact hy ((genericPoint_specializes y).mem_closed hc (Set.mem_singleton _)))
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem cxDeg_pull {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]
    (hX : IsArithVar p 1) (C : RegCover p) {E : X.Modules} {r : ℕ} (hE : IsVB E r) :
    cxDeg (C.ρ ≫ p) ((Scheme.Modules.pullback C.ρ).obj E) r = C.deg * cxDeg p E r := by
  have hY : IsArithVar (C.ρ ≫ p) 1 := C.reg.toIsArithVar
  have cX := GlobalTheory.T.rational_fibre_projective_curve k X p hX
  have cY := GlobalTheory.T.rational_fibre_projective_curve k C.Y (C.ρ ≫ p) hY
  have := isFinite_ratFibre_map hX C
  have := cY.isIntegral
  have hE' := hE.pullback C.ρ
  rw [ChernDegree.cxDeg_eq_ratDeg hY hE', ChernDegree.cxDeg_eq_ratDeg hX hE]
  have hA := Semi.LB.isLB_pull hE.isLB_det C.ρ
  have c : CechPic.cls _ hA = CechPic.cls _ hE'.isLB_det :=
    (CechPic.cls_eq_iff hA hE'.isLB_det).2 (hE.lbIso_det_pullback C.ρ)
  have hA' := Semi.LB.isLB_pull hA (ratFibre.fst (C.ρ ≫ p))
  have hB' := Semi.LB.isLB_pull hE'.isLB_det (ratFibre.fst (C.ρ ≫ p))
  have i : LBIso ((LB.pull (det E r) C.ρ).pull (ratFibre.fst (C.ρ ≫ p)))
      ((det ((Scheme.Modules.pullback C.ρ).obj E) r).pull (ratFibre.fst (C.ρ ≫ p))) := by
    refine (CechPic.cls_eq_iff hA' hB').1 ?_
    rw [CechPic.cls_pull hA _ hA', CechPic.cls_pull hE'.isLB_det _ hB', c]
  rw [ratDeg_eq_degLB hE'.isLB_det, ← degLB_congr hA' hB' i, ← ratDeg_eq_degLB hA,
    ratDeg_pull_of_isFinite p C.ρ cX cY C.generic _ hE.isLB_det]
  rfl

theorem degOmega_ch2Omega_cover : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ (P : PPAS X) (C : RegCover p) (P' : PPAS C.Y) (φ : P'.A.left ⟶ P.A.left), P'.IsPull P C.ρ φ → P'.degOmega (C.ρ ≫ p) = C.deg * P.degOmega p ∧ ∀ a : ℝ, P'.IsCh2Omega (C.ρ ≫ p) a → P.IsCh2Omega p (a / C.deg) := by
  intro HP HR k _ X p _ hX P C P' φ hP
  haveI : Nonempty C.Y := ⟨genericPoint C.Y⟩
  have hg : P'.g = P.g := g_eq hP
  refine ⟨?_, ?_⟩
  · rw [PPAS.degOmega, PPAS.degOmega, ← cxDeg_congr (ShFam.Pad.omegaPullIso hP), hg]
    exact cxDeg_pull hX C P.isVB_omega
  · rintro a ⟨h', H', ha⟩
    obtain ⟨h, H, -, hc, -⟩ := PPAS.exists_isHodge_ch2Omega HP.p4 k X p
      (fun Y q _ hq => GlobalTheory.RegCoverExists.nonempty_regCover HR k Y q hq) hX P
    have I := HodgePull.form_omegaBase k X p C.Y (C.ρ ≫ p) C.ρ rfl P P' φ hP.1 hg hP _ h h' H H'
    clear H'
    revert h'
    rw [hg]
    intro h' ha I
    have e := eq_deg_mul C (α := ShFam.Pad.omegaPullIso hP) I hc ha
    rw [e, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 C.deg_pos.ne')]
    exact ⟨h, H, hc⟩

end GlobalTheory.CoverHodge
