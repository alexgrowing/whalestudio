import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGoodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTupleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrameStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.DualType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.StepLaw (ResAt UnrOff)

variable {D : D7} {S T : HSp D}

open Classical in
theorem dualTypePlaces_isSplitNonconjugate_of_admissible {B : Base S T} {Q : Finset (Pl D.host.E)} (h : B.admitted Q) : SplitSet (allP B Q) := by
  obtain ⟨P, h1, h2, hP⟩ := h.1.split
  exact hP.mono (Finset.union_subset h1 h2)

theorem char_laws (B : Base S T) (hB : B.Good) (ν : Twist D Circle) (hν : ν.Good) (hQ : B.admitted ν.Q) :
    (∀ PP ∈ allP B ν.Q, ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧ ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧
      UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) :=
  GlobalTheory.T.dualType_residueChars_unramified_tuple B hB ν hν hQ

theorem om_theta_move {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ Φ Φ' f f' : WO S T → ℂ}
    (hth : ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm →
      ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ))
    (hΘ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f)
    (hΘ' : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ' f')
    {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {c c' : ℂ} (hc : c ≠ 0) (hf₀ : om (g, h) f₀ = c • f₀)
    (hΦ : ∀ x, Φ' x = c' * Φ (actO S T g h x)) : om (g, h) f' = (c * c') • f := by
  open GlobalTheory.ThetaMove GlobalTheory.SplitHecke in
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hΘ
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))
  have hT' : ∀ Ψ, Tm' Ψ = c⁻¹ • om (g, h) (Tm fun t => Ψ (actO S T g h t)) := fun Ψ => rfl
  have hP : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.trans _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hx)
      simp only [act_add, act_act_inv] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have hΨ' := isSBHalf_comp g h hΛ hΨ
      have h1 := hTm.modul _ hΨ' _ (isHalf_actO g⁻¹ h⁻¹ hy)
      have h2 : ∀ t, symplO S T t (actO S T g⁻¹ h⁻¹ y) = symplO S T (actO S T g h t) y := fun t => by
        rw [← symplO_actO S T g h, act_act_inv]
      simp only [h2] at h1
      rw [hT', hT', h1, hom.om_heis _ _ _ _ (hth Tm hTm _ hΨ'), act_act_inv, heisO_smul']
    · have h1 := hTm.vac
      rw [one_smul] at h1 ⊢
      have h2 : (fun t => halfInd e Λ (actO S T g h t)) = halfInd e Λ := funext (halfInd_act g h hΛ)
      rw [hT', h2, h1, hf₀, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have e2 : f = Tm' Φ := hall Tm' hP
  have e1 : f' = Tm Φ' := hΘ'.2 Tm hTm
  have e3 : Φ' = c' • fun t => Φ (actO S T g h t) := funext hΦ
  rw [hT'] at e2
  have e4 : om (g, h) (Tm fun t => Φ (actO S T g h t)) = c • f := by
    rw [e2, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [e1, e3, map_smul, map_smul, e4, smul_smul, mul_comm]

theorem om_vac_base {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ν : Twist D Circle} (hν : ν.Good) (hQ : B.admitted ν.Q)
    {ω : PairRep S T} (hω : B.IsWeil ν.chi ω) {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T)
    (sg : Lev.finE S g ∈ St B.F.βS) (sh : Lev.finE T h ∈ St B.F.βT) :
    ω (g, h) B.F.f₀ = ((vacC B ν g h : ℂˣ) : ℂ) • B.F.f₀ := by
  obtain ⟨h1, h2, h3⟩ := char_laws B hB ν hν hQ
  have hF := hB.frame
  exact GlobalTheory.StepVecLaw.om_vac hω hS hB.sigOK (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hF.onbS τ)) hF.cartT hF.sdS hF.sdT hF.frS hF.frT
    hF.vac (dualTypePlaces_isSplitNonconjugate_of_admissible hQ).isIdemSum (fun PP hP => (h1 PP hP).1) (fun PP hP => (h1 PP hP).2) h2 h3 hg hh sg sh

open Classical in

theorem om_vec_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {ν : Twist D Circle} (hν : ν.Good) (hQ : B.admitted ν.Q)
    {ω : PairRep S T} (hω : B.IsWeil ν.chi ω) {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T)
    (sg : Lev.finE S g ∈ St B.F.βS) (sh : Lev.finE T h ∈ St B.F.βT)
    {φ φ' : ∀ PP : ↥ν.Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ} {c' : ℂ}
    (hD : ∀ x, B.F.datumFn B.G (B.de.Q ∪ ν.Q) (B.locFn ν.Q φ') x =
      c' * B.F.datumFn B.G (B.de.Q ∪ ν.Q) (B.locFn ν.Q φ) (actO S T g h x)) :
    ω (g, h) (B.vecAt ν.Q φ') = (((vacC B ν g h : ℂˣ) : ℂ) * c') • B.vecAt ν.Q φ := by
  have hF := hB.frame
  have hsq : (halfIdem B.G.Pg (B.de.Q ∪ ν.Q)) * (halfIdem B.G.Pg (B.de.Q ∪ ν.Q)) = halfIdem B.G.Pg (B.de.Q ∪ ν.Q) :=
    hQ.1.isOrthSum.1.idem
  refine om_theta_move hω (fun Tm hT Ψ hΨ => GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D _ hF.vac.1 S T _ _ hF.sdS hF.sdT _ hsq hQ.1.isOrthSum.1.infPart_eq _
      hF.vac.2.theta Tm hT Ψ hΨ) (Base.isThetaAt_vecAt hB hQ φ) (Base.isThetaAt_vecAt hB hQ φ')
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D S T _ _ _ _ hF.sdS hF.sdT hF.frS hF.frT g h sg sh) (Units.ne_zero _) (om_vac_base hB hS hν hQ hω hg hh sg sh) hD

section Datum

theorem frMapO_act (F : Frame S T) {g : GA D S} {h : GA D T} (sg : Lev.finE S g ∈ St F.βS) (sh : Lev.finE T h ∈ St F.βT) (x : WO S T) :
    (IsIntM (frMapO S T F.βS F.βT (actO S T g h x)) ↔ IsIntM (frMapO S T F.βS F.βT x)) ∧
      (IsIntM (frMapO S T F.βS F.βT x) → ∀ PP : Pl D.host.E, redM PP (frMapO S T F.βS F.βT (actO S T g h x)) =
        (redFn F.βT PP (Lev.finE T h)).val * redM PP (frMapO S T F.βS F.βT x) * ((redFn F.βS PP (Lev.finE S g))⁻¹).val) := by
  have sg' : Lev.finE S g⁻¹ ∈ St F.βS := by rw [map_inv]; exact inv_mem sg
  have sh' : Lev.finE T h⁻¹ ∈ St F.βT := by rw [map_inv]; exact inv_mem sh
  have := GlobalTheory.FrameRed.frMapO_actO_int_red D S T F.βS F.βT g⁻¹ h⁻¹ sg' sh' x
  rw [inv_inv, inv_inv] at this
  refine ⟨this.1, fun hx PP => ?_⟩
  rw [this.2 hx PP, map_inv, map_inv, redFn_inv sh PP, redFn_inv sg PP, inv_inv]

theorem frMapAdj_act (F : Frame S T) {g : GA D S} {h : GA D T} (sg : Lev.finE S g ∈ St F.βS) (sh : Lev.finE T h ∈ St F.βT) (x : WO S T) :
    (IsIntM (frMapAdj S T F.βS F.βT (actO S T g h x)) ↔ IsIntM (frMapAdj S T F.βS F.βT x)) ∧
      (IsIntM (frMapAdj S T F.βS F.βT x) → ∀ PP : Pl D.host.E, redM PP (frMapAdj S T F.βS F.βT (actO S T g h x)) =
        (redFn F.βS PP (Lev.finE S g)).val * redM PP (frMapAdj S T F.βS F.βT x) * ((redFn F.βT PP (Lev.finE T h))⁻¹).val) := by
  have sg' : Lev.finE S g⁻¹ ∈ St F.βS := by rw [map_inv]; exact inv_mem sg
  have sh' : Lev.finE T h⁻¹ ∈ St F.βT := by rw [map_inv]; exact inv_mem sh
  refine ⟨⟨fun hx => ?_, fun hx => (GlobalTheory.AdjDatumMove.red_actO S T _ _ sg sh hx).1⟩,
    fun hx PP => (GlobalTheory.AdjDatumMove.red_actO S T _ _ sg sh hx).2 PP⟩
  have := (GlobalTheory.AdjDatumMove.red_actO S T _ _ sg' sh' hx).1
  rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this

open Classical in

theorem datumFn_act (F : Frame S T) (G : TypeDat D T.rank) (Q' : Finset (Pl D.host.E)) {g : GA D S} {h : GA D T}
    (sg : Lev.finE S g ∈ St F.βS) (sh : Lev.finE T h ∈ St F.βT) {ω ω' : Reds D T.rank S.rank → ℂ} {a b : ℂ}
    (hA : ∀ y : Reds D S.rank T.rank, omegaG G.levT G.muC (fun PP => (redFn F.βS PP (Lev.finE S g)).val * y PP *
      ((redFn F.βT PP (Lev.finE T h))⁻¹).val) = a * omegaG G.levT G.muC y)
    (hB : ∀ y : Reds D T.rank S.rank, ω (fun PP => (redFn F.βT PP (Lev.finE T h)).val * y PP *
      ((redFn F.βS PP (Lev.finE S g))⁻¹).val) = b * ω' y) (x : WO S T) :
    F.datumFn G Q' ω (actO S T g h x) = a * b * F.datumFn G Q' ω' x := by
  have hO := frMapO_act F sg sh x
  have hJ := frMapAdj_act F sg sh x
  have hH : IsHalf (halfIdem G.Pg Q') (actO S T g h x) ↔ IsHalf (halfIdem G.Pg Q') x :=
    ⟨GlobalTheory.ThetaMove.isHalf_of_act g h, GlobalTheory.AdjDatumMove.isHalf_actO' g h⟩
  unfold Frame.datumFn
  simp only [hH, hO.1, hJ.1]
  by_cases c1 : IsHalf (halfIdem G.Pg Q') x ∧ IsIntM (frMapAdj S T F.βS F.βT x)
  · by_cases c2 : IsHalf (halfIdem G.Pg Q') x ∧ IsIntM (frMapO S T F.βS F.βT x)
    · rw [if_pos c1, if_pos c2, if_pos c1, if_pos c2, funext (hJ.2 c1.2), funext (hO.2 c2.2), hA, hB]
      ring
    · rw [if_neg c2, if_neg c2]; ring
  · rw [if_neg c1, if_neg c1]; ring

variable {n r : ℕ}

theorem blockTri_blkOf_one_top {κ : Type} [CommRing κ] (g : GL (Fin r) κ) : g ∈ blockTri (blkOf r 1) := by
  refine mem_blockTri.2 fun i j h => ?_
  simp [blkOf] at h

open Classical in

theorem omegaG_levT_of (G : TypeDat D r) {y : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)}
    (h0 : ∀ PP ∈ G.Pg, LowZero r (y PP)) (g : G0 G.Pg r) (hg : ∀ PP : ↥G.Pg, (g PP).val = topL r (y PP.1)) (hH : g ∈ G.P.H) :
    omegaG G.levT G.muC y = ((G.P.chi ⟨g, hH⟩ : ℂˣ) : ℂ) *
      ∏ PP : ↥G.Pg, (((G.muC PP.1 (GeneralLinearGroup.det (g PP)) : ℂˣ)) : ℂ)⁻¹ := by
  have hr : ∀ g' : G0 G.Pg r, (fun PP => upperLeftBlock (le_refl r) (g' PP)) = g' := fun g' => funext fun PP => GlobalTheory.AdjDatumMove.restrictedBlock_self_apply _
  have hex : (∀ PP ∈ G.levT.Pg, LowZero r (y PP)) ∧
      ∃ g' : ∀ PP : ↥G.levT.Pg, GL (Fin r) (kP PP.1), (∀ PP : ↥G.levT.Pg, ((g' PP : GL (Fin r) _) : Matrix (Fin r) (Fin r) _) = topL r (y PP.1)) ∧
        (∀ PP : ↥G.levT.Pg, g' PP ∈ blockTri (blkOf G.levT.r G.levT.t)) ∧ (fun PP => upperLeftBlock G.levT.hr (g' PP)) ∈ G.levT.P.H :=
    ⟨h0, g, hg, fun PP => blockTri_blkOf_one_top _, by show (fun PP : ↥G.Pg => upperLeftBlock (le_refl r) (g PP)) ∈ G.P.H; rw [hr]; exact hH⟩
  unfold omegaG
  rw [dif_pos hex]
  have e : hex.2.choose = g := funext fun PP => Units.ext ((hex.2.choose_spec.1 PP).trans (hg PP).symm)
  have e2 : (⟨fun PP => upperLeftBlock G.levT.hr (hex.2.choose PP), hex.2.choose_spec.2.2⟩ : G.levT.P.H) = ⟨g, hH⟩ :=
    Subtype.ext ((hr _).trans e)
  rw [e2, e]
  simp [TypeDat.levT]
  rfl

open Classical in
theorem omegaG_levT_zero (G : TypeDat D r) {y : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)}
    (h : ¬ ((∀ PP ∈ G.Pg, LowZero r (y PP)) ∧ ∃ g : G0 G.Pg r, (∀ PP : ↥G.Pg, (g PP).val = topL r (y PP.1)) ∧ g ∈ G.P.H)) :
    omegaG G.levT G.muC y = 0 := by
  unfold omegaG
  refine dif_neg fun h' => h ⟨h'.1, ?_⟩
  obtain ⟨g, h1, -, h3⟩ := h'.2
  refine ⟨g, h1, ?_⟩
  rwa [show (fun PP => upperLeftBlock G.levT.hr (g PP)) = g from funext fun PP => GlobalTheory.AdjDatumMove.restrictedBlock_self_apply _] at h3

open Classical in

theorem omegaG_levT_mul (G : TypeDat D r) (hr : r ≤ n) (K : ∀ PP : Pl D.host.E, GL (Fin n) (kP PP))
    (hK : ∀ PP ∈ G.Pg, K PP ∈ blockTri (blk2 r)) (a : G0 G.Pg r) (ha : ∀ PP : ↥G.Pg, a PP = upperLeftBlock hr (K PP.1)) (hH : a ∈ G.P.H)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaG G.levT G.muC (fun PP => (K PP).val * y PP) = (((G.P.chi ⟨a, hH⟩ : ℂˣ) : ℂ) *
      ∏ PP : ↥G.Pg, (((G.muC PP.1 (GeneralLinearGroup.det (a PP)) : ℂˣ)) : ℂ)⁻¹) * omegaG G.levT G.muC y := by
  have eK : ∀ PP (u : Matrix (Fin n) (Fin r) (kP PP)), (K PP).val * u = (K PP).val * u * ((1 : GL (Fin r) (kP PP))).val := fun PP u => by
    rw [Units.val_one, Matrix.mul_one]
  have low : ∀ PP ∈ G.Pg, ∀ u : Matrix (Fin n) (Fin r) (kP PP), LowZero r ((K PP).val * u) ↔ LowZero r u := fun PP hP u => by
    rw [eK]; exact GlobalTheory.AdjDatumMove.lowZero_mul_iff (hK PP hP) 1 u
  have top : ∀ PP : ↥G.Pg, LowZero r (y PP.1) → topL r ((K PP.1).val * y PP.1) = (a PP).val * topL r (y PP.1) := fun PP hu => by
    have := GlobalTheory.AdjDatumMove.topL_mul hr (hK PP.1 PP.2) 1 hu
    rw [Matrix.mul_one, Matrix.mul_one] at this
    rw [this, ha]
  by_cases hy : (∀ PP ∈ G.Pg, LowZero r (y PP)) ∧ ∃ g : G0 G.Pg r, (∀ PP : ↥G.Pg, (g PP).val = topL r (y PP.1)) ∧ g ∈ G.P.H
  · obtain ⟨h0, g, hg, hgH⟩ := hy
    rw [omegaG_levT_of G h0 g hg hgH,
      omegaG_levT_of G (fun PP hP => (low PP hP _).2 (h0 PP hP)) (a * g)
        (fun PP => by rw [top PP (h0 PP.1 PP.2), ← hg PP]; rfl) (mul_mem hH hgH)]
    have e : (⟨a * g, mul_mem hH hgH⟩ : G.P.H) = ⟨a, hH⟩ * ⟨g, hgH⟩ := rfl
    rw [e, map_mul, Units.val_mul]
    have e2 : ∀ PP : ↥G.Pg, (((G.muC PP.1 (GeneralLinearGroup.det ((a * g) PP)) : ℂˣ)) : ℂ)⁻¹ =
        (((G.muC PP.1 (GeneralLinearGroup.det (a PP)) : ℂˣ)) : ℂ)⁻¹ * (((G.muC PP.1 (GeneralLinearGroup.det (g PP)) : ℂˣ)) : ℂ)⁻¹ := fun PP => by
      rw [Pi.mul_apply, map_mul, map_mul, Units.val_mul, mul_inv]
    rw [Finset.prod_congr rfl fun PP _ => e2 PP, Finset.prod_mul_distrib]
    ring
  · rw [omegaG_levT_zero G hy, mul_zero]
    refine omegaG_levT_zero G fun h => hy ?_
    obtain ⟨h0, g, hg, hgH⟩ := h
    have h0' : ∀ PP ∈ G.Pg, LowZero r (y PP) := fun PP hP => (low PP hP _).1 (h0 PP hP)
    refine ⟨h0', a⁻¹ * g, fun PP => ?_, mul_mem (inv_mem hH) hgH⟩
    have := (hg PP).trans (top PP (h0' PP.1 PP.2))
    show ((a PP)⁻¹ * g PP).val = _
    rw [Units.val_mul, this, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

end Datum

section Source

variable {k R : Type} [CommRing k] [CommRing R] {n r : ℕ}

theorem flat_mul_inv (hr : r ≤ n) (ν : kˣ →* Rˣ) {K : GL (Fin n) k} (hK : K ∈ blockTri (blk2 r)) (y : Matrix (Fin r) (Fin n) k) :
    flat ν (y * (K⁻¹).val) = ((ν (GeneralLinearGroup.det (upperLeftBlock hr K)))⁻¹ : Rˣ) * flat ν y := by
  have hK' : K⁻¹ ∈ blockTri (blk2 r) := inv_mem hK
  have htop : topL r (y * (K⁻¹).val) = topL r y * (upperLeftBlock hr K⁻¹).val := by
    rw [upper_block_val_submatrix hr hK']
    ext i j
    have hi : i.val < r ∧ j.val < n := ⟨i.2, lt_of_lt_of_le j.2 hr⟩
    have hi' : ∀ l : Fin r, i.val < r ∧ l.val < n := fun l => ⟨i.2, lt_of_lt_of_le l.2 hr⟩
    simp only [topL, dif_pos hi, Matrix.mul_apply, dif_pos (hi' _), Matrix.submatrix_apply]
    refine (Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ (fun l hl => ?_) (fun l => ?_)).symm
    · have hl' : ¬ l.val < r := fun h => hl ⟨⟨l.val, h⟩, by ext; rfl⟩
      rw [mem_blockTri.1 hK' l ⟨j.val, hi.2⟩ (by simp [blk2, hl', j.2]), mul_zero]
    · rfl
  have hinv : upperLeftBlock hr K⁻¹ = (upperLeftBlock hr K)⁻¹ := extendOne_inv _ hK
  by_cases h : IsUnit (topL r y).det
  · obtain ⟨u, hu⟩ := h
    rw [flat_of_isUnit ν hu.symm, flat_of_isUnit ν (u := u * GeneralLinearGroup.det (upperLeftBlock hr K)⁻¹)
      (by rw [htop, det_mul, ← hu, hinv]; rfl), map_mul, Units.val_mul, mul_comm, map_inv, map_inv]
  · rw [flat_of_not_isUnit ν h, flat_of_not_isUnit, mul_zero]
    rw [htop, det_mul]
    exact fun h' => h (isUnit_of_mul_isUnit_left h')

end Source

section T0

variable {B : Base S T}

theorem finE_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (PP : Pl D.host.E) : redFn β PP (Lev.finE V 1) = 1 := by
  rw [map_one, redFn_one]

theorem one_mem_St (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Lev.finE V 1 ∈ St β := by
  rw [map_one]; exact one_mem _

def blkA (B : Base S T) (k : GA D S) (PP : Pl D.host.E) : (kP PP)ˣ :=
  GeneralLinearGroup.det (upperLeftBlock B.hr (redFn B.F.βS PP (Lev.finE S k)))

open Classical in

def srcC (B : Base S T) (ψ : Twist D Circle) (k : GA D S)
    (hk : Lev.finE S k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS ψ)) : ℂˣ :=
  B.G.P.chi ⟨rTup B.F.βS (B.levS ψ) (Lev.finE S k), hk.2⟩ * (∏ PP ∈ B.G.Pg, (B.G.muC PP (blkA B k PP))⁻¹) *
    ((∏ PP ∈ B.de.Q, (B.de.resC PP (blkA B k PP))⁻¹) * ∏ PP ∈ ψ.Q, (ψ.resC PP (blkA B k PP))⁻¹)

open Classical in
theorem datumFunction_sourceLevel_scalar (B : Base S T) (ψ : Twist D Circle) {k : GA D S}
    (hk : Lev.finE S k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS ψ)) (x : WO S T) :
    B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) (actO S T k 1 x) =
      ((srcC B ψ k hk : ℂˣ) : ℂ) * B.F.datumFn B.G (B.de.Q ∪ ψ.Q) (B.locFn ψ.Q fun PP => flat (ψ.resC PP.1)) x := by
  have hp := Formalism.L2.DIV.lev_le_parLev hk
  have tri : ∀ PP ∈ B.de.Q ∪ ψ.Q, redFn B.F.βS PP (Lev.finE S k) ∈ blockTri (blk2 T.rank) := fun PP hP => parLev_q hp hP
  have triG : ∀ PP ∈ B.G.Pg, redFn B.F.βS PP (Lev.finE S k) ∈ blockTri (blk2 T.rank) := fun PP hP =>
    blockTri_blkOf_le _ _ (parLev_g hp hP)
  have e := datumFn_act B.F B.G (B.de.Q ∪ ψ.Q) (parLev_St hp) (one_mem_St T B.F.βT) (ω := B.locFn ψ.Q fun PP => flat (ψ.resC PP.1))
    (ω' := B.locFn ψ.Q fun PP => flat (ψ.resC PP.1))
    (a := ((B.G.P.chi ⟨rTup B.F.βS (B.levS ψ) (Lev.finE S k), hk.2⟩ : ℂˣ) : ℂ) *
      ∏ PP : ↥B.G.Pg, (((B.G.muC PP.1 (GeneralLinearGroup.det (rTup B.F.βS (B.levS ψ) (Lev.finE S k) PP)) : ℂˣ)) : ℂ)⁻¹)
    (b := (((∏ PP ∈ B.de.Q, (B.de.resC PP (blkA B k PP))⁻¹) * ∏ PP ∈ ψ.Q, (ψ.resC PP (blkA B k PP))⁻¹ : ℂˣ) : ℂ))
    (fun y => by
      simp only [finE_one, inv_one, Units.val_one, Matrix.mul_one]
      exact omegaG_levT_mul B.G B.hr _ triG _ (fun PP => rfl) hk.2 y)
    (fun y => by
      simp only [finE_one, Units.val_one, Matrix.one_mul]
      have h1 : ∀ PP : Pl D.host.E, PP ∈ B.de.Q → flat (B.de.resC PP) (y PP * ((redFn B.F.βS PP (Lev.finE S k))⁻¹).val) =
          (((B.de.resC PP (blkA B k PP))⁻¹ : ℂˣ) : ℂ) * flat (B.de.resC PP) (y PP) := fun PP hP =>
        flat_mul_inv B.hr _ (tri PP (Finset.mem_union_left _ hP)) (y PP)
      have h2 : ∀ PP : ↥ψ.Q, flat (ψ.resC PP.1) (y PP.1 * ((redFn B.F.βS PP.1 (Lev.finE S k))⁻¹).val) =
          (((ψ.resC PP.1 (blkA B k PP.1))⁻¹ : ℂˣ) : ℂ) * flat (ψ.resC PP.1) (y PP.1) := fun PP =>
        flat_mul_inv B.hr _ (tri PP.1 (Finset.mem_union_right _ PP.2)) (y PP.1)
      unfold Base.locFn
      rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl (fun PP _ => h2 PP), Finset.prod_mul_distrib,
        Finset.prod_mul_distrib, Finset.prod_coe_sort ψ.Q (fun PP => (((ψ.resC PP (blkA B k PP))⁻¹ : ℂˣ) : ℂ))]
      simp only [Units.val_mul, Units.coe_prod]
      ring) x
  rw [e]
  congr 1
  unfold srcC
  simp only [Units.val_mul, Units.coe_prod]
  rw [← Finset.prod_coe_sort B.G.Pg (fun PP => (((B.G.muC PP (blkA B k PP))⁻¹ : ℂˣ) : ℂ))]
  rfl

end T0

section Scal

variable {B : Base S T}

open Classical in
theorem prod_allP {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) (f : Pl D.host.E → ℂˣ) :
    ∏ PP ∈ allP B Q, f PP = (∏ PP ∈ B.G.Pg, f PP) * ((∏ PP ∈ B.de.Q, f PP) * ∏ PP ∈ Q, f PP) := by
  unfold allP
  rw [Finset.prod_union hQ.1.disj, Finset.prod_union hQ.2]

open Classical in
theorem resP_g {ν : Twist D Circle} (hQ : B.admitted ν.Q) {PP : Pl D.host.E} (hP : PP ∈ B.G.Pg) : resP B ν PP = B.G.muC PP := by
  have h1 : PP ∉ B.de.Q := fun h => Finset.disjoint_left.1 hQ.1.disj hP (Finset.mem_union_left _ h)
  have h2 : PP ∉ ν.Q := fun h => Finset.disjoint_left.1 hQ.1.disj hP (Finset.mem_union_right _ h)
  simp [resP, Twist.locC, hP, h1, h2]

open Classical in
theorem resP_d {ν : Twist D Circle} (hQ : B.admitted ν.Q) {PP : Pl D.host.E} (hP : PP ∈ B.de.Q) : resP B ν PP = B.de.resC PP := by
  have h1 : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_left _ hP)
  have h2 : PP ∉ ν.Q := fun h => Finset.disjoint_left.1 hQ.2 hP h
  simp [resP, Twist.locC, hP, h1, h2]

open Classical in
theorem resP_q {ν : Twist D Circle} (hQ : B.admitted ν.Q) {PP : Pl D.host.E} (hP : PP ∈ ν.Q) : resP B ν PP = ν.resC PP := by
  have h1 : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_right _ hP)
  have h2 : PP ∉ B.de.Q := fun h => Finset.disjoint_left.1 hQ.2 h hP
  simp [resP, Twist.locC, hP, h1, h2]

open Classical in
theorem resP_dq {ν : Twist D Circle} (hQ : B.admitted ν.Q) {PP : Pl D.host.E} (hP : PP ∈ B.de.Q ∪ ν.Q) :
    resP B ν PP = B.de.locC PP * ν.locC PP := by
  have h1 : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.1 hQ.1.disj h hP
  simp [resP, h1]

open Classical in

theorem levFn_eq {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {k : GA D S}
    (hk : Lev.finE S k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS ψ)) :
    levFn B.F.βS (B.levS ψ) (Lev.finE S k) = B.G.P.chi ⟨rTup B.F.βS (B.levS ψ) (Lev.finE S k), hk.2⟩ *
      ∏ PP ∈ allP B ψ.Q, resP B ψ PP (dBlk (blk2 T.rank) 1 (redFn B.F.βS PP (Lev.finE S k))) := by
  have hp := Formalism.L2.DIV.lev_le_parLev hk
  have eS : S.rank = T.rank + (S.rank - T.rank) := by have := B.hr; omega
  unfold levFn
  rw [extendOne_of_mem _ hk.2, prod_allP hQ, ← Finset.prod_union hQ.2, mul_assoc]
  congr 1
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => ?_
    rw [show (B.levS ψ).s = 1 from rfl, Finset.prod_range_one, resP_g hQ hP]
    exact congrArg _ ((GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ _ B.hr _).2.1 eS (parLev_g hp hP))
  · exact Finset.prod_congr rfl fun PP hP => by rw [resP_dq hQ hP]; rfl

theorem alg3 {G : Type} [CommGroup G] (X Y C : G) : X⁻¹ * Y⁻¹ * (C * X⁻¹)⁻¹ = (C * Y)⁻¹ := by
  rw [_root_.mul_inv_rev, inv_inv, _root_.mul_inv_rev, mul_comm X⁻¹, mul_assoc, inv_mul_cancel_left]

open Classical in
theorem dualTypeVacuumScalar_div_levelScalar {ψ : Twist D Circle} (hQ : B.admitted ψ.Q) {k : GA D S}
    (hk : Lev.finE S k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS ψ)) :
    vacC B ψ k 1 * (srcC B ψ k hk)⁻¹ = (levFn B.F.βS (B.levS ψ) (Lev.finE S k))⁻¹ := by
  have hp := Formalism.L2.DIV.lev_le_parLev hk
  have tri : ∀ PP ∈ allP B ψ.Q, redFn B.F.βS PP (Lev.finE S k) ∈ blockTri (blk2 T.rank) := fun PP hP => by
    rcases Finset.mem_union.1 hP with h | h
    · exact blockTri_blkOf_le _ _ (parLev_g hp h)
    · exact parLev_q hp h
  have hv : vacC B ψ k 1 = ∏ PP ∈ allP B ψ.Q, (resP B ψ PP (blkA B k PP))⁻¹ *
      (resP B ψ PP (dBlk (blk2 T.rank) 1 (redFn B.F.βS PP (Lev.finE S k))))⁻¹ := by
    unfold vacC
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [finE_one, map_one, map_one, mul_one, (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 B.hr _).1 (tri PP hP), map_mul, mul_inv]
    rfl
  have hs : srcC B ψ k hk = B.G.P.chi ⟨rTup B.F.βS (B.levS ψ) (Lev.finE S k), hk.2⟩ *
      ∏ PP ∈ allP B ψ.Q, (resP B ψ PP (blkA B k PP))⁻¹ := by
    unfold srcC
    rw [prod_allP hQ, mul_assoc]
    congr 2
    · exact Finset.prod_congr rfl fun PP hP => by rw [resP_g hQ hP]
    congr 1
    · exact Finset.prod_congr rfl fun PP hP => by rw [resP_d hQ hP]
    · exact Finset.prod_congr rfl fun PP hP => by rw [resP_q hQ hP]
  rw [hv, hs, levFn_eq hQ hk, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  exact alg3 _ _ _

end Scal

section Main

variable {B : Base S T}

theorem dual_type (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {ω : PairRep S T}
    (hω : B.IsWeil ψ.chi ω) {k : GA D S} (hk : k ∈ GfC S) (hJ : finPt S k ∈ B.levJ ψ) :
    ω (k, 1) (B.vecFlat ψ) = ((B.levLam ψ ⟨_, hJ⟩ : ℂˣ) : ℂ)⁻¹ • B.vecFlat ψ := by
  have hk' : Lev.finE S k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS ψ) := ((B.finPt_mem_levJ ψ hk).1 hJ).2
  have e := om_vec_move hB hS hψ hQ hω hk (one_mem _) (parLev_St (Formalism.L2.DIV.lev_le_parLev hk')) (one_mem_St T _)
    (φ := fun PP => flat (ψ.resC PP.1)) (φ' := fun PP => flat (ψ.resC PP.1)) (c' := (((srcC B ψ k hk')⁻¹ : ℂˣ) : ℂ))
    (fun x => by rw [datumFunction_sourceLevel_scalar B ψ hk' x, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul])
  rw [Base.vecFlat, e, B.levLam_finPt ψ hJ]
  congr 1
  rw [← Units.val_mul, dualTypeVacuumScalar_div_levelScalar hQ hk', Units.val_inv_eq_inv_val]
  rfl

theorem dual_type_fock (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {ω : PairRep S T}
    (hω : B.IsWeil ψ.chi ω) {k : GA D S} (hk : k ∈ GfC S) (hJ : finPt S k ∈ B.levJ ψ) (P : PolF D T.rank S.rank) :
    ω (k, 1) (B.F.fock (B.vecFlat ψ) P) = ((B.levLam ψ ⟨_, hJ⟩ : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat ψ) P :=
  GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ S T _ _ ω hB.frame.vac.2.inf hω _ _ _ _ _
    (fun P' => Base.isThetaFunO_fock_vecAt hB hQ _ P') k hk 1 (one_mem _) _ (dual_type hB hS hψ hQ hω hk hJ) P

end Main

section Target

variable {B : Base S T}

open Classical in

theorem om_tgt_of_red (hB : B.Good) (hS : S.SigOK) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {κ : GA D T} (hκ : κ ∈ GfC T) (sκ : Lev.finE T κ ∈ St B.F.βT) (hpg : ∀ PP ∈ B.G.Pg, redFn B.F.βT PP (Lev.finE T κ) = 1)
    {φ φ' : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ} (s : ↥Q → ℂˣ)
    (hφ : ∀ (PP : ↥Q) y, φ PP ((redFn B.F.βT PP.1 (Lev.finE T κ)).val * y) = (s PP : ℂ) * φ' PP y) :
    ω (1, κ) (B.vecAt Q φ') = (((∏ PP, s PP)⁻¹ : ℂˣ) : ℂ) • B.vecAt Q φ := by
  have hν : (Twist.triv Circle Q : Twist D Circle).Good := Twist.triv_good ((dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono
    (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)))
  set bδ : ℂˣ := ∏ PP ∈ B.de.Q, B.de.resC PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) with hbδ
  have hD : ∀ x, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ') x =
      (((bδ * ∏ PP, s PP)⁻¹ : ℂˣ) : ℂ) * B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ) (actO S T 1 κ x) := fun x => by
    rw [datumFn_act B.F B.G (B.de.Q ∪ Q) (one_mem_St S _) sκ (a := 1) (b := ((bδ * ∏ PP, s PP : ℂˣ) : ℂ))
      (ω' := B.locFn Q φ')
      (fun y => by
        rw [one_mul]
        refine GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hP => ?_
        change _ = y PP
        simp [hpg PP hP, redFn_one])
      (fun y => by
        simp only [finE_one, inv_one, Units.val_one, Matrix.mul_one]
        unfold Base.locFn
        rw [Finset.prod_congr rfl fun PP _ => flat_mul B.hr _ _ (y PP), Finset.prod_congr rfl fun PP _ => hφ PP (y PP.1),
          Finset.prod_mul_distrib, Finset.prod_mul_distrib, hbδ]
        simp only [Units.val_mul, Units.coe_prod]
        ring) x, one_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  refine (om_vec_move hB hS hν hQ hω (one_mem _) hκ (one_mem_St S _) sκ hD).trans ?_
  rw [← Units.val_mul]
  congr 2
  have hv : vacC B (Twist.triv Circle Q) 1 κ = bδ := by
    unfold vacC
    simp only [map_one, redFn_one, inv_one, one_mul]
    rw [show allP B (Twist.triv Circle Q : Twist D Circle).Q = allP B Q from rfl, prod_allP hQ, hbδ]
    have h1 : ∏ PP ∈ B.G.Pg, resP B (Twist.triv Circle Q) PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) = 1 :=
      Finset.prod_eq_one fun PP hP => by rw [hpg PP hP, map_one, map_one]
    have h3 : ∏ PP ∈ Q, resP B (Twist.triv Circle Q) PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) = 1 :=
      Finset.prod_eq_one fun PP hP => by
        rw [resP_q (ν := Twist.triv Circle Q) hQ hP]
        simp [Twist.resC, Twist.triv]
    rw [h1, h3, one_mul, mul_one]
    exact Finset.prod_congr rfl fun PP hP => by rw [resP_d (ν := Twist.triv Circle Q) hQ hP]
  rw [hv, mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]

end Target

section TargetSeries

variable {B : Base S T}

end TargetSeries

section TargetSeriesAll

variable {B : Base S T}

open Classical in

theorem gen_mul_right_of_red (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {ω : PairRep S T}
    (hω : B.IsWeil 1 ω) {κ : GA D T} (hκ : κ ∈ GfC T) (sκ : Lev.finE T κ ∈ St B.F.βT)
    (hpg : ∀ PP ∈ B.G.Pg, redFn B.F.βT PP (Lev.finE T κ) = 1) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    B.gen ω ψ h P (g * κ) = B.gen ω ψ h P g := by
  set d : ∀ PP : Pl D.host.E, (kP PP)ˣ := fun PP => GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ)) with hd
  have hv : ω (1, κ) (B.vecFlat ψ) = (((∏ PP : ↥ψ.Q, ψ.resC PP.1 (d PP.1))⁻¹ : ℂˣ) : ℂ) • B.vecFlat ψ :=
    om_tgt_of_red hB hS hQ hω hκ sκ hpg (fun PP => ψ.resC PP.1 (d PP.1)) fun PP y => flat_mul B.hr _ _ y
  have hf : ω (1, κ) (B.F.fock (B.vecFlat ψ) P) =
      (((∏ PP : ↥ψ.Q, ψ.resC PP.1 (d PP.1))⁻¹ : ℂˣ) : ℂ) • B.F.fock (B.vecFlat ψ) P :=
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ S T _ _ ω hB.frame.vac.2.inf hω _ _ _ _ _
      (fun P' => Base.isThetaFunO_fock_vecAt hB hQ _ P') 1 (one_mem _) κ hκ _ hv P
  have hdet : detChar T ψ.chi κ = ∏ PP ∈ ψ.Q, ψ.res PP (d PP) :=
    GlobalTheory.T.unitaryDetCharacter_eq_prod_residue_goodBaseFrame B hB ψ hψ hκ sκ
  have e1 : ((detChar T ψ.chi κ : Circle) : ℂ) * (((∏ PP : ↥ψ.Q, ψ.resC PP.1 (d PP.1))⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [hdet, Finset.prod_coe_sort ψ.Q (fun PP => ψ.resC PP (d PP))]
    have : ((∏ PP ∈ ψ.Q, ψ.res PP (d PP) : Circle) : ℂ) = ((∏ PP ∈ ψ.Q, ψ.resC PP (d PP) : ℂˣ) : ℂ) := by
      simp only [Twist.resC, MonoidHom.comp_apply, Units.coe_prod]
      exact map_prod Circle.coeHom _ _
    rw [this, Units.mul_inv]
  have e2 : ((h, g * κ) : GA D S × GA D T) = (h, g) * (1, κ) := by simp
  simp only [Base.gen, LinearMap.comp_apply, twistBy_apply, series_apply]
  rw [e2, map_mul, Module.End.mul_apply, hf, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, detChar_mul hψ.real, Circle.coe_mul]
  calc ((detChar T ψ.chi g : Circle) : ℂ) * ((detChar T ψ.chi κ : Circle) : ℂ) * _ = _ := by
        rw [mul_assoc, ← mul_assoc ((detChar T ψ.chi κ : Circle) : ℂ), e1, one_mul]

end TargetSeriesAll

section TargetLattice

variable {B : Base S T}

end TargetLattice

section Xi

variable {B : Base S T} {C : Type} [AddCommGroup C] [Fintype C]

open Classical in

theorem delQ_det_of_red (hB : B.Good) {u : UnivTwist D C} {Q : Finset (Pl D.host.E)} (hu : u.Good Q) {κ : GA D T} (hκ : κ ∈ GfC T)
    (sκ : Lev.finE T κ ∈ St B.F.βT) :
    Multiplicative.toAdd (detChar T (u.delQ Q) κ) =
      fun PP : ↥Q => Multiplicative.toAdd (u.kap PP.1 (GeneralLinearGroup.det (redFn B.F.βT PP.1 (Lev.finE T κ)))) := by
  have ht := GlobalTheory.T.tameTwistFamily_specialization_good D C (Multiplicative (↥Q → C)) u Q (MonoidHom.id _) hu
  have e := GlobalTheory.T.unitaryDetCharacter_eq_prod_residue_goodBaseFrame B hB (u.spec Q (MonoidHom.id _)) ht hκ sκ
  have e1 : (u.spec Q (MonoidHom.id _)).chi = u.delQ Q := MonoidHom.id_comp _
  rw [e1] at e
  rw [e, toAdd_prod, show (u.spec Q (MonoidHom.id _)).Q = Q from rfl, ← Finset.sum_coe_sort Q]
  refine Eq.trans (Finset.sum_congr rfl fun PP _ => ?_) (Finset.univ_sum_single _)
  show Multiplicative.toAdd ((u.spec Q (MonoidHom.id _)).res PP.1 _) = _
  rw [show (u.spec Q (MonoidHom.id _)).res PP.1 = (MonoidHom.id _).comp ((AddMonoidHom.toMultiplicative
    (AddMonoidHom.single (fun _ : ↥Q => C) ⟨PP.1, PP.2⟩)).comp (u.kap PP.1)) from dif_pos PP.2]
  rfl

open Classical in

theorem xiCoef_mul_right_of_red (hB : B.Good) (hS : S.SigOK) {u : UnivTwist D C} {Q : Finset (Pl D.host.E)} (hu : u.Good Q)
    (hQ : B.admitted Q) {Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ} (hΦ : Base.IsAdmFam u Q Φ)
    {ω : PairRep S T} (hω : B.IsWeil 1 ω) {κ : GA D T} (hκ : κ ∈ GfC T) (sκ : Lev.finE T κ ∈ St B.F.βT)
    (hpg : ∀ PP ∈ B.G.Pg, redFn B.F.βT PP (Lev.finE T κ) = 1) (h : GA D S) (P : PolF D T.rank S.rank) (a : ↥Q → C) (g : GA D T) :
    B.xiCoef ω u Q Φ h P a (g * κ) = B.xiCoef ω u Q Φ h P a g := by
  set dκ : ↥Q → C := fun PP => Multiplicative.toAdd (u.kap PP.1 (GeneralLinearGroup.det (redFn B.F.βT PP.1 (Lev.finE T κ))))
    with hdκ
  have hmul : Multiplicative.toAdd (detChar T (u.delQ Q) (g * κ)) = Multiplicative.toAdd (detChar T (u.delQ Q) g) + dκ := by
    rw [detChar_mul hu.delQ_real, toAdd_mul, delQ_det_of_red hB hu hκ sκ]
  set b := a - Multiplicative.toAdd (detChar T (u.delQ Q) g) - dκ with hb
  have hvec : ω (1, κ) (B.vecFam Q Φ b) = B.vecFam Q Φ (b + dκ) := by
    have := om_tgt_of_red hB hS hQ hω hκ sκ hpg (φ := fun PP y => ((Φ PP.1 ((b + dκ) PP) y : ℚ) : ℂ))
      (φ' := fun PP y => ((Φ PP.1 (b PP) y : ℚ) : ℂ)) (fun _ => 1) (fun PP y => by
        have e := (hΦ PP.1 PP.2).equiv (redFn B.F.βT PP.1 (Lev.finE T κ)) (b PP)
          ((redFn B.F.βT PP.1 (Lev.finE T κ)).val * y)
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at e
        simp only [Pi.add_apply, Units.val_one, one_mul, hdκ]
        rw [← e])
    rw [Finset.prod_const_one, inv_one, Units.val_one, one_smul] at this
    exact this
  have hf : ω (1, κ) (B.F.fock (B.vecFam Q Φ b) P) = B.F.fock (B.vecFam Q Φ (b + dκ)) P := by
    have hth : IsThetaFunO B.F.ψ S T (B.vecFam Q Φ b) := by
      exact GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
        (Base.isThetaAt_vecAt hB hQ (fun PP y => ((Φ PP.1 (b PP) y : ℚ) : ℂ))) hB.frame.vac.2.theta
    rw [Frame.fock, (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hB.frame.vac.2.inf (fun _ => 1) (fun _ => 1)
      (fun τ => (B.F.BS τ).val) (fun τ => (B.F.BS τ).val) B.F.sT B.F.sT B.F.BT B.F.BT 1 κ
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hκ])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hκ]) _ hth P).2, hvec]
    rfl
  have e2 : ((h, g * κ) : GA D S × GA D T) = (h, g) * (1, κ) := by simp
  rw [Base.xiCoef_apply, Base.xiCoef_apply, series_apply, series_apply, hmul,
    show a - (Multiplicative.toAdd (detChar T (u.delQ Q) g) + dκ) = b by rw [hb]; abel, e2, map_mul, Module.End.mul_apply, hf,
    show b + dκ = a - Multiplicative.toAdd (detChar T (u.delQ Q) g) by rw [hb]; abel]

end Xi

section Statement

variable {B : Base S T}

open Classical in

theorem thetaSeriesData_have_dualType (hB : B.Good) (hS : S.SigOK) {ψ : Twist D Circle} (hψ : ψ.Good) (hQ : B.admitted ψ.Q) :
    (∀ ω : PairRep S T, B.IsWeil ψ.chi ω → ∀ k ∈ GfC S, ∀ hJ : finPt S k ∈ B.levJ ψ,
      ω (k, 1) (B.vecFlat ψ) = ((B.levLam ψ ⟨_, hJ⟩ : ℂˣ) : ℂ)⁻¹ • B.vecFlat ψ ∧
        ∀ P : PolF D T.rank S.rank, ω (k, 1) (B.F.fock (B.vecFlat ψ) P) = ((B.levLam ψ ⟨_, hJ⟩ : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat ψ) P) ∧
    (∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ κ ∈ GfC T, Lev.finE T κ ∈ St B.F.βT →
      (∀ PP ∈ B.G.Pg, redFn B.F.βT PP (Lev.finE T κ) = 1) →
      ∀ (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T), B.gen ω ψ h P (g * κ) = B.gen ω ψ h P g) ∧
    (∀ (C : Type) [AddCommGroup C] [Fintype C] (u : UnivTwist D C) (Q : Finset (Pl D.host.E)), u.Good Q → B.admitted Q →
      ∀ Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ, Base.IsAdmFam u Q Φ →
      ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ κ ∈ GfC T, Lev.finE T κ ∈ St B.F.βT →
      (∀ PP ∈ B.G.Pg, redFn B.F.βT PP (Lev.finE T κ) = 1) →
      ∀ (h : GA D S) (P : PolF D T.rank S.rank) (a : ↥Q → C) (g : GA D T),
        B.xiCoef ω u Q Φ h P a (g * κ) = B.xiCoef ω u Q Φ h P a g) :=
  ⟨fun _ hω _ hk hJ => ⟨dual_type hB hS hψ hQ hω hk hJ, dual_type_fock hB hS hψ hQ hω hk hJ⟩,
    fun _ hω _ hκ sκ hpg h P g => gen_mul_right_of_red hB hS hψ hQ hω hκ sκ hpg h P g,
    fun _ _ _ _ _ hu hQ' _ hΦ _ hω _ hκ sκ hpg h P a g => xiCoef_mul_right_of_red hB hS hu hQ' hΦ hω hκ sκ hpg h P a g⟩

example (D : D7) (k : ℕ) : ∃ (S T : HSp D) (B : Base S T), B.Good ∧ S.SigOK ∧ B.admitted (Twist.triv Circle (∅ : Finset (Pl D.host.E))).Q ∧
    (Twist.triv Circle (∅ : Finset (Pl D.host.E)) : Twist D Circle).Good := by
  let S : HSp D := Examples₂.posSpace Examples₂.star_isIntegral (2 * k + 2)
  let T : HSp D := Examples₂.posSpace Examples₂.star_isIntegral (2 * k + 1)
  have hr : T.rank ≤ S.rank := Nat.le_succ _
  obtain ⟨F, hF⟩ := exists_frame_good S T (Examples₂.posSpace_sigOK _ _) (fun _ => rfl) (Examples₂.posSpace_sigOK _ _) hr
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  let B : Base S T := ⟨hr, F, TypeDat.empty D _, Twist.triv Circle ∅,
    Weight.first D _ (fun _ => 2 * k + 1) (fun _ => 0) fun _ => k, 1, η⟩
  have hB : B.Good :=
    { even := ⟨k + 1, by change 2 * k + 2 = _; ring⟩
      odd := ⟨k, rfl⟩
      frame := hF
      de := Twist.triv_good splitSet_empty
      places := placesOK_empty
      wt := Weight.first_good _ (fun _ => Nat.succ_pos _) fun _ => Nat.le_succ _
      sig := fun _ => rfl
      sigOK := Examples₂.posSpace_sigOK _ _
      eta := hη
      hecke := ⟨continuous_const, fun _ => rfl⟩
      real := fun _ => rfl
      unram := fun _ _ _ _ _ => rfl
      tame := fun _ h => absurd h (Finset.notMem_empty _)
      inf := fun τ => ⟨0, by simp [B, Weight.first]; ring, ⟨_, hF.vac.2.inf⟩, fun _ _ _ _ _ => by simp [B]⟩ }
  exact ⟨S, T, B, hB, Examples₂.posSpace_sigOK _ _, Base.admissible_empty_of_good hB, Twist.triv_good splitSet_empty⟩

end Statement

end GlobalTheory.ExportSeries.DualType

end
