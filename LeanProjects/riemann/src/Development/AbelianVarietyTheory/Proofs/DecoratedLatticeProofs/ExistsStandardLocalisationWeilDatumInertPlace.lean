import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertSupportedPointIntegralFramesMemLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupActionInertSupportedPointsFramesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticFormInertSupportedPointsAntidiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLatticeVacuumMemSpanInertTranslatesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertFrameLoc

set_option maxHeartbeats 800000 in

theorem exists_isStd_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ (∀ m : M, IsThetaFunO ψ S T m) ∧ ∀ x, ∃ u : WO S T, ∀ m : M, ((ρ x m : M) : WO S T → ℂ) = heisO ψ S T u m := by
  intro D ψ S T χS χT om hW v w h hw uS uT c ϖ eS eT hU hcS hcT f hf hf0
  obtain ⟨hconj, ⟨aS, haS, gS, eSa⟩, kSc⟩ := hcS
  obtain ⟨-, ⟨aT, haT, gT, eTa⟩, kTc⟩ := hcT
  obtain ⟨k, hk⟩ := GlobalTheory.InertLoc.exists_isGen D w
  have h2 := GlobalTheory.T.valued_two_eq_one_inertPlace_cmField D v w hw
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := GlobalTheory.InertLoc.exists_delta_psi hU h2 (thW ψ hw h (k * c k))
    (GlobalTheory.T.inert_place_local_character_conjugation_inverse D ψ v w hw h c k hconj hU.1) (GlobalTheory.T.inertPlace_localTraceCharacter_conductor_integers D ψ v w hw h c ϖ k hW.std hconj hU hk)
  have hadd : ∀ x y, uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := uPt_add
  have hMθ : spanT ψ (uPt hw h k aS aT) f ≤ GlobalTheory.FinWeilO.thetaSub ψ S T := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact GlobalTheory.FinTranslate.isTheta_heisO_fin hW.std.1 (map_infPart_uPt (hw := hw) (h := h) (k := k) (aS := aS) (aT := aT) x) hf.1)
  let π : GU c S.rank × GU c T.rank →* Module.End ℂ (WO S T → ℂ) :=
    om.comp (((embV S v).comp eS.symm.toMonoidHom).prodMap ((embV T v).comp eT.symm.toMonoidHom))
  have hπ : ∀ p m, π p m = om (embV S v (eS.symm p.1), embV T v (eT.symm p.2)) m := fun _ _ => rfl
  have hstab : ∀ p, ∀ m ∈ spanT ψ (uPt hw h k aS aT) f, π p m ∈ spanT ψ (uPt hw h k aS aT) f := fun p m hm =>
    mem_spanT_of (fun y => by
      rw [hπ, hW.om_heis _ _ _ _ hf.1, GlobalTheory.T.local_group_action_inert_supported_points_frames]
      exact heis_mem_spanT hadd _
        (GlobalTheory.T.weilRep_latticeVacuum_mem_span_inertTranslates D ψ S T χS χT om hW v w hw h uS uT c ϖ k aS aT hU hconj hk haS haT gS gT f hf _ _)) hm
  have hint2 : (2⁻¹ : w.adicCompletion D.host.E) ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := (GlobalTheory.SphTheta.half h2).2
  have hvac : ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E),
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → heisO ψ S T (uPt hw h k aS aT x) f = f := fun x hx => by
    have h1 := hf.2.1 _ (GlobalTheory.T.inert_supported_point_integral_frames_mem_lattice D v w hw h S T k aS aT hk haS haT ((2⁻¹ : w.adicCompletion D.host.E) • x)
      fun i j => mul_mem hint2 (hx i j))
    rwa [two_nsmul, ← uPt_add, GlobalTheory.InertLoc.half_add_half] at h1
  have hfM : f ∈ spanT ψ (uPt hw h k aS aT) f := self_mem_spanT uPt_zero
  have dict := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have unr : ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → GlobalTheory.Hk3.UnrPl w χ := fun χ hχ =>
    dict.2.1 χ fun w' hw' => by rw [(GlobalTheory.LFun.InertChart.under_eq_iff hw w').1 hw']; exact hχ
  have hfix := GlobalTheory.ConjVacFix.vacFix_of_unrPl ψ S T χS χT om w hW (unr χS uS) (unr χT uT)
  refine ⟨δ, ψ', spanT ψ (uPt hw h k aS aT) f, rhoT ψ (uPt hw h k aS aT) f hadd, omT ψ (uPt hw h k aS aT) f π hstab,
    ⟨f, hfM⟩, ⟨⟨hU, GlobalTheory.InertLoc.odd_of_v_two hU h2, antiG_mem _, antiG_mem _, antiJ_herm c _, antiJ_herm c _, hδ, p1, p2,
      ?_, fun x y => ?_, ?_, fun g g' x => ?_, fun g g' hg hg' s hs => ?_⟩,
      fun e => hf0 (congrArg Subtype.val e), fun x hx => Subtype.ext (hvac x hx), span_rhoT_eq_top hadd hfM⟩,
    rfl, fun _ _ _ => rfl, fun m => hMθ m.2, fun x => ⟨uPt hw h k aS aT x, fun _ => rfl⟩⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [coe_rhoT, uPt_zero, GlobalTheory.SplitScalar.heisO_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, coe_rhoT, coe_rhoT, GlobalTheory.SplitScalar.heisO_heisO, LinearMap.smul_apply, Submodule.coe_smul,
      coe_rhoT, ← uPt_add, GlobalTheory.T.symplectic_form_inert_supported_points_antidiagonal D ψ v w hw h S T c k aS aT hconj gS gT, ← p3]
    simp only [GlobalTheory.Hk3.locH, one_mul]
  · refine eq_top_iff.2 ((span_rhoT_eq_top hadd hfM).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨x, rfl⟩
    exact ⟨x, ⟨f, hfM⟩, fun y hy => Subtype.ext (hvac y hy), rfl⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    have hinv : (eS.symm g)⁻¹ = eS.symm g⁻¹ := (map_inv eS.symm g).symm
    show π (g, g') (heisO ψ S T (uPt hw h k aS aT x) m) = heisO ψ S T (uPt hw h k aS aT _) (π (g, g') m)
    rw [hπ, hπ, hW.om_heis _ _ _ _ (hMθ m.2), GlobalTheory.T.local_group_action_inert_supported_points_frames]
    refine congrArg (fun z => heisO ψ S T (uPt hw h k aS aT z) (om (embV S v (eS.symm g), embV T v (eT.symm g')) m)) ?_
    rw [← eTa, hinv, ← eSa]
    erw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  · refine Subtype.ext (hfix _ ⟨hMθ s.2, fun e e' he uu huu hh => ?_⟩ _
      ((dict.2.2.1 S _).2 ⟨eS.symm g, (kSc _).2 ((eS.apply_symm_apply g).symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg), rfl⟩) _
      ((dict.2.2.1 T _).2 ⟨eT.symm g', (kTc _).2 ((eT.apply_symm_apply g').symm ▸ GlobalTheory.SphTheta.mem_KU_iff.2 hg'), rfl⟩))
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integralFramePoint_of_inertHalf_latticePoint D v w hw h S T k aS aT hk haS haT e e' he uu huu hh
    exact congrArg Subtype.val (hs x hx)

end GlobalTheory.InertFrameLoc

end
