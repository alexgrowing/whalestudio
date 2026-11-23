import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometry
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIndexPlaceEqOfReadsStdOfMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocXStdStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
theorem GlobalTheory.XGeoStd.exists_xgeo_alt : GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, ∃ (a : XGeo (I.rec7 l Z)) (c₀ : ℕ → ℂ), (∀ j, j ≤ B.R.m → (a.x j).Is) ∧ GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ a.x a.vac c₀ ∧ a.bT = 1 ∧ (∀ r s, (a.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) ∧ a.LT = (_root_.GlobalTheory.Fam.pk_z W).ΛX ∧ IsLineVec a.Lz a.ζ₀ ∧ star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) ∧ GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) ∧ (∀ r, vecB (a.oT B.R.m rfl) a.ζ₀ r = (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)) ∧ (∀ n (h : n = B.R.m) x, ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) ∧ ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∃ s : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  open GlobalTheory.XGeoStd GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel GlobalTheory.Mem in (
    intro hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hW u
    have hI : I.Ok := hW.tr.ok
    obtain ⟨hP⟩ := hW.tr.pins
    have hψ : IsStdChar (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := W.Q.stdChar
    have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := W.Q.charW.base.models.inf
    choose vac hvac using exists_vac (l := l) (Z := Z) hI hψ hθ
    choose c hc using fun i hi => GlobalTheory.T.exists_const_movedVacuum_all_tuples hSA I hI hP l Z _ _ hψ hθ i hi (vac i) (hvac i)
    refine ⟨xgeo l Z hI vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX, fun j => if h : j + 1 ≤ B.R.m then c j h else 1,
      fun j _ => stdSp_is ((I.rec7 l Z).sp.X_sig _) (gram_X hI j),
      ⟨hψ, hθ, fun j _ => ⟨rfl, rfl, fun z => ?_⟩, fun j _ => hvac j, fun j hj => ?_⟩, rfl, fun r s => by
      show (if ((s : ℕ) = r) then (1 : (I.rec7 l Z).host.E) else 0) = if (r : ℕ) = s then 1 else 0
      by_cases h : (r : ℕ) = s
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun h' => h h'.symm), if_neg h], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← lat_X hI j]; exact Iff.rfl
    · rw [dif_pos hj]; exact hc j hj
    case refine_3 => exact isLineVec_zeta l Z u
    case refine_4 => exact norm_zeta l Z u
    case refine_5 => exact isEmbTop_topDec (gram_X hI _) (gram_X' hI) hP.iX _
    case refine_6 =>
      intro r
      have h0 := rk_top (I.rec7 l Z)
      have h2 := Formalism.L2.Forms.rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl
      change (∑ _i : Fin 1, (if (I.rec7 l Z).sp.X'.rank = (r : ℕ) then (1 : (I.rec7 l Z).host.E) else 0) *
        piE I l Z u) = if (r : ℕ) + 1 = B.R.N B.R.m then piE I l Z u else 0
      rw [Fin.sum_univ_one]
      have hr := r.2
      have e : ((I.rec7 l Z).sp.X'.rank = (r : ℕ)) ↔ ((r : ℕ) + 1 = B.R.N B.R.m) := by
        change _ ↔ (r : ℕ) + 1 = (I.rec7 l Z).R.N (I.rec7 l Z).R.m
        constructor <;> intro h <;> omega
      by_cases h : (I.rec7 l Z).sp.X'.rank = (r : ℕ)
      · rw [if_pos h, if_pos (e.1 h), one_mul]
      · rw [if_neg h, if_neg (fun h' => h (e.2 h')), zero_mul]
    case refine_7 =>
      intro n h x
      refine ⟨GlobalTheory.PlaceModel.latFrame _, GlobalTheory.PlaceModel.isSelfDualC_latFrame _, ?_⟩
      have e : (_root_.GlobalTheory.Fam.pk_z W).ΛX = GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X' := eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX
      show GlobalTheory.FinPl.OrthAt (oTop l Z hI n h) (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X n)) (_root_.GlobalTheory.Fam.pk_z W).ΛX _ x
      rw [e]
      exact GlobalTheory.XGeoStd.orthAt_oTop hI n h x
    case refine_8 =>
      intro PP hPP
      obtain ⟨k, _, _, _, _, _, _, q, h1, h2, h3, h4⟩ := _root_.GlobalTheory.XGeoPlace.exists_index_place_eq_of_readsStd_of_mem W hW u PP hPP
      exact _root_.GlobalTheory.T.true_family_vacuum_data_alt W hW u vac PP k q h1 h2 h3 h4
  )
end
end
