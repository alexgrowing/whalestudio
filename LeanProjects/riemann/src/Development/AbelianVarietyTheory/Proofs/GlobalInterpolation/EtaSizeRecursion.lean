import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelDataRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBdRecOfEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.Top.Bl

theorem exists_linked_of_eq {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}
    (hB : ∀ (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (c : ℝ)
      (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}),
      q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (BWit q b))
    (q : WPt p.s K) (R' : Formalism.L2.RecT q.O.ex) (hR' : RecPinE q R') (c : ℝ) {D : D7} {O : Obj D} (R : BdRec D O c)
    (he : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), BdRec D O c) = ⟨q.w.D q.Z, q.O, R'⟩) (hsc : O.L.sc = K.s)
    (hv : Val K.C K.cD K.ch O.L) (n : {n : ℕ × ℕ // D.s.Del = (n.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (n.2 : ℝ)}) :
    ∃ b : GlobalTheory.Fc.Bundle D O c, ∃ (q' : WPt p.s K) (b' : GlobalTheory.Fc.Bundle (q'.w.D q'.Z) q'.O c), Nonempty (BWit q' b') ∧
      (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), GlobalTheory.Fc.Bundle D O c) = ⟨q'.w.D q'.Z, q'.O, b'⟩ := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp he
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  obtain ⟨b, -, hW⟩ := hB q R' hR' c n hsc hv
  exact ⟨b, q, b, hW, rfl⟩

theorem exBL_isLinked : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (BWit q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (IsLinked p) := by
  intro hA hW hRay hL p hWit hZe hB
  refine ⟨fun _ _ _ _ _ => True, GlobalTheory.Fc.largeBaseProperty_true, ?_⟩
  unfold GlobalTheory.Fc.ExB
  refine GlobalTheory.Fc.EvP.mono (fun κ K _ H => ?_) (GlobalTheory.Fc.EvP.and hZe hB)
  intro β hβ c
  obtain ⟨q, hq, hE⟩ := hWit K β hβ.1
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hO : Over β.X.toD7 K.P K.Lv := by
    obtain ⟨sp, hT, hY, hA', hV, hz, e, -⟩ := β.c.isOver
    exact ⟨sp, hT, hY, hA', hV, hz, β.X, e, rfl⟩
  have hP : K.P.H.levelPrimes = {K.P.H.g 0, K.P.H.g 1, K.P.H.pde, K.P.H.pde', DC.q0H K.P.H} :=
    hG.host.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLT : Formalism.L2.Host.LevelTied β.D :=
    GlobalTheory.Mem.HD.levelTied_of_levEx _ ((GlobalTheory.Mem.HD.levEx_of_over _ _ _ hO hP).2 _ _)
  have hD : β.D = q.w.D q.Z := congrArg Sigma.fst hq
  have hLT' : Formalism.L2.Host.LevelTied (q.w.D q.Z) := hD ▸ hLT
  obtain ⟨R', hR'⟩ := GlobalTheory.T.exists_level_data_ray_field hA hW hRay hL p K q hLT' (H.1 q) hE
  obtain ⟨R, he⟩ := exists_bdRec_of_eq hq R' c
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact exists_linked_of_eq H.2 q R' hR' c R he β.sc hv ⟨(_, _), hv.Del_eq, hv.eta_eq⟩

end GlobalTheory.Mem.Top.Bl
