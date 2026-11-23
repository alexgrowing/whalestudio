import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCoordPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBaseStatement

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

theorem exists_preX {K : Ctx} {P : Pre} (hO : K.Over P) (X₀ : PreX P) (Q : PiBar P.host) :
    ∃ X : PreX P, InEx.Oriented X Q ∧ ∀ u, P.cOf u * (X.piT u : P.host.E) = (X.piT P.u₀ : P.host.E) := by
  obtain ⟨X, hX⟩ := InEx.exists_oriented X₀ Q
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hO
  exact ⟨{ X with
    piT := K.Lv.piT
    piT_K := K.Lv.piT_K
    piT_norm := K.Lv.piT_norm
    piT_cong := fun u => Ideal.mem_span_singleton.1 (K.Lv.piT_cong u) }, hX, fun u => div_mul_cancel₀ _ (K.Lv.piT_ne u)⟩

theorem step_colW (h2b : StandardLattice.SiegelMassRatioCM) : Step KPx (fun _ _ _ _ => True) fun _ B f T => Nonempty (ColW B f T) := by
  refine EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => (InEx.lg_colIn K).imp ?_
  rintro B f T hO h ⟨⟨δ, hδ⟩, hp⟩ - -
  obtain ⟨X₀⟩ := (hfr _ hO).1
  obtain ⟨X, hX, hc⟩ := exists_preX hO X₀ f.P
  obtain ⟨sel, hsel⟩ := Formalism.L2.Col.exists_sel B.fields
  obtain ⟨J, hJ⟩ := exists_ambIn_ok B.host
  obtain ⟨I, a1, a2, a3, a4, -⟩ := h.1 X hX sel hsel J hJ
  exact ⟨⟨X, I, a1, a2, a3, a4, ⟨hp, hc⟩, TrueColsTest.laws a1, TrueColsTest.law0 a1 _, δ, hδ, h.2.2, h.2.1⟩⟩

theorem prePin_coordPre (P : PreCh) (L : LevCh P) : PrePin (GlobalTheory.StdFrameObj.coordPre P L) :=
  fun a b h => PinsCoord.extTo_basis _ _ a b h

theorem ksCond (hR : GlobalTheory.NT.RayField) (hP : GlobalTheory.Published.PrincipalIdealSt) (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) :
    V4.KsCond fun B f => ∃ δ : Fld.FieldDat B.toPre, B.KsExact δ f := by
  refine ⟨InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := Fld.nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.T.rayField_le_and_exists_base hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

theorem baseCond_KPx (h2b : StandardLattice.SiegelMassRatioCM) (hR : GlobalTheory.NT.RayField) (hP : GlobalTheory.Published.PrincipalIdealSt)
    (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) : BaseCond KPx :=
  baseCond_of (PP := fun P _ => PrePin P) (ksCond hR hP hA)
    (EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => by
      have hO : K.Over (GlobalTheory.StdFrameObj.coordPre K.P K.Lv) :=
        ⟨_, _, _, _, _, _, rfl, GlobalTheory.StdFrameObj.diagSpaces_coordPre K.P K.Lv⟩
      obtain ⟨f⟩ := (hfr _ hO).2
      exact ⟨_, f, hO, prePin_coordPre _ _⟩)

theorem not_step_false (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) {KP : BaseP} (hK : BaseCond KP) :
    ¬ Step KP (fun _ _ _ _ => True) fun _ _ _ _ => False := fun h =>
  not_exTrueG_false hH hLP h2b hK (exTrueG_iff_step.2 (h.trans (Step.of_all fun _ _ _ _ _ _ _ a => a.elim)))

theorem exists_colW (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) (hR : GlobalTheory.NT.RayField)
    (hP : GlobalTheory.Published.PrincipalIdealSt) (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) :
    ∃ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B), K.Over B.toPre ∧ KPx B f ∧ Forced K B T ∧ Nonempty (ColW B f T) := by
  by_contra h
  refine not_step_false hH hLP h2b (baseCond_KPx h2b hR hP hA) ((step_colW h2b).trans (Step.of_all ?_))
  exact fun K B f T a b c d => h ⟨K, B, f, T, a, b, c, d⟩

theorem not_stepW_false (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM) (hR : GlobalTheory.NT.RayField)
    (hP : GlobalTheory.Published.PrincipalIdealSt) (hA : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt) :
    ¬ StepW (fun _ _ _ _ _ => True) fun _ _ _ _ _ => False := fun h =>
  not_step_false hH hLP h2b (baseCond_KPx h2b hR hP hA)
    (((step_colW h2b).and h).trans (Step.of_all fun _ _ _ _ _ _ _ H => H.1.elim fun w => H.2 w trivial))

theorem ColW.kpx {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) : KPx B f := ⟨⟨w.δ, w.exact⟩, w.pins.iX⟩

theorem not_corePropertyOf_false (K : Ctx) (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T) :
    ¬ positionOf (fun _ _ _ _ _ _ _ => False) K X f T c := fun ⟨_, _, _, h, _⟩ => h

theorem positionOf_cols {P : CP} {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T}
    (h : positionOf P K X f T c) : ∃ w : ColW X.B f T, X.C = w.C :=
  let ⟨w, _, _, _, e⟩ := h; ⟨w, congrArg Sigma.fst e⟩

theorem exists_later {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (hO : K.Over B.toPre) (w : ColW B f T) (G : GJStage B w.C) :
    ∃ Z : w.Lt, Z.G = G :=
  let ⟨Z⟩ := TrueColsTest.later w.l (JetEx.hasLetters_of_over hO); ⟨⟨Z.W, Z.V, Z.S, Z.N, G⟩, rfl⟩

theorem GIs.exists_colT {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (hO : K.Over B.toPre) {w : ColW B f T}
    {G : GJStage B w.C} (h : GIs K w G) : ∃ Z : w.Lt, Z.G = G ∧ Formalism.L2.Theta.VolTieG (w.D Z) ∧ Nonempty (ColT w Z) := by
  obtain ⟨⟨W, V, S, N, G'⟩, rfl⟩ := exists_later hO w G
  exact ⟨_, rfl, (h W V S N).1, (h W V S N).2.2⟩

theorem GIs.not_double {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (hO : K.Over B.toPre) {w : ColW B f T}
    {G : GJStage B w.C} (h : GIs K w G) (X : @HSpace B.host.E _ _ B.host.cmStar) (hX : letI := B.host.cmStar; X.SigOK) :
    ¬ GIs K w { G with vol := fun Y => 2 * G.vol Y, vol_pos := fun Y => mul_pos two_pos (G.vol_pos Y) } := fun h' => by
  obtain ⟨⟨W, V, S, N, G'⟩, rfl⟩ := exists_later hO w G
  obtain ⟨⟨μ, hμ⟩, H⟩ := (h W V S N).1 X hX
  obtain ⟨⟨F, hF⟩, H1⟩ := H μ hμ
  have a := H1 F hF
  have b := (((h' W V S N).1 X hX).2 μ hμ).2 F hF
  have c : ENNReal.ofReal (G'.vol X) = ENNReal.ofReal (2 * G'.vol X) := a.symm.trans b
  have p := G'.vol_pos X
  rw [ENNReal.ofReal_eq_ofReal_iff p.le (by positivity)] at c
  linarith

end GlobalTheory.Mem.Top.Bl.Model

end
