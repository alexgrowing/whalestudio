import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientBuiltLocalHypothesisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.etaJ_with_local_data_eq_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL K B f T w P hK hF hS x l big L hB hO M Tn Q hstd hQ hlat hT hR hAV hCS hE hI h42 hZ hG j v h1 h2 v' hv
  obtain rfl : v' = v := eq_of_heq hv
  have hTup : Formalism.L2.DIV.TupTie (withLoc L) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) x.r.Y.tup :=
    ⟨x.r.Y.tup0, x.r.Y.muAt, x.m.z.R.hv0, fun a b h => by rw [← x.r.Y.tupT_tup a, h, x.r.Y.tupT_tup]⟩
  have hTw : ∀ y, y ∈ ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).Tw ↔
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).μ y ≠
        (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 :=
    fun y => ⟨x.m.z.pins.char.tup.mu_ne y, fun h => by_contra fun hw => h (x.m.z.pins.char.tup.mu_off y hw)⟩
  have hθ := GlobalTheory.Mem.ThRead.theta_of_noEta GlobalTheory.Mem.ThetaRead3.thetaP_read_noEta GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth_noEta
    _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have hZ0 := GlobalTheory.Mem.R3.DivisionRationalLift.rationalReadingNoCongruence_thetaComplement_spanned _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have key := GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality (withLoc L) _ _ _ _ (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
    x.m.z.F.P0 x.m.z.F.ψ0 ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).fam3.toSub2 (zsOf x.m.z.R x.m.z.F))
    x.r.Y.tup x.r.Y.eMt 1 x.m.intersectionNumber_baseChange.ok.ok2 le_rfl
    ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) M Tn
    hTup hTw (fun i y _ => ⟨x.r.Y.formsL i _, x.r.Y.latL i _, hZ0 i _⟩) hstd Q hQ hlat hT hR hAV hCS x.r.Z.jW rfl
    (fun i y _ x' => hθ i _ x') hE hI h42 hZ hG
  obtain ⟨i, rfl⟩ : ∃ i : Fin (Dof x).R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine (key i v').trans (Eq.trans ?_ (x.m.eta _ v'))
  unfold Rw.etaOf
  rw [dif_pos ⟨by omega, i.2⟩]
  split_ifs with ha hb hb
  · simp only [Nat.add_sub_cancel, Fin.eta]
    rfl
  · exact (hb ha).elim
  · exact (ha hb).elim
  · rfl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaJ_local_compatibility_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.etaJ_with_local_data_eq_alt | exact _root_.GlobalTheory.etaJ_with_local_data_eq_alt | (intros; apply _root_.GlobalTheory.etaJ_with_local_data_eq_alt <;> assumption)
end
end
