import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaEqLam
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.LamPosTw

theorem eigenvalue_twistedWeight_pos : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → 0 < (w.D Z).what₂.lamP ((w.D Z).what₂.muTw v) j σ := by
  intro hP hL
  have e1 := evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  have e0 : EvLgG fun _ _ _ _ => True :=
    e1.imp fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ => trivial⟩
  unfold AtMem
  refine (e0.inter e1).imp fun K _ _ _ _ H => ?_
  obtain ⟨hK, hH⟩ := H
  refine hK.imp fun B f T hO _ _ w Z Wt p0 t nch n xd c _ _ _ v hTw j hj1 hjm σ hne => ?_
  letI : Algebra (↥t.r.z.core.Q.c.F) (w.D Z).what₂.LL := t.r.z.alg
  have host : Formalism.IndefR.Links.HostHyp (w.D Z) := (hH (w.st Z) hO).1
  obtain ⟨p, hp⟩ := GlobalTheory.Mem.LamPosTw.hasLab_exists hP.decay (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0
    t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange host σ
  have hi : j - 1 < (w.D Z).R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin (w.D Z).R.m) : ℕ) + 1 = j := by simp only; omega
  have hmu : (w.D Z).what₂.muTw v = t.r.Y.tup (t.r.z.R.mu ((w.D Z).plEq v)) := by
    rcases (w.D Z).what₂.muAt_or v with h | h
    · exact absurd h hTw
    · rw [← h]; exact t.r.Y.muAt v
  have key := GlobalTheory.Mem.LamPosTw.eigenvalue_eq_of_label (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.Z t.r.z.pins
    t.r.intersectionNumber_baseChange host σ p ⟨j - 1, hi⟩ (t.r.z.R.mu ((w.D Z).plEq v)) hp (Or.inr ⟨v, (t.r.Y.muAt v).symm⟩) (by rw [hj']; exact hne)
  rw [hj'] at key
  rw [hmu, key]
  exact t.r.intersectionNumber_baseChange.prim.posScal.2 _ _ _ _

end GlobalTheory.Mem.LamPosTw
