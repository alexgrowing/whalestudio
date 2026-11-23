import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.AllPlaceRigidityResidual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegreesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem of_eq_of_isSpeh {w : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (σ : SmIrr (GL (Fin N) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N') (w.adicCompletion E))) (x : GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) (d : ℕ)
    (h : GlobalTheory.LocGL.IsSpeh x d σ.ρ) (h' : GlobalTheory.LocGL.IsSpeh x d σ'.ρ) :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨hd, hc⟩ := h
  obtain ⟨hd', hc'⟩ := h'
  obtain rfl : N = N' := hd.symm.trans hd'
  exact GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.LocGL.IsCosocle.unique hc' hc)

theorem ascEmb_of_sigma {N a a' d : ℕ} {V : Submodule ℂ (Sm E N)} (P : CuspSub E a) (P' : CuspSub E a')
    (h : ∀ P'' : CuspSub E a', P'.Iso P'' → AscEmb V P'' d)
    (e : (⟨a', CG.mk P'⟩ : Σ b, CG E b) = ⟨a, CG.mk P⟩) : AscEmb V P d := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp e
  exact h P (Quotient.exact (eq_of_heq he))

theorem rLoc : RLoc := by
  intro hJS hSS hStr E _ _ _ n D D' hr hr' hsat
  choose a d P ha hd hPu hPn hPs using hStr E n D hr
  choose a' d' P' ha' hd' hPu' hPn' hPs' using hStr E n D' hr'
  have he : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hPs i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have he' : ∀ j, AscEmb (D'.V j) (P' j) (d' j) := fun j =>
    hPs' j (P' j) (Setoid.refl (α := CuspSub E (a' j)) (P' j))
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E
  have h1 := Filter.eventually_all.2 fun i => hSS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i)
    (D.discrete i) (hPu i) (hPn i) (he i) (D.loc i) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d i) k))
    (fun k => hν _)
  have h2 := Filter.eventually_all.2 fun j => hSS E (D'.N j) (a' j) (d' j) (D'.V j) (P' j) (D'.σ j) (D'.pos j)
    (D'.discrete j) (hPu' j) (hPn' j) (he' j) (D'.loc j) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d' j) k))
    (fun k => hν _)
  obtain ⟨s, hs⟩ := GlobalTheory.Published.JacquetShalikaRigidity.unitary hJS (ι := Σ i, Fin (d i)) (κ := Σ j, Fin (d' j))
    (fun x => CG.mk (P x.1)) (fun y => CG.mk (P' y.1)) (fun x => ha x.1) (fun y => ha' y.1)
    (fun x => (CG.isUnitary_mk _).2 (hPu x.1)) (fun y => (CG.isUnitary_mk _).2 (hPu' y.1)) _ hν
    (fun x => spehExp (d x.1) x.2) (fun y => spehExp (d' y.1) y.2) (by
      filter_upwards [h1, h2, hsat] with w hw hw' hB
      obtain ⟨B, ⟨b, hb, hbB⟩, ⟨b', hb', hbB'⟩⟩ := hB
      choose c hc hsph hcs using hw
      choose c' hc' hsph' hcs' using hw'
      refine ⟨fun x => c x.1 x.2, fun y => c' y.1 y.2, fun x => hc x.1 x.2, fun y => hc' y.1 y.2, ?_⟩
      rw [Fintype.sum_sigma, Fintype.sum_sigma]
      have e1 : ∀ i, ∑ k, c i k = b i := fun i => (hcs i).unique (hb i).2
      have e2 : ∀ j, ∑ k, c' j k = b' j := fun j => (hcs' j).unique (hb' j).2
      simp only [e1, e2]
      exact hbB.trans hbB'.symm)
  have hstr := GlobalTheory.Rigid.strings_eq_of_equiv (fun i => (⟨a i, CG.mk (P i)⟩ : Σ b, CG E b)) d
    (fun j => (⟨a' j, CG.mk (P' j)⟩ : Σ b, CG E b)) d' s fun x => ⟨(hs x).1, (hs x).2⟩
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.multiset_of_strings_determines_points_degrees _ d _ d' hd hd' hstr
  refine ⟨s0, fun i w => ?_⟩
  have hA : AscEmb (D'.V (s0 i)) (P i) (d i) := by
    rw [(hs0 i).2]
    exact ascEmb_of_sigma (P i) (P' (s0 i)) (hPs' (s0 i)) (hs0 i).1.symm
  obtain ⟨σ0, hσ0, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E (a i) (P i) w
  have k1 := ascSeed_holds2.2 E (D.N i) (a i) (d i) (D.V i) (P i) (D.pos i) (D.discrete i) (hPu i) (hPn i) (he i)
    w σ0 (D.σ i w) hσ0 (D.loc i w)
  have k2 := ascSeed_holds2.2 E (D'.N (s0 i)) (a i) (d i) (D'.V (s0 i)) (P i) (D'.pos _) (D'.discrete _) (hPu i)
    (hPn i) hA w σ0 (D'.σ (s0 i) w) hσ0 (D'.loc _ w)
  exact of_eq_of_isSpeh _ _ _ _ k1 k2

end PositivityTheory.Rg.BcB.F.Rig

end
