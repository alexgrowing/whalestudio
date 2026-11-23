import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PkOf
section Heq
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7}
end Heq
end GlobalTheory.Fam.PkOf
namespace GlobalTheory.Fam
theorem pkHyp_of_real_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin W.R W.S W.Q) → (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) → GlobalTheory.MiS.DcPtG W.P → _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx W.Q → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation W.Q → _root_.Formalism.IndefR.IndefiniteRealisationExtends W.Q → _root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q → W.Q.Rl.toRealDat.ExAt → Formalism.IndefR.Links.PrimRows3 W.Q.Rl W.Q.F → W.P.A3.fam3.TypesSep3 → (∃ s, W.P.A3.fam3.Ok3 s) → GlobalTheory.Core.Mi.IdE W.S.X → GlobalTheory.Count.GapGe W.S.X.B (100 * (B.R.r : ℝ) ^ 4) → Formalism.L2.SG.PackageTie2.FinX W.S.Y → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap (I.rec7 l Z) → _root_.GlobalTheory.Fam.ValidRealPackage W → _root_.GlobalTheory.Fam.GeometricFamilyConditions W → _root_.GlobalTheory.Fam.PackageHypotheses W := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hJ hLM hDc hFr hPins hSee hRec hEx hPrim hTS hOk3 hIdE hGap hFinX hNG hTW hTQ
  have hC3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hEx
  have hU : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 _ (W.P.I.tup t) := by
    apply Formalism.L2.DIV.tupAllUsed_of_cover
    intro t
    have hmu : W.Q.Rl.mu = W.P.S0.μ :=
      GlobalTheory.Fam.PkOf.mu_of_heq (congrArg (fun Z => W.P.A3.side3 W.P.P0 W.P.ψ0 Z) W.Q.zs) W.Q.s0
    rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨(I.rec7 l Z).plEq.symm w, ?_⟩
      show t = W.P.S0.μ ((I.rec7 l Z).plEq ((I.rec7 l Z).plEq.symm w))
      rw [← hmu, Equiv.apply_symm_apply]
      exact h.symm
  refine ⟨⟨⟨hJ, hLM, hDc, hC3, W.Q.frames hFr⟩, hPins, hSee, hU, hIdE, hGap, hFinX⟩, ?lev, hEx, hRec.hTop, hNG, ?fin, ?sel, ?aa⟩
  case lev =>
    obtain ⟨s, hs⟩ := hOk3
    have hR := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hs hTS W.Q.charW hPrim
    exact ⟨⟨s, hs⟩, hR.ratZ, _, hR.gUnit, hR.gEquiv, hR.h2P, hR.lev0, hR.lev1⟩
  case fin =>
    classical
    have h1 := W.Q.charW.tup.mu_off
    have h2 := W.Q.charW.tup.mu_used
    have : (Set.univ : Set W.P.T) ⊆ insert W.P.A3.A.μ0 (W.Q.Rl.mu '' (W.Q.Rl.twPl : Set _)) := fun t _ => by
      rcases h2 t with h | ⟨w, rfl⟩
      · exact Or.inl h
      · by_cases hw : w ∈ W.Q.Rl.twPl
        · exact Or.inr ⟨w, hw, rfl⟩
        · exact Or.inl (h1 w hw)
    exact Set.finite_univ_iff.1 ((((W.Q.Rl.twPl).finite_toSet.image _).insert _).subset this)
  case sel =>
    rintro PP PP' ⟨t, ht⟩ ⟨t', ht'⟩ hu
    have hs := hTW.ok.sel_ok
    obtain ⟨v, rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t PP).1 ht)
    obtain ⟨v', rfl⟩ := GlobalTheory.Fam.PkOf.exists_of_mem_QE ((hTQ.Q t' PP').1 ht')
    have e1 := congrArg HeightOneSpectrum.asIdeal hu
    have hv : v = v' := by
      apply HeightOneSpectrum.ext
      rw [← hs v, ← hs v']
      exact e1
    rw [hv]
  case aa =>
    intro PP h hmem
    have hcop := (I.rec7 l Z).host.ccK_coprime
    rcases h with ⟨t, ht⟩ | hg | ⟨u, hu⟩
    · apply hPins.qGuard.2 t PP ht
      push_cast
      exact Ideal.mul_mem_left _ _ hmem
    · obtain ⟨plg, iso, -, -, -, -⟩ := hPins.grpRecPin
      set kv := plg.symm ⟨PP, hg⟩ with hkv
      have hPP : ((plg kv : W.Q.Rl.toRealDat.Pg) : Pl (I.rec7 l Z).host.E) = PP := by
        rw [hkv, Equiv.apply_symm_apply]
      have h0 : (((I.rec7 l Z).host.g kv.1 : ℕ) : kP (plg kv).1) = 0 := by
        rw [← map_natCast (iso kv), ZMod.natCast_self, map_zero]
      have hg' : (((I.rec7 l Z).host.g kv.1 : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rw [← hPP]
        exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using h0)
      exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).host.g_level kv.1])) hg' hmem
    · exact GlobalTheory.Fam.PkOf.natCast_not_mem_of_coprime PP
        (hcop _ (by simp [(I.rec7 l Z).T_level u])) hu hmem
end GlobalTheory.Fam
end
end
