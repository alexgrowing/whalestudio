import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenPrincipalCongruenceFinitelyManyPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.PrinMeas

variable {D : D7}

theorem proj_mem_stabLoc_of_mem_prinInf (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D))
    (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (hfr : Formalism.L2.DIV.IsFrame β (frameLat A)) {g : GA D A}
    (hg : g ∈ prinInf A β Z) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    proj D.sp.cm.sig A.gram v g ∈ stabLoc D.sp.cm.sig A.gram (frameLat A) v :=
  (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D A β (frameLat A) hfr g).1 (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg)) v

theorem frameInv_eq_one {θ : InfFam D} {A : HSp D} {cA : CptF A} {a : GL (Fin A.rank) (AE D)} (h : Defin θ A cA a)
    (τ : D.what₂.Tau) : frameInv θ A a τ = 1 := by
  have h3 := h.maj_eq τ
  rw [Matrix.mul_one] at h3
  rw [frameInv, Matrix.mul_assoc]
  exact mul_eq_one_comm.1 h3

theorem prinInf_props : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Formalism.L2.DIV.IsFrame β (frameLat A) → ∀ m : Measure (GA D A), m.IsHaarMeasure → MeasurableSet (prinInf A β Z) ∧ prinInf A β Z ⊆ openOff A (frameLat A) (under Z) ∧ (∀ g ∈ prinInf A β Z, hgtL A (frameLat A) a g = 1) ∧ ∃ mR : Measure (GinfC A), mR.IsHaarMeasure ∧ ∀ F : GA D A → ℂ, Continuous F → (∀ (b : GinfC A), ∀ κ ∈ prin A β Z, F ((b : GA D A) * κ) = F b) → ∫ g in prinInf A β Z, F g ∂m = ∫ b : GinfC A, F b ∂mR := by
  intro D θ A cA a hD β Z hfr m hm
  haveI := hm
  set K := prin A β Z
  let S : Subgroup (GA D A) := (Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z)).comap (Formalism.IndefR.Lev.finE A)
  have hSset : (S : Set (GA D A)) = prinInf A β Z := rfl
  have hstab : ∀ g ∈ S, ∀ v, proj D.sp.cm.sig A.gram v g ∈ stabLoc D.sp.cm.sig A.gram (frameLat A) v :=
    fun g hg v => proj_mem_stabLoc_of_mem_prinInf A β Z hfr hg v

  obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D A β Z
  have hUS : U ≤ S := fun k hk => by
    refine Subgroup.mem_comap.2 (GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm A.gram β (prinDat A Z) _
      (GlobalTheory.LevSplit.finE_mem_UA A k) (hUk k hk).1 fun PP hPP => ?_)
    rcases hPP with h | h
    · exact (hUk k hk).2 PP h
    · exact absurd h (Finset.notMem_empty PP)
  have hSopen : IsOpen (S : Set (GA D A)) := Subgroup.isOpen_mono hUS hU

  have hfinK : ∀ g ∈ S, (GlobalTheory.AutMult.toFin A g : GA D A) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin A g).2, Subgroup.mem_comap.2 (by
      rw [GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩
  have hker : {g : GA D A | g ∈ S ∧ GlobalTheory.AutMult.toInf A g = 1} = (K : Set (GA D A)) := by
    ext g
    simp only [Set.mem_setOf_eq, GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D A)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D A (frameLat A) (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) K inf_le_left
      (fun k hk v => hstab k hk.2 v) ⟨U, hU, fun k hk hkf => ⟨hkf, hUS hk⟩⟩
  have hpi : ∀ b : GinfC A, GlobalTheory.AutMult.toInf A ((GinfC A).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiS : ∀ b : GinfC A, (GinfC A).subtype b ∈ S := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, GlobalTheory.ChainOnto.HaarInf.finE_of_mem_ginfC A b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf A) (m.restrict (S : Set (GA D A)))).IsHaarMeasure :=
    GlobalTheory.T.map_restrict_isHaar_of_open_product_compact (GA D A) (GinfC A) m S (GinfC A).subtype (GlobalTheory.AutMult.toInf A) hSopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf A) hpi hiS (hker ▸ hKc)
  refine ⟨hSopen.measurableSet, fun g hg v _ => hstab g hg v, fun g hg => ?_, _, hHaar, fun F hF hinv => ?_⟩
  ·
    have hK : g ∈ Kmax A a := by
      refine (hD.maj.mem_Kmax_iff hD.inf g).2 ⟨mem_levelOpen.2 (hstab g hg), fun τ => ?_⟩
      rw [frameInv_eq_one hD τ]
      exact Commute.one_right _
    have := hgt_mul A a 1 ((io_mem_Khat A a).2 ⟨hK, one_mem _⟩)
    change hgt A a (io A (g, 1)) = 1
    simpa using this
  · have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf A) (m.restrict (S : Set (GA D A))) :=
      (GlobalTheory.AutMult.continuous_toInf A).measurable.aemeasurable
    have hFA : ∀ g ∈ (S : Set (GA D A)), F g = (fun b : GinfC A => F b) (GlobalTheory.AutMult.toInf A g) := fun g hg => by
      conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
      exact hinv _ _ (hfinK g hg)
    have hf : AEStronglyMeasurable (fun b : GinfC A => F b)
        (Measure.map (GlobalTheory.AutMult.toInf A) (m.restrict (S : Set (GA D A)))) :=
      (hF.comp continuous_subtype_val).aestronglyMeasurable
    rw [← hSset, setIntegral_congr_fun hSopen.measurableSet hFA, integral_map hmeas hf]

end GlobalTheory.Core.Rk.PrinMeas
