import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

variable {D : D7} {V : HSp D}

theorem levelFam_open_compact (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧
      IsCompact (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) := by
  by_cases hu : v = U.u
  · subst hu
    rw [levelFam_u]
    exact ⟨U.frame.isOpen_iwahori, U.frame.isCompact_iwahori⟩
  by_cases hv : v ∈ T.S
  · have e : levelFam T U v = kerSub T ⟨v, hv⟩ := by
      rw [levelFam, Function.update_of_ne hu, dif_pos hv]
    rw [e]
    have ho : IsOpen (kerSub T ⟨v, hv⟩ : Set (GLoc D.sp.cm.sig V.gram v)) := by
      rw [kerSub, Subgroup.coe_map]
      exact (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v).isOpenMap_subtype_val _
        (T.frame ⟨v, hv⟩).isOpen_ker_red
    refine ⟨ho, (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ ho) ?_⟩
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [levelFam_of_notMem T U hv hu]
    exact ⟨isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v, isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v⟩

theorem isFinFamily_fam : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V)
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) →
    (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → U.u ∉ T.S → ∀ A,
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fam T U μf A) := by
  intro D V T U μf _ h1 _ A
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v ∈ T.S ∧ v ∈ A
    · rw [fam_of_mem T U μf A hv.1 hv.2]
      exact (T.frame ⟨v, hv.1⟩).idem_mem _ _
    · rw [fam_of_not T U μf A hv, normInd]
      obtain ⟨ho, hc⟩ := levelFam_open_compact T U v
      exact Submodule.smul_mem _ _ (indicator_mem_SB ho hc)
  · filter_upwards [T.S.eventually_cofinite_notMem, eventually_cofinite_ne U.u, h1] with v hS hU hK
    rw [fam_of_not T U μf A (fun h => hS h.1), levelFam_of_notMem T U hS hU, normInd, measureReal_def]
    funext g
    simp only [Pi.smul_apply, unitLoc]
    rw [hK]
    simp

end GlobalTheory.TrIdem
