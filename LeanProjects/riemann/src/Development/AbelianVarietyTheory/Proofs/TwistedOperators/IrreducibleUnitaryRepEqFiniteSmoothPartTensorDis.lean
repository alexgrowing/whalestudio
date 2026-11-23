import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroDiscreteSeriesInfiniteHomStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothVectorNeZeroOfDiscreteSeriesHomStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

theorem GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ hU : IsSubrep π ⊤, IsCopyFinDS (finPartDSSm M hU) M π ⊤ := by
  intro D V S M H _ _ _ π hπ hDS hU
  classical
  obtain ⟨Φ0, hΦ0, hne⟩ := GlobalTheory.T.exists_ne_zero_discreteSeriesInfiniteHom D V S M H π hπ hDS
  obtain ⟨Ψ0, hΨ0, hΨne⟩ := GlobalTheory.T.exists_smoothVector_ne_zero_of_discreteSeriesHom D V S M H π hπ.unitary hU ⟨Φ0, hΦ0⟩ (fun h => hne (congrArg Subtype.val h))
  let T : GlobalTheory.PRep.smoothPart (finPartDS M hU) →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
    (homDS M π ⊤).subtype ∘ₗ (GlobalTheory.PRep.smoothPart (finPartDS M hU)).subtype
  have hT : ∀ w, T w ∈ homDS M π ⊤ := fun w => w.1.2
  refine ⟨T, mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => rfl, fun i g w y => (hT w).2 i g y⟩,
    Subtype.val_injective.comp Subtype.val_injective, ?_⟩
  have hinv : ∀ g, ∀ v ∈ Submodule.span ℂ {v | ∃ w y, v = T w y}, π g v ∈ Submodule.span ℂ {v | ∃ w y, v = T w y} := by
    intro g v hv
    refine (Submodule.span_le (p := (Submodule.span ℂ {v | ∃ w y, v = T w y}).comap (π g : H →ₗ[ℂ] H))).2 ?_ hv
    rintro _ ⟨w, y, rfl⟩
    refine Submodule.subset_span ⟨finPartDSSm M hU (toFin V g) w, fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ), ?_⟩
    have e1 : π g (T w y) = π (toInf V g : GA D V) (π (toFin V g : GA D V) (T w y)) := by
      conv_lhs => rw [← toInf_mul_toFin g]
      rw [map_mul]; rfl
    have e2 : π (toFin V g : GA D V) (T w y) = T (finPartDSSm M hU (toFin V g) w) y := rfl
    change π g (T w y) = _
    rw [e1, e2]
    exact GlobalTheory.TrAct.toInf_apply_homDS D V S M H π ⊤ _ (hT _) g y
  rcases hπ.irred.2 _ (isSubrep_topologicalClosure hinv) with h | h
  · exfalso
    refine hΨne (Subtype.ext (ContinuousMultilinearMap.ext fun y => ?_))
    have : T ⟨Ψ0, hΨ0⟩ y ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, y, rfl⟩)
    rw [h, Submodule.mem_bot] at this
    simp only [ZeroMemClass.coe_zero, ContinuousMultilinearMap.zero_apply]
    exact this
  · exact h
