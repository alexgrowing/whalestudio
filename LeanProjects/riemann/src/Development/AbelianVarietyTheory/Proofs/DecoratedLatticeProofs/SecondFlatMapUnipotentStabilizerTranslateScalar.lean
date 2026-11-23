import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem GlobalTheory.FinPl.flatFB_om_shift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LW : Lat B.V) (v : Pl D), IsSelfDualC J.W LV → IsSelfDualC B.V LW → Tame D v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ (x : GA D B.V) (κ : GA D B.V), InK B.V LW (· = v) κ → flatFB s (s.om (1, n * x * κ) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s (s.om (1, x) f) := by
  intro D ψ σ J B s LV LW v hLV hLW hv hu f hf n hn hnv x κ hκ
  have hmul : s.om (1, n * x * κ) f = s.om (1, n) (s.om (1, x) (s.om (1, κ) f)) := by
    have : ((1 : GA D J.W), n * x * κ) = (1, n) * (1, x) * (1, κ) := by simp
    rw [this, map_mul, map_mul]; rfl
  have hκf : s.om (1, κ) f = f := by
    refine GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hLV hLW (· = v) ?_ f hf 1 κ ?_ hκ
    · rintro w rfl; exact ⟨hv, hu.1, hu.2⟩
    · refine ⟨one_mem _, ?_⟩
      intro y _
      simp
  have hth : IsThetaFunO ψ J.W B.V (s.om (1, x) f) := s.weil.om_pres _ _ hf.1
  have h := ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B s).equiv _ hth n hn hnv 1 (one_mem _)
  have he : B.o.emb (1, 1) = 1 := map_one B.o.emb
  have he₀ : s.om₀ ((1 : GA D J.W₀), (1 : GA D B.V₀)) = 1 := map_one s.om₀
  rw [map_one, mul_one, he, he₀, Module.End.one_apply] at h
  rw [hmul, hκf, h]
