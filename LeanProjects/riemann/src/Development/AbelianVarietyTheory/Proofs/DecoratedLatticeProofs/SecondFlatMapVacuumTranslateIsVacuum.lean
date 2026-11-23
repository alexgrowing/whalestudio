import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.VacSecondPf

variable {D : D7}

theorem latO_of_none (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (hP : ∀ v, ¬ P v) : latO S T LS LT P = ⊥ := by
  rw [eq_bot_iff, latO, AddSubgroup.closure_le]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    ext v : 1
    exact hα v (hP v)
  subst h0
  rw [SetLike.mem_coe, AddSubgroup.mem_bot]
  have hp : pairA D.host.F 0 0 = 0 := rfl
  ext i j
  simp [hp]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem vac_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ P hP f hf h₁ hh₁ h₂ hh₂
  have hflat : ∀ Q : Pl D → Prop, IsFlatFB s Q (flatFB s) := fun Q => (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ Q).2 σ J B s
  have htheta : IsThetaFunO ψ J.W B.V (s.om (h₁, h₂) f) := s.weil.om_pres _ _ hf.1
  have hth0 : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (h₁, h₂) f)) := (hflat P).Heisenberg₂.theta _ htheta
  by_cases hne : ∃ v, P v
  · obtain ⟨v₀, hv₀⟩ := hne
    have a₀ := (hP v₀ hv₀).1
    have hT : ∀ v, P v → Tame D v := fun v hv => (hP v hv).1.tame
    have L1 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW a₀.sdV a₀.sdW P hT
    have L0 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ a₀.sdV₀ a₀.sdW₀ P hT
    have hg : Vac ψ J.W B.V LV LW P (s.om (h₁, h₂) f) := (L1 f).2.1 hf h₁ hh₁ h₂ hh₂
    have hgv := ((L1 _).1.mp hg).2
    refine (L0 _).1.mpr ⟨hth0, fun v hv => ?_⟩
    exact (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B s LV LV₀ LW LW₀ v (hP v hv).1 (hP v hv).2 (flatFB s) (hflat (· = v))
      ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B s) _ (hgv v hv)).1
  · push_neg at hne
    have hbot := latO_of_none J.W₀ B.V₀ (LV₀ : Set _) (LW₀ : Set _) P hne
    refine ⟨hth0, ?_, ?_⟩
    · intro u hu
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [two_nsmul, add_zero, heisO_zero]
    · intro e _ u hu _
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [heisO_zero]

end GlobalTheory.VacSecondPf
