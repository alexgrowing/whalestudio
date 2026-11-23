import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw.VacShape

theorem nonempty_pl (D : D7) : Nonempty (Pl D) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩⟩

theorem vacOfShape : ∀ D : D7, GlobalTheory.SeeSaw.VacOfShape D := by
  intro D c v k _ _ _ _ ι o hc hv hs t
  obtain ⟨x₀⟩ := nonempty_pl D
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∉ v.tP)
  have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hc.std
  refine ⟨?_, ?_⟩
  · intro j σ h Ψ₁ Ψ₂ h₁ h₂
    have f₁ := hFV.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) (v.N j) (o.M j (σ + 1) h)
      (v.N (j + 1)) (c.x (j + 1)).L (fun x _ => (hs.good x).bf j (σ + 1) h) Ψ₁ h₁
    have f₂ := hFV.2.1 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) (v.N (j + 1)) (c.x (j + 1)).L
      (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) (fun x _ => (hs.good x).fb j σ h) Ψ₂ h₂
    have hg0 := (hs.good x₀).bf j (σ + 1) h
    have hg1 := (hs.good x₀).fb j σ h
    have hor : ∀ x, x ∉ v.tP → (∃ LL, OrthAt (c.B j (σ + 1) h).o (o.M j (σ + 1) h) (c.x j).L LL x) ∧
        ∃ LL, OrthAt (c.B (j + 1 + 1) σ (idx_step h)).o (o.M (j + 1 + 1) σ (idx_step h)) (c.x (j + 1 + 1)).L LL x := by
      intro x hx
      obtain ⟨LL, _, hLL⟩ := (hs.split x hx).core j (σ + 1) h
      obtain ⟨LL', _, hLL'⟩ := (hs.split x hx).core (j + 1 + 1) σ (idx_step h)
      exact ⟨⟨LL, hLL⟩, ⟨LL', hLL'⟩⟩
    exact (hCC (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h)
      _ _ f₁.1 f₂.1).2.2 (· ∉ v.tP) (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (o.M j (σ + 1) h)
      (o.M (j + 1 + 1) σ (idx_step h)) (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd hg0.sdV₀ hg1.sdW₀ hor f₁ f₂
  · intro j h Ψ₁ Ψ₂ h₁ h₂
    have f₁ := hFV.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) (v.N j) (o.M j 0 h) (v.N (j + 1)) (c.x (j + 1)).L
      (fun x _ => (hs.good x).bf j 0 h) Ψ₁ h₁
    have f₂ := hFV.2.2 (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d (v.N (j + 1)) (c.x (j + 1)).L v.NT
      (hv.sd (j + 1) (by omega)) (hc.x (j + 1) (by omega)).sd hv.sdT (fun x _ => ((hs.good x).bf j 0 h).monoW) Ψ₂ h₂
    have hg0 := (hs.good x₀).bf j 0 h
    exact GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both D c.ψ hc.std _ (c.X j) _ (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o
      (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hs.pre.line.1 (hs.pre.tau j h) (· ∉ v.tP) (o.M j 0 h)
      (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L v.NT hg0.sdV₀ (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd hv.sdT (fun x hx => ⟨((hs.good x).bf j 0 h).tame, (hs.split x hx).top j h⟩)
      _ _ f₁ f₂

end GlobalTheory.SeeSaw.VacShape

end
