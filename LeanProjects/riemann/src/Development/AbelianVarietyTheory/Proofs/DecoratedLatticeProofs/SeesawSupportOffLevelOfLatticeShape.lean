import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAllStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamifiedStatement

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem offOfShape_of_supp (h1 : SuppFirst D) (h2 : SuppSecond D) : OffOfShape D := by
  intro c v k _ _ _ _ ι o hc hv hS t w ht hQ hU j σ h Φ₁ Φ₂ hΦ₁ hΦ₂
  have hD : DblShape (t.sBF j (σ + 1) h) (t.sFB j σ h)
      (⟨v.N j, o.M j (σ + 1) h, v.N (j + 1), (c.x (j + 1)).L, v.N (j + 1 + 1), o.M (j + 1 + 1) σ (idx_step h)⟩ :
        DblLat (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))) (offP v w) o.q
      ⟨o.β j, o.β₀ j (σ + 1) h, o.Q j⟩ ⟨o.β (j + 1), o.Q (j + 1)⟩
      ⟨o.β (j + 1 + 1), o.β₀ (j + 1 + 1) σ (idx_step h), o.Q (j + 1 + 1)⟩ :=
    { inj := hS.pre.inj
      mem := fun i => ⟨fun hg => Finset.disjoint_left.1 hv.disj hg ((hS.pre.tP _).2 ⟨i, rfl⟩),
        fun hg => Finset.disjoint_left.1 hQ hg ((hS.pre.tP _).2 ⟨i, rfl⟩)⟩
      good := fun x _ => (hS.good x).bf j (σ + 1) h
      adapt := fun x _ => (hS.good x).fb j σ h
      unr := fun x hx => ⟨hU.bf j (σ + 1) h x hx, hU.fb j σ h x hx⟩
      split := fun x _ hx => by
        obtain ⟨LL, a, b⟩ := (hS.split x fun hx' => by
          obtain ⟨i, hi⟩ := (hS.pre.tP x).1 hx'
          exact hx i hi).core (j + 1 + 1) σ (idx_step h)
        exact ⟨(c.x (j + 1 + 1)).L, LL, (hc.x _ (by omega)).sd, a, b⟩
      gl := fun i => hS.glued j (σ + 1) h i
      gl' := fun i => hS.glued (j + 1 + 1) σ (idx_step h) i
      mid := fun i => hS.pre.latT (j + 1) (by omega) i }
  have A := h1 c.ψ (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) _ _ _ _ (offP v w) hD.good
    (fun x hx => (hD.unr x hx).1) (hv.sd (j + 1) (by omega)) Φ₁ hΦ₁
  have B := h2 k ι o.p _ _ _ o.q c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ (offP v w) _ _ _ hD
    (hv.sd (j + 1 + 1) (by omega)) Φ₁ Φ₂ hΦ₁ hΦ₂
  have one : ∀ (S : HSp D) (L : Lat S), InK S L (offP v w) 1 := fun S L =>
    ⟨one_mem _, fun y _ => by simp [Formalism.L2.Theta.mt]⟩
  rw [← (ht.sBF j (σ + 1) h).1, ← (ht.sFB j σ h).1]
  refine ⟨fun κ hκ => ⟨A.1 1 κ (one _ _) hκ, B.1 κ 1 hκ (one _ _)⟩, fun κ hκ => B.1 1 κ (one _ _) hκ,
    (A.2 1 (one_mem _)).1, fun φ hφ h₂ => (B.2 1 (one_mem _)).2 1 (one_mem _) φ ?_ h₂⟩
  rw [hS.ram] at hφ
  exact hφ

theorem offOfShape_all : ∀ D : D7, OffOfShape D := fun D => offOfShape_of_supp (GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all D) (GlobalTheory.T.jacobiToBessel_second_step_flat_support_ramified D)

end GlobalTheory.SeeSaw

end
