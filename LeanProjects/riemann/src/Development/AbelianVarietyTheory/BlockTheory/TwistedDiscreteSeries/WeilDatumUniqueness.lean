import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

variable {D : D7}

def TrivOnF (D : D7) (ξ : (AE D)ˣ →* Circle) : Prop := ∀ a : (AF D.host.F)ˣ, ξ (idF D a) = 1

def IsTildeDet (V : HSp D) (ξ : (AE D)ˣ →* Circle) (g : GA D V) (c : Circle) : Prop :=
  (∃ x, IsDetRoot V g x) ∧ ∀ x, IsDetRoot V g x → ξ x = c

def WeilDatumUnique (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' →
      ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → om' (g, h) f = om (g, h) f

def WeilDatumTwist (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT ξ ξ' : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    TrivOnF D ξ → TrivOnF D ξ' →
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T (χS * ξ) (χT * ξ') om' →
      ∀ (g : GA D S) (h : GA D T), ∃ a b : Circle, IsTildeDet S ξ' g a ∧ IsTildeDet T ξ h b ∧
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
          om' (g, h) f = ((a⁻¹ * b : Circle) : ℂ) • om (g, h) f

def WeilDatumDetermined (D : D7) : Prop := WeilDatumUnique D ∧ WeilDatumTwist D

theorem IsTildeDet.unique {V : HSp D} {ξ : (AE D)ˣ →* Circle} {g : GA D V} {c c' : Circle}
    (h : IsTildeDet V ξ g c) (h' : IsTildeDet V ξ g c') : c = c' := by
  obtain ⟨x, hx⟩ := h.1
  rw [← h.2 x hx, ← h'.2 x hx]

theorem IsTildeDet.at_one {V : HSp D} {ξ : (AE D)ˣ →* Circle} {c : Circle} (h : IsTildeDet V ξ 1 c) : c = 1 := by
  have h1 : IsDetRoot V 1 1 := by simp [IsDetRoot]
  rw [← h.2 1 h1, map_one]

theorem WeilDatumTwist.unique (H : WeilDatumTwist D) : WeilDatumUnique D := by
  intro ψ S T χS χT om om' h h' g k f hf
  obtain ⟨a, b, ha, hb, e⟩ := H ψ S T χS χT 1 1 om om' (fun _ => rfl) (fun _ => rfl) h
    (by simpa using h') g k
  obtain ⟨x, hx⟩ := ha.1
  obtain ⟨y, hy⟩ := hb.1
  have ha1 : a = 1 := (ha.2 x hx).symm
  have hb1 : b = 1 := (hb.2 y hy).symm
  simpa [ha1, hb1] using e f hf

end GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

end
