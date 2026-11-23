import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7} {a b : ℕ}

def EvGood (Φ : Mx D a b → ℂ) : Prop :=
  ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ

theorem good_zero (S : Finset (Pl D)) (e : AE D) : Good S e (0 : Mx D a b → ℂ) := by
  intro x
  split_ifs <;> rfl

theorem good_add {S : Finset (Pl D)} {e : AE D} {Φ Ψ : Mx D a b → ℂ} (hΦ : Good S e Φ) (hΨ : Good S e Ψ) :
    Good S e (Φ + Ψ) := by
  intro x
  simp only [Pi.add_apply]
  rw [hΦ x, hΨ x]
  split_ifs with h
  · rfl
  · simp

theorem good_smul {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : Good S e Φ) :
    Good S e (c • Φ) := by
  intro x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hΦ x]
  split_ifs with h
  · rfl
  · simp

theorem evGood_zero : EvGood (0 : Mx D a b → ℂ) :=
  ⟨∅, fun S _ e _ => good_zero S e⟩

theorem evGood_add {Φ Ψ : Mx D a b → ℂ} (hΦ : EvGood Φ) (hΨ : EvGood Ψ) : EvGood (Φ + Ψ) := by
  classical
  obtain ⟨S₁, h₁⟩ := hΦ
  obtain ⟨S₂, h₂⟩ := hΨ
  exact ⟨S₁ ∪ S₂, fun S hS e he =>
    good_add (h₁ S (Finset.union_subset_left hS) e he) (h₂ S (Finset.union_subset_right hS) e he)⟩

theorem evGood_smul {Φ : Mx D a b → ℂ} (c : ℂ) (hΦ : EvGood Φ) : EvGood (c • Φ) := by
  obtain ⟨S₀, h⟩ := hΦ
  exact ⟨S₀, fun S hS e he => good_smul c (h S hS e he)⟩

theorem evGood_span {s : Set (Mx D a b → ℂ)} (hs : ∀ φ ∈ s, EvGood φ) :
    ∀ Φ ∈ Submodule.span ℂ s, EvGood Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact evGood_zero
  | add x y _ _ hx hy => exact evGood_add hx hy
  | smul c x _ hx => exact evGood_smul c hx

theorem ev_span {θ : InfFam D} (s : Set (Mx D a b → ℂ)) (hs : schwartzA θ a b = Submodule.span ℂ s)
    (h : ∀ φ ∈ s, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e φ) :
    ∀ Φ ∈ schwartzA θ a b, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → Good S e Φ := by
  intro Φ hΦ
  rw [hs] at hΦ
  exact evGood_span h Φ hΦ

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
