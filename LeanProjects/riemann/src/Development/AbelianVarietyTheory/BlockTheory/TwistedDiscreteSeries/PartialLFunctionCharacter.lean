import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NotRootUnity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult IsDedekindDomain NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

variable {D : D7}

def TrivialOnF (χ : (AE D)ˣ →* Circle) : Prop := ∀ a : (AF D.host.F)ˣ, χ (idF D a) = 1

def lPartial (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) (s : ℂ) : ℂ :=
  ∏' P : {P : HeightOneSpectrum (𝓞 D.host.E) // OffS D S P}, Mi.lfac χ P.1 s

def IsPartialL (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re →
    HasProd (fun P : {P : HeightOneSpectrum (𝓞 D.host.E) // OffS D S P} => Mi.lfac χ P.1 s) (Λ s)

def IsFiniteL (χ : (AE D)ˣ →* Circle) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re →
    HasProd (fun P : HeightOneSpectrum (𝓞 D.host.E) => Mi.lfac χ P s) (Λ s)

def PosUpTo (t : ℕ) (Λ : ℂ → ℂ) : Prop := ∀ n : ℕ, 1 ≤ n → n ≤ t → (Λ n).im = 0 ∧ 0 < (Λ n).re

def HeckeRatioPos (D : D7) : Prop :=
  ∀ μ μ' : (AE D)ˣ →* Circle, IsHeckeChar D μ → IsHeckeChar D μ' → TrivialOnF μ → TrivialOnF μ' →
    (∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D μ τ (-e) ∧ HasInfExp D μ' τ (-e') ∧ e ≠ e') →
    ∀ t : ℕ,
      (∃ Λ : ℂ → ℂ, IsFiniteL (μ * μ'⁻¹) Λ ∧ PosUpTo t Λ) ∧
      ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∃ Λ : ℂ → ℂ, IsPartialL S (μ * μ'⁻¹) Λ ∧ PosUpTo t Λ

theorem IsPartialL.eq_lPartial {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {χ : (AE D)ˣ →* Circle} {Λ : ℂ → ℂ}
    (h : IsPartialL S χ Λ) {s : ℂ} (hs : 1 < s.re) : Λ s = lPartial S χ s := (h.2 s hs).tprod_eq.symm

theorem IsFiniteL.eq_lEuler {χ : (AE D)ˣ →* Circle} {Λ : ℂ → ℂ} (h : IsFiniteL χ Λ) {s : ℂ} (hs : 1 < s.re) :
    Λ s = Mi.lEuler χ s := (h.2 s hs).tprod_eq.symm

theorem eq_of_eqOn_re {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2) (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) ?_
  have : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  exact Filter.mem_of_superset this h

theorem IsPartialL.unique {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {χ : (AE D)ˣ →* Circle} {Λ Λ' : ℂ → ℂ}
    (h : IsPartialL S χ Λ) (h' : IsPartialL S χ Λ') : Λ = Λ' :=
  eq_of_eqOn_re h.1 h'.1 fun _ hs => (h.eq_lPartial hs).trans (h'.eq_lPartial hs).symm

theorem IsFiniteL.unique {χ : (AE D)ˣ →* Circle} {Λ Λ' : ℂ → ℂ} (h : IsFiniteL χ Λ) (h' : IsFiniteL χ Λ') : Λ = Λ' :=
  eq_of_eqOn_re h.1 h'.1 fun _ hs => (h.eq_lEuler hs).trans (h'.eq_lEuler hs).symm

example (P : HeightOneSpectrum (𝓞 D.host.E)) : OffS D ∅ P := fun _ h => absurd h (Finset.notMem_empty _)

end GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

end
