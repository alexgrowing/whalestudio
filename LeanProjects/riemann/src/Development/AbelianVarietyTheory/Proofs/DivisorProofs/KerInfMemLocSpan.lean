import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def locSpan (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) : Submodule ℂ (GA E a → ℂ) :=
  sInf {V | F₀ ∈ V ∧ (∀ F ∈ V, ∀ h ∈ supS E a S, (fun g => F (g * h)) ∈ V) ∧
    ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V}

variable {S : Finset (HeightOneSpectrum (𝓞 E))} {F₀ : GA E a → ℂ}

theorem self_mem_locSpan : F₀ ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun _ hV => hV.1

theorem rt_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {h : GA E a} (hh : h ∈ supS E a S) :
    (fun g => F (g * h)) ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.1 F (Submodule.mem_sInf.1 hF V hV) h hh

theorem kerInf_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.2 F (Submodule.mem_sInf.1 hF V hV) X ν k γ hk

theorem locSpan_le {V : Submodule ℂ (GA E a → ℂ)} (h₁ : F₀ ∈ V)
    (h₂ : ∀ F ∈ V, ∀ h ∈ supS E a S, (fun g => F (g * h)) ∈ V)
    (h₃ : ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V) : locSpan S F₀ ≤ V :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem locSpan_le_rspan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ rspan π :=
  locSpan_le (mem_rspan hφ) (fun _ hF h _ => rt_mem_rspan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_rspan hF ν hk

theorem locSpan_le_mspanR {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ mspanR π := by
  rw [← rspan_eq_mspanR]; exact locSpan_le_rspan hφ

end GlobalTheory.JSW.MirSemi
