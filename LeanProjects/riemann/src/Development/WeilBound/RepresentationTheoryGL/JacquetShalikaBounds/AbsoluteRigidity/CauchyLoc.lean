import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import GroundTheory.AutomorphicForms.MacdonaldFormula

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.Spherical
open scoped ComplexConjugate

namespace PositivityTheory.RgJS

abbrev Off (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  {w : HeightOneSpectrum (𝓞 E) // w ∉ S}

def nq {E : Type} [Field E] [NumberField E] {S : Finset (HeightOneSpectrum (𝓞 E))} (w : Off E S) : ℕ :=
  Ideal.absNorm w.1.asIdeal

def LS {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) {m k : ℕ} (α : Off E S → Fin m → ℂˣ)
    (β : Off E S → Fin k → ℂˣ) (s : ℂ) : ℂ :=
  eul nq (fun w a => (α w a : ℂ)) (fun w b => (β w b : ℂ)) s

def pad {k : ℕ} (m : ℕ) (l : Fin k → ℤ) : Fin m → ℤ := fun a => if h : (a : ℕ) < k then l ⟨a, h⟩ else 0

open Classical in

def loc {m k : ℕ} (q : ℕ) (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ) (l : Fin k → ℤ) : ℂ :=
  if Antitone l ∧ ∀ i, 0 ≤ l i then evalAt α (schur (pad m l)) * conj (evalAt β (schur l)) * (q : ℂ) ^ (-s * ((∑ i, l i : ℤ) : ℂ))
  else 0

def CauchyLoc : Prop := ∀ (m k q : ℕ) (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ), k ≤ m → 2 ≤ q →
  (∀ a, ‖(α a : ℂ)‖ ≤ Real.sqrt q) → (∀ b, ‖(β b : ℂ)‖ ≤ Real.sqrt q) → 1 < s.re →
    loc q α β s 0 = 1 ∧ HasSum (loc q α β s) (∏ a, ∏ b, (1 - (α a : ℂ) * conj (β b : ℂ) * (q : ℂ) ^ (-s))⁻¹) ∧
      Summable (fun l => ‖loc q α β s l‖) ∧ ∑' l, ‖loc q α β s l‖ ≤ ((1 - (q : ℝ) ^ (1 - s.re))⁻¹) ^ (m * m)

def CAUCHY : Prop := ∀ (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) (m k : ℕ)
  (α : Off E S → Fin m → ℂˣ) (β : Off E S → Fin k → ℂˣ) (s : ℂ), k ≤ m → (∀ w a, ‖(α w a : ℂ)‖ ≤ Real.sqrt (nq w)) →
  (∀ w b, ‖(β w b : ℂ)‖ ≤ Real.sqrt (nq w)) → 2 < s.re →
    Summable (fun l : Off E S →₀ (Fin k → ℤ) => ‖∏ w ∈ l.support, loc (nq w) (α w) (β w) s (l w)‖) ∧
      HasSum (fun l : Off E S →₀ (Fin k → ℤ) => ∏ w ∈ l.support, loc (nq w) (α w) (β w) s (l w)) (LS S α β s)

def SatOff {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (π : CG E m)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (α : Off E S → Fin m → ℂˣ) : Prop :=
  ∀ w, π.HasSat w.1 (Finset.univ.val.map (α w))

def RSPole : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ) (π : CuspSub E m) (π' : CuspSub E k)
  (u : ℝ), 1 ≤ k → k ≤ m → GlobalTheory.DiscSpec.IsNormalised π → GlobalTheory.DiscSpec.IsNormalised π' →
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 E)), ∀ S, S₀ ⊆ S → ∀ (α : Off E S → Fin m → ℂˣ) (β : Off E S → Fin k → ℂˣ),
      SatOff (CG.mk π) S α → SatOff (CG.mk π') S β → ∃ (Z ZS : ℂ → ℂ) (σ₀ : ℝ),
        DifferentiableOn ℂ Z {s | 0 < s.re} ∧ DifferentiableOn ℂ ZS {s | 0 < s.re} ∧
        (∀ σ : ℝ, 0 < σ → ZS (σ + u * Complex.I) ≠ 0) ∧ (∀ s : ℂ, σ₀ < s.re → Z s = (s - 1) * ZS s * LS S α β s) ∧
        ((⟨m, CG.mk π⟩ : Σ a, CG E a) ≠ ⟨k, CG.mk π'⟩ → Z 1 = 0)

open Classical in

def RSU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ) (π : CG E m) (π' : CG E k),
  1 ≤ m → 1 ≤ k → π.IsUnitary → π'.IsUnitary →
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 E)), ∀ S, S₀ ⊆ S → ∀ (α : Off E S → Fin m → ℂˣ) (β : Off E S → Fin k → ℂˣ),
      SatOff π S α → SatOff π' S β → ∃ (F : ℂ → ℂ) (σ₀ : ℝ), (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ) ∧
        ∀ σ : ℝ, σ₀ < σ → F σ = (if (⟨m, π⟩ : Σ a, CG E a) = ⟨k, π'⟩ then (σ : ℂ) - 1 else 1) * LS S α β σ

def NormEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ∃ ν : ℝ → HChar E,
  (∀ τ w, (ν τ).UnrAt w ∧ (((ν τ).val w : ℂˣ) : ℂ) = (Ideal.absNorm w.asIdeal : ℂ) ^ (-((τ : ℂ) * Complex.I))) ∧
  ∀ (m : ℕ) (π : CG E m), 1 ≤ m → π.IsUnitary → ∃ (π₀ : CuspSub E m) (τ : ℝ), GlobalTheory.DiscSpec.IsNormalised π₀ ∧
    π = (CG.mk π₀).twist (ν τ)

def UnitEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ∃ ν : ℝ → HChar E,
  (∀ t, (ν t).IsAbsPow t) ∧ ∀ (m : ℕ) (π : CG E m), 1 ≤ m → ∃ (π₀ : CG E m) (t : ℝ), π₀.IsUnitary ∧ π = π₀.twist (ν t)

def SatTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CG E m) (χ : HChar E)
  (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), χ.UnrAt w → π.HasSat w B → (π.twist χ).HasSat w (B.map (· * χ.val w))

def DetOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CG E m)
  (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.IsUnitary → π.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1

def PrimeOff : Prop := ∀ (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))), Primes (nq (S := S))

end PositivityTheory.RgJS
