import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open Classical in

def sat (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) : Multiset ℂˣ :=
  if h : ∃ B, π.HasSat w B then h.choose else 0

def UnrOutside (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CG E a) : Prop := ∀ w ∉ S, ∃ B, π.HasSat w B

def locL (q : ℕ) (B B' : Multiset ℂˣ) (s : ℂ) : ℂ :=
  ((B ×ˢ B').map fun p : ℂˣ × ℂˣ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-s))⁻¹).prod

def partialL (S : Finset (HeightOneSpectrum (𝓞 E))) {b : ℕ} (π : CG E a) (π' : CG E b) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S}, locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) (sat π' w.1) s

example (χ : HChar E) : partialL ∅ (CG.ofChar χ) (CG.ofChar χ) 2 = partialL ∅ (CG.ofChar χ) (CG.ofChar χ) 2 := rfl

end GlobalTheory.JSW
