import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.NoPiHk

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS
open GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def GSat (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (φ : Sm E n) : Prop :=
  ∀ w, w ∉ S → FixAt w φ ∧ (B w).card = n ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, ∀ g : GL (Fin n) (w.adicCompletion E),
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < j then ϖ else 1) →
    ∀ R, IsHk w g R → ∃ m : ℕ, ((hk w R - satEig (qV E w) n (B w) j • (1 : Module.End ℂ (Sm E n))) ^ m) φ = 0

def sclQ (w : HeightOneSpectrum (𝓞 E)) (u : ℂ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun b : ℂˣ => (b : ℂ) * ((qV E w : ℕ) : ℂ) ^ u

end Defs

def PiZSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (z : ℂ),
  ∃ π' : CuspSub E n, ∀ᶠ w in Filter.cofinite, ∃ B : Multiset ℂˣ, (CG.mk π').HasSat w B ∧
    ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, ∀ g : GL (Fin n) (w.adicCompletion E),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < j then ϖ else 1) →
      ∀ R, IsHk w g R → ∀ v ∈ piZ π z, FixAt w v → hk w R v = satEig (qV E w) n B j • v

def TwistSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ) (σ : CuspSub E m) (u : ℂ),
  ∃ σ' : CuspSub E m, ∀ᶠ w in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk σ).HasSat w B →
    ∃ B' : Multiset ℂˣ, (CG.mk σ').HasSat w B' ∧ B'.map (fun b : ℂˣ => (b : ℂ)) = sclQ w u B

def CuspSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (φ : Sm E n), IsCuspForm φ →
  φ ≠ 0 → ∀ S B, GSat S B φ → ∃ σ : CuspSub E n, ∀ᶠ w in Filter.cofinite, (CG.mk σ).HasSat w (B w)

def CTEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : Sm E n), IsAutForm φ →
  ¬ IsCuspidal φ.1 → ∀ S B, GSat S B φ →
  ∃ (r s : ℕ) (ψ₁ : Sm E r) (ψ₂ : Sm E s) (S₁ : Finset (HeightOneSpectrum (𝓞 E))) (S₂ : Finset (HeightOneSpectrum (𝓞 E)))
    (B₁ B₂ : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (u₁ u₂ : ℂ), r + s = n ∧ 0 < r ∧ 0 < s ∧
    IsAutForm ψ₁ ∧ ψ₁ ≠ 0 ∧ GSat S₁ B₁ ψ₁ ∧ IsAutForm ψ₂ ∧ ψ₂ ≠ 0 ∧ GSat S₂ B₂ ψ₂ ∧
    ∀ᶠ w in Filter.cofinite, (B w).map (fun b : ℂˣ => (b : ℂ)) = sclQ w u₁ (B₁ w) + sclQ w u₂ (B₂ w)

def Supp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (φ : Sm E n), IsAutForm φ →
  φ ≠ 0 → ∀ S B, GSat S B φ →
  ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (σ : ∀ i, CuspSub E (m i)), Nonempty ι ∧ (∀ i, 1 ≤ m i) ∧
    ∀ᶠ w in Filter.cofinite, ∃ Bi : ι → Multiset ℂˣ, (∀ i, (CG.mk (σ i)).HasSat w (Bi i)) ∧ ∑ i, Bi i = B w

end DiscreteGroups.T1.G

end
