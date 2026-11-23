import Mathlib
import Formalism.PeriodIntegrals.StrongApproxE

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

def IntSpan : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ (n : ℕ) (b : Fin n → E), (∀ i, IsIntegral ℤ (b i)) ∧ ∀ e : E, ∃ c : Fin n → F, e = ∑ i, c i • b i

def DedSA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (a c : HeightOneSpectrum (𝓞 F) → F),
    (∀ p ∈ T, c p ≠ 0) →
    ∃ t : F, (∀ p ∈ T, p.valuation F (t - a p) ≤ p.valuation F (c p)) ∧ ∀ p, p ∉ T → p.valuation F t ≤ 1

def LocSmall : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (V : AddSubgroup L.Fp), IsOpen (V : Set L.Fp) →
    ∃ c : F, c ≠ 0 ∧ ∀ z : F, p.valuation F z ≤ p.valuation F c → L.ιF z ∈ V

def LocDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (V : AddSubgroup L.Fp), IsOpen (V : Set L.Fp) →
    ∀ α : L.Fp, ∃ a : F, L.ιF a - α ∈ V

def LocInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (z : F) (e : E), p.valuation F z ≤ 1 → IsIntegral ℤ e →
    L.ιF z • L.ιE e ∈ L.O

def LocOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (U : AddSubgroup L.Ep), IsOpen (U : Set L.Ep) →
    ∀ (n : ℕ) (w : Fin n → L.Ep), ∃ V : AddSubgroup L.Fp, IsOpen (V : Set L.Fp) ∧ ∀ α ∈ V, ∀ i, α • w i ∈ U

def LocSpan : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (n : ℕ) (b : Fin n → E),
    (∀ e : E, ∃ c : Fin n → F, e = ∑ i, c i • b i) → ∀ x : L.Ep, ∃ α : Fin n → L.Fp, x = ∑ i, α i • L.ιE (b i)

def LocLin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (a : F) (e : E), L.ιE (a • e) = L.ιF a • L.ιE e

end PI.StrongApproxE
