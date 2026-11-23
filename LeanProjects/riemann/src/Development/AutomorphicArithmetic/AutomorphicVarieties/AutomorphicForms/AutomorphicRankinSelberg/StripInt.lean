import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

noncomputable section

open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate ENNReal

namespace UpperTheory.V.Af.Rs

def strip : Set ℍ := {z | 0 ≤ z.re ∧ z.re < 1}

def pt (x y : ℝ) : ℍ := ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)

abbrev Cop : Type := {x : Fin 2 → ℤ // IsCoprime (x 0) (x 1)}

def cls (L : ℕ) (x : Fin 2 → ℤ) : Fin 2 → ZMod L := fun i => (x i : ZMod L)

def row (γ : SL(2, ℤ)) : Fin 2 → ℤ := fun i => γ.1 1 i

def Nice (F : ℍ → ℂ) : Prop :=
  Continuous F ∧ ∃ C : ℝ, ∀ (γ : SL(2, ℤ)) (z : ℍ), 1 / 2 ≤ z.im → ‖F (γ • z)‖ * z.im ^ 3 ≤ C

def NiceG {L : ℕ} (G : (Fin 2 → ZMod L) → ℍ → ℂ) : Prop :=
  (∀ v, Continuous (G v)) ∧ ∃ C : ℝ, ∀ v (z : ℍ), 1 / 2 ≤ z.im → ‖G v z‖ * z.im ^ 3 ≤ C

def stripI (F : ℍ → ℂ) (s : ℝ) : ℂ := ∫ z in strip, F z * ((z.im ^ s : ℝ) : ℂ)

def ker (s : ℝ) (x : Fin 2 → ℤ) (z : ℍ) : ℝ := (z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ))) ^ s

def Zc (L : ℕ) (v : Fin 2 → ZMod L) (s : ℝ) (z : ℍ) : ℝ := ∑' x : Fin 2 → ℤ, if cls L x = v then ker s x z else 0

def Wsum (s : ℝ) : ℝ := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * s))

def Lps {L : ℕ} (ψ : DirichletCharacter ℂ L) (s : ℝ) : ℂ := ∑' n : ℕ, ψ (n : ZMod L) / (((n : ℝ) ^ (2 * s) : ℝ) : ℂ)

def TT (L : ℕ) [NeZero L] (G : (Fin 2 → ZMod L) → ℍ → ℂ) (s : ℝ) : ℂ :=
  ∫ z in ModularGroup.fd, ∑ v, G v z * (Zc L v s z : ℂ)

def IsCls {L : ℕ} (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ) (G : (Fin 2 → ZMod L) → ℍ → ℂ) : Prop :=
  ∀ (n : ℕ) (γ : SL(2, ℤ)) (z : ℍ), G (cls L ((n : ℤ) • row γ)) z = ψ (n : ZMod L) * F (γ • z)

example : IsCls (1 : DirichletCharacter ℂ 1) 1 1 := fun _ _ _ => by
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]; simp

example : Nice 0 := ⟨continuous_const, 0, fun _ _ _ => by simp⟩

def gam (t : ℝ) : ℝ := Real.Gamma t / (4 * Real.pi) ^ t

def VolMap : Prop :=
  Measurable (fun p : ℝ × ℝ => pt p.1 p.2) ∧ (volume : Measure ℍ) = Measure.map (fun p : ℝ × ℝ => pt p.1 p.2)
    (((volume : Measure ℝ).prod (volume.restrict (Ioi 0))).withDensity fun p => ENNReal.ofReal (1 / p.2 ^ 2))

def StripFub : Prop :=
  ∀ H : ℍ → ℂ, IntegrableOn H strip →
    IntegrableOn (fun y : ℝ => (∫ x in (0 : ℝ)..1, H (pt x y)) / ((y ^ 2 : ℝ) : ℂ)) (Ioi 0) ∧
    ∫ z in strip, H z = ∫ y in Ioi (0 : ℝ), (∫ x in (0 : ℝ)..1, H (pt x y)) / ((y ^ 2 : ℝ) : ℂ)

def StripIm : Prop :=
  ∀ φ : ℝ → ℝ, Measurable φ → IntegrableOn (fun y => φ y / y ^ 2) (Ioi 0) → IntegrableOn (fun z : ℍ => φ z.im) strip

def FdFin : Prop := MeasurableSet ModularGroup.fd ∧ volume ModularGroup.fd < ∞

def FdNull : Prop := volume (ModularGroup.fd \ ModularGroup.fdo) = 0

def FdPos : Prop :=
  ∀ φ : ℍ → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) → IntegrableOn φ ModularGroup.fd → ∀ z ∈ ModularGroup.fd, 0 < φ z → 0 < ∫ z in ModularGroup.fd, φ z

def StripInt : Prop :=
  ∀ F : ℍ → ℂ, Nice F → ∀ s ∈ Ioc (1 : ℝ) 2, IntegrableOn (fun z : ℍ => F z * ((z.im ^ s : ℝ) : ℂ)) strip

def FdCount : Prop :=
  ∀ᵐ z : ℍ, ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z) = 2

def UnfM : Prop :=
  Measure.sum (fun γ : SL(2, ℤ) => Measure.map (fun z : ℍ => γ • z) (volume.restrict ModularGroup.fd)) = (2 : ℝ≥0∞) • (volume : Measure ℍ)

def RowBij : Prop :=
  (∀ γ : SL(2, ℤ), IsCoprime (row γ 0) (row γ 1)) ∧
    ∀ (z : ℍ) (x : Cop), ∃! γ : SL(2, ℤ), row γ = x.1 ∧ γ • z ∈ strip

def RowRep : Prop := ∀ x : Fin 2 → ℤ, ∃ (n : ℕ) (γ : SL(2, ℤ)), x = (n : ℤ) • row γ

def Unfold : Prop :=
  ∀ (H : ℍ → ℂ) (Φ : (Fin 2 → ℤ) → ℍ → ℂ), Continuous H → IntegrableOn H strip → (∀ γ z, H (γ • z) = Φ (row γ) z) →
    (∀ x : Cop, IntegrableOn (Φ x.1) ModularGroup.fd) →
    HasSum (fun x : Cop => ∫ z in ModularGroup.fd, Φ x.1 z) (2 * ∫ z in strip, H z)

def GcdSum : Prop :=
  ∀ (u : (Fin 2 → ℤ) → ℂ) (c : ℕ → ℂ), Summable u → Summable c → u 0 = 0 → c 0 = 0 →
    (∀ (n : ℕ) (x : Cop), u ((n : ℤ) • x.1) = c n * u x.1) → ∑' x, u x = (∑' n, c n) * ∑' x : Cop, u x.1

def KerBd : Prop :=
  ∀ s ∈ Icc (1 : ℝ) 2, (∀ x, Continuous (ker s x)) ∧ (∀ x z, 0 ≤ ker s x z) ∧ (∀ z, ker s 0 z = 0) ∧
    (∀ (γ : SL(2, ℤ)) (z : ℍ), ker s (row γ) z = (γ • z).im ^ s) ∧
    (∀ (n : ℕ) x z, ker s ((n : ℤ) • x) z = ker s x z / (n : ℝ) ^ (2 * s)) ∧
    ∀ x, ∀ z ∈ ModularGroup.fd, ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s))

def KerLow : Prop :=
  ∀ s ∈ Icc (1 : ℝ) 2, ∀ x, ∀ z ∈ ModularGroup.fd, 1 / 2 / (‖(z : ℂ)‖ + 1) ^ 4 * ‖x‖ ^ (-(2 * s)) ≤ ker s x z

def KerDiff : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (1 : ℝ) 2, ∀ x x' : Fin 2 → ℤ, x ≠ 0 → x' ≠ 0 → ∀ z ∈ ModularGroup.fd,
    |ker s x z - ker s x' z| ≤ C * ‖x - x'‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ))

def WTop : Prop :=
  (∀ t : ℝ, 2 < t → Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-t)) ∧ ∀ M : ℝ, ∃ s ∈ Ioc (1 : ℝ) 2, M ≤ Wsum s

def ZDiff : Prop :=
  ∀ (L : ℕ) [NeZero L], ∃ C : ℝ, ∀ v v', ∀ s ∈ Ioc (1 : ℝ) 2, ∀ z ∈ ModularGroup.fd, |Zc L v s z - Zc L v' s z| ≤ C * z.im ^ 3

def ZLow : Prop :=
  ∀ (L : ℕ) [NeZero L], ∀ s ∈ Ioc (1 : ℝ) 2, ∀ z ∈ ModularGroup.fd, 1 / 2 / (‖(z : ℂ)‖ + 1) ^ 4 * Wsum s ≤ ∑ v, Zc L v s z

def ZInt : Prop :=
  ∀ (L : ℕ) [NeZero L] (G : (Fin 2 → ZMod L) → ℍ → ℂ), NiceG G → ∀ s ∈ Ioc (1 : ℝ) 2, ∀ v v',
    IntegrableOn (fun z => G v z * (Zc L v' s z : ℂ)) ModularGroup.fd

def Swap : Prop :=
  ∀ (L : ℕ) [NeZero L] (G : (Fin 2 → ZMod L) → ℍ → ℂ), NiceG G → ∀ s ∈ Ioc (1 : ℝ) 2,
    (∀ x, IntegrableOn (fun z => G (cls L x) z * (ker s x z : ℂ)) ModularGroup.fd) ∧
    HasSum (fun x : Fin 2 → ℤ => ∫ z in ModularGroup.fd, G (cls L x) z * (ker s x z : ℂ)) (TT L G s)

def TBdd : Prop :=
  ∀ (L : ℕ) [NeZero L] (G : (Fin 2 → ZMod L) → ℍ → ℂ), NiceG G → (∀ z, ∑ v, G v z = 0) → ∃ C : ℝ, ∀ s ∈ Ioc (1 : ℝ) 2, ‖TT L G s‖ ≤ C

def TTop : Prop :=
  ∀ (L : ℕ) [NeZero L] (G : (Fin 2 → ZMod L) → ℍ → ℂ), NiceG G → (∀ v z, 0 ≤ (G v z).re) → (∃ v, ∃ z ∈ ModularGroup.fd, 0 < (G v z).re) →
    ∀ M : ℝ, ∃ s ∈ Ioc (1 : ℝ) 2, M ≤ (TT L G s).re

def ClsEx : Prop :=
  ∀ (L : ℕ) [NeZero L] (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ),
    (∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ z, F (γ • z) = ψ ((γ 1 1 : ℤ) : ZMod L) * F z) → ∃ G, IsCls ψ F G

def ClsProp : Prop :=
  ∀ (L : ℕ) [NeZero L] (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ) (G : (Fin 2 → ZMod L) → ℍ → ℂ), IsCls ψ F G →
    (Nice F → NiceG G) ∧ (ψ ≠ 1 → ∀ z, ∑ v, G v z = 0) ∧
    (ψ = 1 → (∀ z, 0 ≤ (F z).re) → (∃ z, 0 < (F z).re) → (∀ v z, 0 ≤ (G v z).re) ∧ ∃ v, ∃ z ∈ ModularGroup.fd, 0 < (G v z).re)

def TEq : Prop :=
  ∀ (L : ℕ) [NeZero L] (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ) (G : (Fin 2 → ZMod L) → ℍ → ℂ), IsCls ψ F G → Nice F → NiceG G →
    ∀ s ∈ Ioc (1 : ℝ) 2, TT L G s = Lps ψ s * (2 * stripI F s)

def LBd : Prop :=
  ∀ (L : ℕ) [NeZero L] (ψ : DirichletCharacter ℂ L) (s : ℝ), 1 ≤ s →
    Summable (fun n : ℕ => ψ (n : ZMod L) / (((n : ℝ) ^ (2 * s) : ℝ) : ℂ)) ∧ 1 / 4 ≤ ‖Lps ψ s‖ ∧ ‖Lps ψ s‖ ≤ 2

def NicePet : Prop :=
  ∀ (k L : ℕ) [NeZero L] (f g : CuspForm (Gamma1 L) (k : ℤ)), Nice (petersson k g f)

def PetChar : Prop :=
  ∀ (k L : ℕ) [NeZero L] (χ ψ : DirichletCharacter ℂ L) (f g : ℍ → ℂ), HasChar k χ f → HasChar k ψ g →
    ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ z, petersson k g f (γ • z) = (χ * ψ⁻¹) ((γ 1 1 : ℤ) : ZMod L) * petersson k g f z

def Pars : Prop :=
  ∀ (k L : ℕ) [NeZero L] (f g : CuspForm (Gamma1 L) (k : ℤ)) (y : ℝ), 0 < y →
    HasSum (fun n : ℕ => conj (coef g n) * coef f n * (Real.exp (-(4 * Real.pi * n) * y) : ℂ)) (∫ x in (0 : ℝ)..1, conj (g (pt x y)) * f (pt x y))

def MelSum : Prop :=
  ∀ (c : ℕ → ℝ) (P : ℝ → ℝ) (t : ℝ), 0 < t → (∀ n, 0 ≤ c n) → (∀ y, 0 < y → HasSum (fun n : ℕ => c n * Real.exp (-(4 * Real.pi * n) * y)) (P y)) →
    IntegrableOn (fun y => P y * y ^ (t - 1)) (Ioi 0) → Summable fun n : ℕ => c n / (n : ℝ) ^ t

def RankSum : Prop :=
  ∀ (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)), ∀ s ∈ Ioc (1 : ℝ) 2,
    Summable fun n : ℕ => ‖coef f n‖ ^ 2 / (n : ℝ) ^ (k + s - 1)

def Rankin : Prop :=
  ∀ (k L : ℕ) [NeZero L] (f g : CuspForm (Gamma1 L) (k : ℤ)), ∀ s ∈ Ioc (1 : ℝ) 2,
    stripI (petersson k g f) s = (gam (k + s - 1) : ℂ) * ∑' n : ℕ, conj (coef g n) * coef f n / (((n : ℝ) ^ (k + s - 1) : ℝ) : ℂ)

def Rec (e a : ℕ → ℂ) : Prop :=
  a 1 = 1 ∧ ∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n → a (p * n) + e p * (if p ∣ n then a (n / p) else 0) = a p * a n

def ArFact : Prop :=
  ∀ (r : ℕ) (e e' a b : ℕ → ℂ), Rec e a → Rec e' b → (∀ p : ℕ, p.Prime → b p = a p) → (∀ p : ℕ, p.Prime → e p ≠ e' p → a p = 0) →
    (∀ p : ℕ, p.Prime → ‖e p‖ ≤ (p : ℝ) ^ r ∧ ‖e' p‖ ≤ (p : ℝ) ^ r) →
    ∃ P : Set ℕ, (∀ n ∈ P, b n = a n) ∧ ∀ n, 1 ≤ n → a n ≠ 0 → ∃ n₁ ∈ P, ∃ m : ℕ, n = n₁ * m ^ 2 ∧
      ‖a n‖ ≤ ‖a n₁‖ * (m : ℝ) ^ r ∧ ‖b n‖ ≤ ‖a n₁‖ * (m : ℝ) ^ r

def ArSum : Prop :=
  ∀ (r : ℕ) (t : ℝ) (a b : ℕ → ℂ) (P : Set ℕ), (r : ℝ) + 1 ≤ t → (∀ n ∈ P, b n = a n) →
    (∀ n, 1 ≤ n → a n ≠ 0 → ∃ n₁ ∈ P, ∃ m : ℕ, n = n₁ * m ^ 2 ∧ ‖a n‖ ≤ ‖a n₁‖ * (m : ℝ) ^ r ∧ ‖b n‖ ≤ ‖a n₁‖ * (m : ℝ) ^ r) →
    (Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ t) →
    ∑' n : ℕ, ‖a n‖ ^ 2 / (n : ℝ) ^ t ≤ 7 * (∑' n : ℕ, conj (b n) * a n / (((n : ℝ) ^ t : ℝ) : ℂ)).re

def Cmp : Prop :=
  ∀ (k L : ℕ) [NeZero L], 1 ≤ k → ∀ (χ ψ : DirichletCharacter ℂ L) (g : Eigenform k L χ) (h : Eigenform k L ψ),
    (∀ p : ℕ, p.Prime → h.a p = g.a p) → (∀ p : ℕ, p.Prime → χ (p : ZMod L) ≠ ψ (p : ZMod L) → g.a p = 0) →
    ∀ s ∈ Ioc (1 : ℝ) 2, ‖stripI (petersson k g.f g.f) s‖ ≤ 7 * ‖stripI (petersson k h.f g.f) s‖

def Core : Prop :=
  ∀ (k L : ℕ) [NeZero L], 1 ≤ k → ∀ (χ ψ : DirichletCharacter ℂ L) (g : Eigenform k L χ) (h : Eigenform k L ψ),
    (∀ p : ℕ, p.Prime → h.a p = g.a p) → (∀ p : ℕ, p.Prime → χ (p : ZMod L) ≠ ψ (p : ZMod L) → g.a p = 0) → χ = ψ

def Deplete : Prop :=
  ∀ (k N L : ℕ) [NeZero N] [NeZero L], 1 ≤ k → N ∣ L → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ),
    ∃ (χ' : DirichletCharacter ℂ (L * L)) (g' : Eigenform k (L * L) χ'), ∀ p : ℕ, p.Prime →
      (¬ p ∣ L → χ' (p : ZMod (L * L)) = χ (p : ZMod N) ∧ g'.a p = g.a p) ∧ (p ∣ L → g'.a p = 0)

def CharEq2 : Prop :=
  ∀ (k N M : ℕ) [NeZero N] [NeZero M], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (g : Eigenform k N χ)
    (h : Eigenform k M ψ), (∀ᶠ p : ℕ in Filter.cofinite, p.Prime →
      h.a p = g.a p ∧ conj (g.a p) * χ (p : ZMod N) = g.a p ∧ conj (h.a p) * ψ (p : ZMod M) = h.a p) →
    ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → χ (p : ZMod N) = ψ (p : ZMod M)

end UpperTheory.V.Af.Rs
