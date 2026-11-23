import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

def mirab (R : Type) [CommRing R] : Subgroup (GL (Fin 2) R) where
  carrier := {g | ![0, 1] ᵥ* (g : Matrix (Fin 2) (Fin 2) R) = ![0, 1]}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rw [← Matrix.vecMul_vecMul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

def aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : GL (Fin 2) R where
  val := !![(y : R), x; 0, 1]
  inv := !![((y⁻¹ : Rˣ) : R), -(((y⁻¹ : Rˣ) : R) * x); 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

section Loc

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

def K1 (c : ℕ) : Subgroup (GL (Fin 2) (w.adicCompletion F)) :=
  ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))).map
    (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers F).subtype)

def Uop {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (c : ℕ) :
    Module.End ℂ V := Hi.dc ρ (K1 w c) (K1 w c) (aff (atFin w (unif w)) 0)

def HasU {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (c : ℕ) (lam : ℂ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ v ∈ Hi.fixd ρ (K1 w c) ∧ Uop w ρ c v = lam • v

def IsCondAt (ω : HChar F) (c : ℕ) : Prop :=
  IsLeast {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
    Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} c

def EmbAt {l : ℕ} [Fact l.Prime] (τ : F →+* Qbar l) : Prop := ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖τ (x : F)‖ < 1

def ordI (I : Ideal (𝓞 F)) : ℕ := (Associates.mk w.asIdeal).count (Associates.mk I).factors

end Loc

section Forms

variable {F : Type} [Field F] [NumberField F]

def chiI (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (I : Ideal (𝓞 F)) : ℂ :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 F), (if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0) ^ ordI w I

def GenD (y : Af F) (𝔪 : Ideal (𝓞 F)) : Prop :=
  𝔪 ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 F),
    Valued.v (pLoc F w y) = WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - (ordI w 𝔪 : ℤ))

open Classical in

def coefAt (c : Ideal (𝓞 F) → ℂ) (y : Af F) : ℂ := if h : ∃ 𝔪, GenD y 𝔪 then c h.choose else 0

open Classical in

def coefDiv (c : Ideal (𝓞 F) → ℂ) (𝔮 𝔪 : Ideal (𝓞 F)) : ℂ := if h : ∃ 𝔫, 𝔪 = 𝔮 * 𝔫 then c h.choose else 0

def absF (y : (Af F)ˣ) : ℝ := ∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖pLoc F w (y : Af F)‖

variable [IsTotallyReal F]

def reAt (v : InfinitePlace F) (x : F) : ℝ := (v.embedding x).re

def HasExp (φ : GA F 2 → ℂ) (k : ℕ) (c₀ : (Af F)ˣ → ℂ) (c : Ideal (𝓞 F) → ℂ) : Prop :=
  ∀ (x : TR.Rinf F) (y : (TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ yf : (Af F)ˣ,
    HasSum (fun ξ : {ξ : F // ∀ v, 0 < reAt v ξ} => coefAt c (algebraMap F (Af F) ξ.1 * (yf : Af F)) *
        Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * ((x v : ℂ) + Complex.I * (y.val v : ℂ))))
      (φ (TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0)) / ((((∏ v, y.val v) * absF yf) ^ ((k : ℝ) / 2) : ℝ) : ℂ) - c₀ yf)

variable (F) in

def locSm (w : HeightOneSpectrum (𝓞 F)) : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) (TR.Sm F 2) :=
  (TR.finRep F 2).comp (locGL F 2 w)

structure IsHol (k : ℕ) (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : HChar F) (φ : TR.Sm F 2) : Prop where
  aut : TR.IsAutForm φ
  level : ∀ w, φ ∈ Hi.fixd (locSm F w) (K1 w (c w))
  cent : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g
  wt : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ
  low : ∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)

def hk (k : ℕ) (w : HeightOneSpectrum (𝓞 F)) (c : ℕ) : Module.End ℂ (TR.Sm F 2) :=
  (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) c

def hkCoef (k : ℕ) (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) (a : Ideal (𝓞 F) → ℂ)
    (𝔪 : Ideal (𝓞 F)) : ℂ :=
  a (w.asIdeal * 𝔪) + chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1) * coefDiv a w.asIdeal 𝔪

structure IsEigHol (k : ℕ) (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : HChar F) (φ : TR.Sm F 2)
    (lam : HeightOneSpectrum (𝓞 F) → ℂ) : Prop where
  hol : IsHol k c ω φ
  ne : φ ≠ 0
  eig : ∀ w, hk k w (c w) φ = lam w • φ

variable {Ω : Type} [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]

structure OrdForm (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s : ℤ) (c : HeightOneSpectrum (𝓞 F) → ℕ)
    (m : HeightOneSpectrum (𝓞 F) → Fin 2 → ℤ) (a : HeightOneSpectrum (𝓞 F) → Qbar l) (π : TR.CuspSub F 2)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) : Prop where
  reg : π.IsRegAlg
  pol : ∃ χ : HChar F, π.Polarized χ
  cont : Continuous r
  att : AttR ι r π
  det : Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ s * ξ
  ξ_open : IsOpen (ξ.ker : Set (G F Ω))
  fin : {w | c w ≠ 0}.Finite
  ram : ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A w →
    (Ine (F := F) A ≤ ξ.ker ↔ c w = 0 ∨ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
  sph : ∀ w, c w = 0 → HasFixed (π.locRep w) (K1 w 0)
  away : ∀ w, c w ≠ 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ lam, HasU w (π.locRep w) (c w) lam ∧ ‖ι.symm lam‖ = 1
  above : ∀ w, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 1 ∧ m w 1 + 2 ≤ m w 0 ∧ m w 0 + m w 1 = s ∧ ‖a w‖ = 1 ∧
    (∃ lam, HasU w (π.locRep w) 1 lam ∧ ‖ι.symm lam * (normV w : Qbar l) ^ m w 0 - a w‖ < 1) ∧
    ∀ τ : F →+* Qbar l, EmbAt w τ → π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf (m w))

end Forms

end UpperTheory.V.Sd
