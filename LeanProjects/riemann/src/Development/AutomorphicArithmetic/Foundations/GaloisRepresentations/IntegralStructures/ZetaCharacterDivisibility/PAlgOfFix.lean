import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbedding
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

private theorem chi_fixed {E : Type} [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (hfix : ∀ z, cj E z = z → χ.1 z = 1) (τ : E →+* ℂ) (z : ℂ)
    (hs : expU (atEmb τ (starRingEnd ℂ z)) = expU (atEmb τ z)) :
    Complex.exp (expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z) = 1 := by
  rw [← chiInf_expU_atEmb]
  have h1 : cj E (infId E (expU (atEmb τ z))) = infId E (expU (atEmb τ z)) := by
    refine (GlobalTheory.NormExpo.conjAd_infId E _).trans ?_
    rw [GlobalTheory.NormExpo.star_expU_atEmb, hs]
  have h2 : chiInf χ (expU (atEmb τ z)) = 1 := hfix _ h1
  rw [h2]
  rfl

private theorem expU_neg_pi {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    expU (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I))) = expU (atEmb τ ((Real.pi : ℂ) * Complex.I)) := by
  classical
  refine Units.ext (funext fun w => ?_)
  change Complex.exp (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I)) w) =
    Complex.exp (atEmb τ ((Real.pi : ℂ) * Complex.I) w)
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    split_ifs <;> simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  · simp [Pi.single_eq_of_ne hw]

private theorem add_eq_zero_of {p q : ℂ} (h : ∀ t : ℝ, Complex.exp (p * t + q * starRingEnd ℂ (t : ℂ)) = 1) : p + q = 0 := by
  have hf : (fun t : ℝ => Complex.exp ((p + q) * t)) = fun _ => 1 := by
    funext t
    have := h t
    rw [Complex.conj_ofReal] at this
    rw [add_mul]; exact this
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((p + q) * t)) (Complex.exp ((p + q) * ((0 : ℝ) : ℂ)) * ((p + q) * 1)) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (p + q) * (t : ℂ)) ((p + q) * 1) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (p + q)
    exact h0.cexp
  rw [hf] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using this

theorem UpperTheory.Gal.Int.Div.algOfFix_of :
    AlgOfFix := by
  intro E _ _ _ χ hfix
  have key : ∀ τ : E →+* ℂ, ∃ n : ℤ, expo χ τ = n := by
    intro τ
    have hpq : expo χ τ + expo χ (ComplexEmbedding.conjugate τ) = 0 :=
      add_eq_zero_of fun t => chi_fixed χ hfix τ t (by rw [Complex.conj_ofReal])
    have h := chi_fixed χ hfix τ _ (expU_neg_pi τ)
    have hq : expo χ (ComplexEmbedding.conjugate τ) = - expo χ τ := by linear_combination hpq
    rw [hq] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ h2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hn
    linear_combination hn
  choose n hn using key
  exact ⟨n, isAlgPos_of_expo E χ n hn⟩
