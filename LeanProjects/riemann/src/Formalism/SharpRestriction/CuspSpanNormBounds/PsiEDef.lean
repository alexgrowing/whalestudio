import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

noncomputable section

open ValuativeRel IsDedekindDomain NumberField

namespace Formalism.MainNotions.S.Loc

def resChar {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) : ℕ :=
  ringChar (𝓞 F ⧸ p.asIdeal)

structure SplitAt (Fp Ep : Type) [Field Fp] [ValuativeRel Fp] [CommRing Ep] [Algebra Fp Ep]
    (cj : Ep ≃ₐ[Fp] Ep) (ell : ℕ) where
  e : Ep ≃ₐ[Fp] Fp × Fp
  e_cj : ∀ x, e (cj x) = (e x).swap
  q : 𝒪[Fp]
  q_irr : Irreducible q
  q_eq : (q : Fp) = (ell : Fp)

structure LocAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) where
  Fp : Type
  [fpF : Field Fp]
  [fpV : ValuativeRel Fp]
  [fpT : TopologicalSpace Fp]
  Ep : Type
  [epR : CommRing Ep]
  [epA : Algebra Fp Ep]
  [epT : TopologicalSpace Ep]
  [epM : MeasurableSpace Ep]

  lf : IsNonarchimedeanLocalField Fp
  char0 : CharZero Fp
  ιF : F →+* Fp
  ιE : E →+* Ep
  compat : ∀ a : F, ιE (algebraMap F E a) = algebraMap Fp Ep (ιF a)

  dense : DenseRange ιF
  val : ∀ x y : F, (ιF x ≤ᵥ ιF y) ↔ p.valuation F x ≤ p.valuation F y

  free : Module.Free Fp Ep
  rank : Module.finrank Fp Ep = 2
  span : Submodule.span Fp (Set.range ιE) = ⊤
  top : IsModuleTopology Fp Ep
  borel : BorelSpace Ep

  cj : Ep ≃ₐ[Fp] Ep
  cj_ιE : ∀ x, cj (ιE x) = ιE (sig x)

  O : Subring Ep
  O_def : ∀ x : Ep, x ∈ O ↔ IsIntegral 𝒪[Fp] x

  ellPrime : Fact (resChar p).Prime
  [qlA : Algebra ℚ_[resChar p] Fp]
  qlCont : Continuous (algebraMap ℚ_[resChar p] Fp)
  qlFin : FiniteDimensional ℚ_[resChar p] Fp

  psiE : AddChar Ep ℂ
  psiE_def : ∀ y : Ep, ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
    ‖(letI := ((algebraMap Fp Ep).comp (algebraMap ℚ_[resChar p] Fp)).toAlgebra;
      Algebra.trace ℚ_[resChar p] Ep y) - (a : ℚ_[resChar p])‖ ≤ 1 ∧
    psiE y = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ))

  split : Option (SplitAt Fp Ep cj (resChar p))

attribute [instance] LocAt.fpF LocAt.fpV LocAt.fpT LocAt.epR LocAt.epA LocAt.epT LocAt.epM LocAt.qlA

end Formalism.MainNotions.S.Loc

end
