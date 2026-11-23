import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
import GroundTheory.AutomorphicForms.L2LocalComponents

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.V

namespace UpperTheory.ConvolutionTheory.Dp

section General

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def clsL : cuspForms K n →ₗ[ℂ] LL μ := (toLp μ).toLinearMap ∘ₗ cuspVecL μ

def formsIn (V : Submodule ℂ (LL μ)) : Submodule ℂ (cuspForms K n) := centralCuspForms K n ⊓ V.comap (clsL μ)

def RG (g : AdelicGLn.AdelicGL K n) : LL μ →L[ℂ] LL μ := rightRegularRep (rationalGLOne K n) μ (retractOne g)

def localRepresentationL2 (w : HeightOneSpectrum (𝓞 K)) : Representation ℂ (GL (Fin n) (w.adicCompletion K)) (LL μ) where
  toFun g := (RG μ (finGL K n (locGL K n w g))).toLinearMap
  map_one' := by
    have h : retractOne (1 : AdelicGLn.AdelicGL K n) = 1 := retractOne_coe 1
    simp only [map_one, RG, h, UnitaryRep.map_one]; rfl
  map_mul' g h := by
    simp only [map_mul, RG]
    rw [retractOne_mul, UnitaryRep.map_mul]; rfl

variable {μ} in

def locOn {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) (w : HeightOneSpectrum (𝓞 K)) :
    Representation ℂ (GL (Fin n) (w.adicCompletion K)) V :=
  (⟨V, fun _ _ hv => hV.inv _ _ hv⟩ : Subrepresentation (localRepresentationL2 μ w)).toRepresentation

end General

section Complex

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
  (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

structure Carries (π : CuspSub E n) (V : Submodule ℂ (LL μ)) : Prop where
  summand : IsSummand μ V
  carrier_eq : Cm.carrier π = formsIn μ V

end Complex

def SumT : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∃ (_ : CompleteSpace (V.comap (toLp μ).toLinearMap))
      (hV : (cuspRepT μ).IsInvariant (V.comap (toLp μ).toLinearMap)),
      ((cuspRepT μ).restrict (V.comap (toLp μ).toLinearMap) hV).IsIrreducible

def FormsIrr : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → Fb.Stab (formsIn μ V) ∧ formsIn μ V ≠ ⊥ ∧ (∀ W ≤ formsIn μ V, Fb.Stab W → W = ⊥ ∨ W = formsIn μ V) ∧
      ((formsIn μ V).map (clsL μ)).topologicalClosure = V

def ClsBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure],
    (∀ φ ∈ centralCuspForms K n, clsL μ φ = 0 → φ = 0) ∧ (∀ φ, clsL μ φ ∈ cuspidalL2 μ) ∧
    (∀ φ ∈ centralCuspForms K n, ∀ (ψ : cuspForms K n) (g : AdelicGLn.AdelicGL K n), (∀ x, ψ.1 x = φ.1 (x * g)) →
      clsL μ ψ = RG μ g (clsL μ φ)) ∧
    ∀ φ ∈ centralCuspForms K n, (clsL μ φ : RightCosetSpace (rationalGLOne K n) → ℂ) =ᵐ[quotientMeasure (rationalGLOne K n) μ]
      fun y => φ.1 ((Quotient.out y : normOneGL K n) : AdelicGLn.AdelicGL K n)

def FormsClosure : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (U : Submodule ℂ (cuspForms K n)), U ≤ centralCuspForms K n → Fb.Stab U →
    formsIn μ (U.map (clsL μ)).topologicalClosure = U

def ClosureSummand : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (U : Submodule ℂ (cuspForms K n)), U ≤ centralCuspForms K n → Fb.Stab U → U ≠ ⊥ →
    (∀ W ≤ U, Fb.Stab W → W = ⊥ ∨ W = U) → IsSummand μ (U.map (clsL μ)).topologicalClosure

def OrthOrIso : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (U U' : Submodule ℂ (cuspForms K n)), U ≤ centralCuspForms K n → U' ≤ centralCuspForms K n → Fb.Stab U → Fb.Stab U' →
    (∀ W ≤ U, Fb.Stab W → W = ⊥ ∨ W = U) → (∀ W ≤ U', Fb.Stab W → W = ⊥ ∨ W = U') →
    U.map (clsL μ) ⟂ U'.map (clsL μ) ∨ ∃ T : U ≃ₗ[ℂ] U',
      (∀ X (φ ψ : U), ψ.1 = (gkModuleCusp K n).ρ X φ.1 → (T ψ).1 = (gkModuleCusp K n).ρ X (T φ).1) ∧
      (∀ k (φ ψ : U), ψ.1 = (gkModuleCusp K n).σ k φ.1 → (T ψ).1 = (gkModuleCusp K n).σ k (T φ).1) ∧
      ∀ g (φ ψ : U), ψ.1 = finRepCusp K n g φ.1 → (T ψ).1 = finRepCusp K n g (T φ).1

def NormIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : CuspSub E n),
    GlobalTheory.DiscSpec.IsNormalised π ↔ Cm.carrier π ≤ centralCuspForms E n

def ExCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∃! π : CuspSub E n, Carries μ π V

def ExSummand : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)),
    Carries μ π V ↔ Cm.carrier π ≤ centralCuspForms E n ∧ V = ((Cm.carrier π).map (clsL μ)).topologicalClosure

def ExTwist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : CuspSub E n), 1 ≤ n → ∃ χ : Formalism.L2.Host.HChar E,
      (∃ s : ℂ, ∀ x, ((χ.1 x : ℂˣ) : ℂ) = (((GroundTheory.Global.IdeleGroup.ideleModule E x).1 : ℝ) : ℂ) ^ s) ∧
      ∃ V, Carries μ (π.twist χ) V

def IsoEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π π' : CuspSub E n), π.Iso π' ↔ π = π'

def IsoIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π π' : CuspSub E n) (V V' : Submodule ℂ (LL μ)), Carries μ π V → Carries μ π' V' → (π.Iso π' ↔ V = V')

def LocEmb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Carries μ π V), ∃ J : π.V →ₗ[ℂ] V, Function.Injective J ∧ DenseRange J ∧
      (∀ ψ : Cm.carrier π, (J (Cm.carrierEq π ψ)).1 = clsL μ ψ.1) ∧
      ∀ w g φ, J (π.locRep w g φ) = locOn h.summand w g (J φ)

def FixedDense : Prop :=
  ∀ (G H X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G H) (τ : Representation ℂ G X) (J : X →ₗ[ℂ] H) (U : Subgroup G),
    IsCompact (U : Set G) → (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ x, IsOpen {g | τ g x = x}) → (∀ g x, J (τ g x) = ρ g (J x)) →
    DenseRange J → ∀ v, (∀ u ∈ U, ρ u v = v) → v ∈ closure (J '' {x | ∀ u ∈ U, τ u x = x})

def SatIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Carries μ π V) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ),
    (UpperTheory.CBC.Cusp.cx π).sat w B ↔ GlobalTheory.LFun.HasSatGL w (locOn h.summand w) B

def LocFlath : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : CuspSub E n)
    (D : AdelicDecomposition (Cm.toModule π)) (w : HeightOneSpectrum (𝓞 E)) σ,
    (UpperTheory.CBC.Cusp.cx π).locComp w σ ↔ Nonempty (σ.ρ.Equiv (D.finite.π w))

def LocIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Carries μ π V) (w : HeightOneSpectrum (𝓞 E)) σ,
    (UpperTheory.CBC.Cusp.cx π).locComp w σ ↔ ∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = locOn h.summand w g (f x)

end UpperTheory.ConvolutionTheory.Dp
