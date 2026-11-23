import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.V
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

def RhoLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) g v,
    rhoL μ w g v = localRepresentationL2 μ w g v

def TsphVec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (B : Multiset ℂˣ),
    GlobalTheory.LFun.HasSatGL w (locOn hV w) B ↔ SSat μ V w (B.map fun b : ℂˣ => (b : ℂ))

def SSatUnit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
    (V : Submodule ℂ (LL μ)) (B : Multiset ℂ), SSat μ V w B →
    (∃ B' : Multiset ℂˣ, B = B'.map fun b : ℂˣ => (b : ℂ)) ∧ ∀ B₁, SSat μ V w B₁ → B₁ = B

def SSatIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V → ∀ (w : Pl E) (B : Multiset ℂ),
    SSat μ V w B ↔ ∃ B' : Multiset ℂˣ, B = B'.map (fun b : ℂˣ => (b : ℂ)) ∧ (UpperTheory.CBC.Cusp.cx π).sat w B'

def SSatEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ w : Pl E,
    V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥ → ∃ B, SSat μ V w B

def JGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (τ : E →+* ℂ),
    (∃ j, IsJ (n := n) τ j) ∧ ∀ j, IsJ (n := n) τ j ↔ ∀ a b, j (HarishChandra.e (a, b)) = Cm.genC τ a b

def CapHC : Prop :=
  ∀ (n : ℕ) (u : ℂ), ∃ z : Subalgebra.center ℂ (HarishChandra.U n),
    (z : HarishChandra.U n) = Formalism.REAL.qdet (fun a b => HarishChandra.e (a, b)) (u + ((n : ℂ) - 1) / 2) ∧
      HarishChandra.harishChandraHom z = ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k)

def CapZc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (τ : E →+* ℂ),
    (∀ i : Fin n, zc τ i ∈ Subalgebra.center ℂ (UC E n)) ∧
    ∀ u : ℂ, Cm.capC τ u = u ^ n • (1 : UC E n) + ∑ i : Fin n, u ^ (n - (i + 1)) • zc τ i

def InfZc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : CuspSub E n) (τ : E →+* ℂ) (m : Multiset ℂ),
    (UpperTheory.CBC.Cusp.cx π).inf τ m ↔ m.card = n ∧ ∀ (i : Fin n), ∀ φ ∈ π.V, Cm.uC E n (zc τ i) φ = m.esymm (i + 1) • φ

def LactSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (u : UC K n) (β : TI K n), SmoothT β →
    ∃ h : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ),
      ∀ g, lact u β g = (rUC u ⟨fun g => β g⁻¹, h⟩ : archGroup K n → ℂ) g⁻¹

def LactCen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n), SmoothT β →
    ∀ p ∈ (isExpLieAlgebra K n).centerU, ∀ q ∈ (isExpLieAlgebra K n).centerU, ∀ φ ∈ centralCuspForms K n,
      Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) (clsL μ φ) =
        Oinf μ ν β (clsL μ (uActionCusp K n p φ + Complex.I • uActionCusp K n q φ))

def DiracSep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (v : LL μ), (∀ β : TI K n, SmoothT β → Oinf μ ν β v = 0) → v = 0

def SInfIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (π : CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V → ∀ (τ : E →+* ℂ) (m : Multiset ℂ),
    SInf μ V τ m ↔ (UpperTheory.CBC.Cusp.cx π).inf τ m

def SInfEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ τ : E →+* ℂ, ∃! m, SInf μ V τ m

def AtEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ (S : Set (Pl E)) (U : Subgroup (AdelicGLn.FiniteAdelicGL E n)),
    (∀ w ∉ S, (GLnLocal.integralGL (w.adicCompletion E) n).map (AdelicGLn.localEmbedding w) ≤ U) →
    V ⊓ fixF μ U ≠ ⊥ → ∃ Λ t, At μ S V Λ t

def AtInj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (V V' : Submodule ℂ (LL μ)), IsSummand μ V → IsSummand μ V' → ∀ (S : Set (Pl E)), S.Finite → ∀ t : Pl E → Multiset ℂ,
    (∀ w ∉ S, SSat μ V w (t w)) → (∀ w ∉ S, SSat μ V' w (t w)) → V = V'

end UpperTheory.ConvolutionTheory.Dp
