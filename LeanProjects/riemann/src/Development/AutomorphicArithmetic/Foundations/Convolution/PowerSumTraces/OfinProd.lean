import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.GM
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def sphOff (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (P : Finset (Pl K)) : Submodule ℂ (LL μ) :=
  ⨅ v ∉ P, fixL μ v (GLnLocal.integralGL (v.adicCompletion K) n)

def levOn (P : Finset (Pl K)) (U : ∀ v : Pl K, Subgroup (Gw n v)) : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
  levF fun v => if v ∈ P then U v else GLnLocal.integralGL (v.adicCompletion K) n

def FixLev : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), fixF μ (levOn P U) = sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v)

def OfinProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (mf : Measure (AdelicGLn.FiniteAdelicGL K n)) [mf.IsHaarMeasure], mf (AdelicGLn.integralFiniteGL K n) = 1 →
    ∀ (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
      (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ) (e : TF K n),
      Function.Injective w → (∀ i, (m i).IsHaarMeasure ∧ m i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
      (∀ i, Test (φ i)) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ x, e x = if ∀ v ∉ Finset.univ.image w, finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n then
        ∏ i, φ i (finAt (w i) (finEmb K n x)) else 0) →
      Ofin μ mf e = (List.ofFn T).prod ∘L prj (sphOff μ (Finset.univ.image w))

def EigAdm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n) (x : ℝ), x ≠ 0 → ∀ (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), (∀ v ∈ P, CO (U v)) →
    FiniteDimensional ℂ ↥(eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v))

def TermF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] (σ : E ≃ₐ[F] E)
    (n l : ℕ), 0 < n → ∀ (μ : Measure (normOneGL F n)) [μ.IsHaarMeasure] (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    [∀ v : Pl F, MeasurableSpace (Gw n v)] [∀ v : Pl F, BorelSpace (Gw n v)] (m : ∀ v : Pl F, Measure (Gw n v)),
    (∀ v, (m v).IsHaarMeasure ∧ m v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (a : TI F n) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (V : Submodule ℂ (LL μ))
      (τ : ∀ v : Pl F, SmIrr (Gw n v)) (x : ℝ), IsSummand μ V → 0 < x → (∀ v ∈ insert q S, Occurs μ V v (τ v)) →
      ∃ N : ℕ, (0 < N ↔ eigIn V (Oinf μ ν a) x ⊓ sphOff μ (insert q S) ≠ ⊥) ∧
        ∀ (L : Loc σ n q w₀) (e : Fin n → ℤ) (𝔣 : Side (Twist.id μ) l), L.S = S → Antitone e → IsSideF L ν a e 𝔣 →
        ∀ (j : ℕ) (sq : ℂ) (s : Pl F → ℂ), HasTrace (m q) (τ q).ρ ((iwCoset q (j • e)).indicator 1) sq →
          (∀ v ∈ S, HasTrace (m v) (τ v).ρ (L.f v) (s v)) →
          trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) = κ * x * N * sq * ∏ v ∈ S, s v

end UpperTheory.ConvolutionTheory.C
