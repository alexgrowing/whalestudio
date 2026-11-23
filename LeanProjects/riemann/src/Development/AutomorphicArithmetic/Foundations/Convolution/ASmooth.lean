import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

noncomputable section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

namespace UpperTheory.ConvolutionTheory

section One

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

def Inner (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (T : LL μ →L[ℂ] LL μ) : Prop :=
  ∀ V : Submodule ℂ (LL μ), IsClosed (V : Set (LL μ)) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V →
    T ∘L prj V = prj V ∘L T

structure Side (θ : Twist μ) (l : ℕ) extends Amp μ where
  a : TG K n
  a_op : Rop μ a = toAmp.A
  a_smooth : IsLeftSmooth a
  g : TG K n
  g_smooth : IsLeftSmooth (CuspidalProjection.ccStar g)
  Uq : ZMod l → LL μ →L[ℂ] LL μ
  Uq_inner : ∀ i, Inner μ (Uq i)
  Uq_comm : ∀ i k, Commute (Uq i) (Uq k)
  Uq_amp : ∀ i, Commute (Uq i) toAmp.A
  Uq_perm : ∀ i, (Rop μ g ∘L θ.U) ∘L Uq i = Uq (i + 1) ∘L (Rop μ g ∘L θ.U)

def Side.tr {θ : Twist μ} {l : ℕ} (𝔰 : Side θ l) (p : Submodule ℂ (LL μ) → Prop) (x : ℝ) (j : ℕ) : ℂ :=
  ∑ᶠ V ∈ {V : Submodule ℂ (LL μ) | IsSummand μ V ∧ V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V ∧ p V},
    trOn (eigIn V 𝔰.toAmp.A x) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)

def Side.Rep {θ : Twist μ} {l : ℕ} (𝔰 : Side θ l) (P : LL μ →L[ℂ] LL μ) (j : ℕ) (Z : ℝ) (f : TG K n) : Prop :=
  Rop μ f = 𝔰.toAmp.A ∘L (P ∘L (𝔰.Uq 0 ^ j)) ∘L Rop μ 𝔰.g ∧ ∀ x, Z < qht x → twK θ f x = 0

end One

def EvEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ),
      0 ≤ 𝔞.A ∧ ‖𝔞.A‖ ≤ 1 ∧ (∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) ∧ ∃ ev, 𝔞.IsEv ev ∧ ∀ P, Inner μ (ev P)

def ParEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V →
      (∀ τ, ∃! m, SInf μ V τ m) ∧
      (∀ w, V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) ≠ ⊥ → ∃! B, SSat μ V w B) ∧
      ∀ w B, SSat μ V w B → 0 ∉ B

def Kill : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ) (η : ℝ), 0 < η →
    ∃ (B : Type) (_ : Fintype B) (b : B → Datum K n), (∀ i, ∃ Λ t, (b i).Pt 𝔞.S Λ t) ∧
      ∀ ev, 𝔞.IsEv ev → ∀ χ : ℝ → ℝ, Continuous χ → (∀ x ≤ η / 2, χ x = 0) → (∀ x, |χ x| ≤ 1) →
      ∀ F G, admitted 𝔞.S F → (∀ i, Kills 𝔞.S F (b i)) → IsGen F G →
        ∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔞.A ∘L (1 - Pc μ)‖ ≤ C ^ (d + 1) / d.factorial

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n l : ℕ}
  {μE : Measure (normOneGL E n)} [μE.IsHaarMeasure] {μF : Measure (normOneGL F n)} [μF.IsHaarMeasure] {θ : Twist μE}

def GeoPair (𝔢 : Side θ l) (𝔣 : Side (Twist.id μF) l) (c : ℂ) : Prop :=
  (∀ w : Pl E, w ∈ 𝔢.S ↔ w.under (𝓞 F) ∈ 𝔣.S) ∧ ∃ (p : ℕ) (C₀ : ℝ), 0 < p ∧
    ∀ (κ : Finset (Pl E)), (∀ w ∈ κ, w ∉ 𝔢.S) → ∀ t₀ : Pl E → Multiset ℂ, (∀ w ∈ κ, (t₀ w).card = n ∧ 0 ∉ t₀ w) →
    ∀ D : ℕ, ∃ γ : MvPolynomial (Pl E × Fin n) ℂ, (∀ x ∈ γ.vars, x.1 ∈ κ) ∧ eval (hval t₀) γ ≠ 0 ∧
      ∀ evE evF, 𝔢.toAmp.IsEv evE → 𝔣.toAmp.IsEv evF → ∀ᶠ j : ℕ in atTop,
        ∀ R : PR E n, (∀ x ∈ R.vars, x.1 ∈ κ) → R.totalDegree ≤ D → (∀ β, (R.coeff β).totalDegree ≤ j / p) →
          ∃ (fE : TG E n) (fF : TG F n), 𝔢.Rep (evE (map C γ * R)) j (Real.exp (C₀ * j)) fE ∧
            𝔣.Rep (evF (bcPR F (map C γ * R))) j (Real.exp (C₀ * j)) fF ∧ twInt θ fE = c * twInt (Twist.id μF) fF

def OffFam (F : Type) [Field F] [NumberField F] [Algebra F E] (n : ℕ) (SE : Set (Pl E)) (SF : Set (Pl F))
    (Λ : (E →+* ℂ) → Multiset ℂ) (t : Pl E → Multiset ℂ) : Prop :=
  (∀ b : Datum E n, ¬ b.Pt SE Λ t) ∧
    ∀ (b : Datum F n) Λ' t', b.Pt SF Λ' t' → ¬ (Λ = bcInf Λ' ∧ ∀ w ∉ SE, t w = bcSat t' w)

end Two

def CI : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (n l : ℕ), 0 < n → 0 < l →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (θ : Twist μE)
      (𝔢 : Side θ l) (𝔣 : Side (Twist.id μF) l) (c : ℂ), GeoPair 𝔢 𝔣 c →
    ∀ (Λ : (E →+* ℂ) → Multiset ℂ) (t : Pl E → Multiset ℂ), (∀ τ, (Λ τ).card = n) → (∀ w ∉ 𝔢.S, (t w).card = n ∧ 0 ∉ t w) →
      OffFam F n 𝔢.S 𝔣.S Λ t → ∀ x : ℝ, 0 < x → ∀ᶠ j : ℕ in atTop,
        𝔢.tr (fun V => At μE 𝔢.S V Λ t) x j =
          c * 𝔣.tr (fun V => ∃ Λ' t', At μF 𝔣.S V Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, t w = bcSat t' w) x j

end UpperTheory.ConvolutionTheory
