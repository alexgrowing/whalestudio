import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth

noncomputable section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

namespace UpperTheory.ConvolutionTheory.Ci

section Defs

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def val (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) : PR K n →+* ℂ :=
  eval₂Hom (eval fun o : Option (Ix K n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1)) (hval t)

def chebP (η : ℝ) (m : ℕ) : PR K n :=
  C (Polynomial.aeval (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ) (Polynomial.Chebyshev.T ℂ m))

def Bd (κ : Finset (Pl K)) (D d : ℕ) (R : PR K n) : Prop :=
  (∀ x ∈ R.vars, x.1 ∈ κ) ∧ R.totalDegree ≤ D ∧ ∀ β, (R.coeff β).totalDegree ≤ d

end Defs

def ExpForm : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (l : ℕ), 0 < l → ∀ (U : ZMod l → Module.End ℂ W)
    (B : Module.End ℂ W), (∀ i k, Commute (U i) (U k)) → (∀ i, B * U i = U (i + 1) * B) →
    ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ j ≥ Module.finrank ℂ W, LinearMap.trace ℂ W (U 0 ^ j * B) = ∑ ζ ∈ s, c ζ * ζ ^ j

def TrExp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n l : ℕ), 0 < l → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (θ : Twist μ)
    (𝔰 : Side θ l) (V : Submodule ℂ (LL μ)) (x : ℝ), 0 ≤ 𝔰.toAmp.A → IsSummand μ V → FiniteDimensional ℂ (eigIn V 𝔰.toAmp.A x) →
    ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop,
      trOn (eigIn V 𝔰.toAmp.A x) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U) = ∑ ζ ∈ s, c ζ * ζ ^ j

def EvVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ) (V : Submodule ℂ (LL μ)) (x : ℝ), 0 < x → IsSummand μ V →
      (eigIn V 𝔞.A x ≠ ⊥ → ∃ Λ t, At μ 𝔞.S V Λ t) ∧
      (∀ Λ t Λ' t', At μ 𝔞.S V Λ t → At μ 𝔞.S V Λ' t' → Λ = Λ' ∧ ∀ w ∉ 𝔞.S, t w = t' w) ∧
      ∀ ev, 𝔞.IsEv ev → ∀ Λ t, At μ 𝔞.S V Λ t → ∀ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ 𝔞.S) →
        ∀ v ∈ eigIn V 𝔞.A x, ev P v = val x Λ t P • v

def ValBc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (x : ℝ)
    (Λ : (F →+* ℂ) → Multiset ℂ) (t : Pl F → Multiset ℂ) (P : PR E n), (∀ y ∈ P.vars, (t (y.1.under (𝓞 F))).card = n) →
    val x Λ t (bcPR F P) = val x (bcInf Λ) (bcSat t) P ∧
      (∀ y ∈ (bcPR F P).vars, ∃ y' ∈ P.vars, y.1 = y'.1.under (𝓞 F)) ∧ ∀ η m, bcPR F (chebP η m : PR E n) = chebP η m

def KillEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (n : ℕ) (SE : Set (Pl E)) (SF : Set (Pl F)), (∀ w : Pl E, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) →
    ∀ (B B' : Type) [Fintype B] [Fintype B'] (b : B → Datum E n) (b' : B' → Datum F n),
      (∀ i, ∃ Λ t, (b i).Pt SE Λ t) → (∀ i, ∃ Λ t, (b' i).Pt SF Λ t) →
    ∀ (L : Ix E n → ℂ) (t : Pl E → Multiset ℂ), (∀ w ∉ SE, (t w).card = n) → OffFam F n SE SF (msOf L) t →
    ∃ Φ : KF (Ix E n) (Pl E × Fin n), admitted SE Φ ∧ evK L (hval t) Φ ≠ 0 ∧ (∀ i, Kills SE Φ (b i)) ∧
      ∀ i (L' : Ix F n → ℂ) t', (b' i).Pt SF (msOf L') t' →
        evK (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (hval (bcSat t')) Φ = 0

def KfBc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (SE : Set (Pl E)) (SF : Set (Pl F)),
    (∀ w : Pl E, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) → ∀ (Φ : KF (Ix E n) (Pl E × Fin n)) G, admitted SE Φ → IsGen Φ G →
    ∃ (Φ' : KF (Ix F n) (Pl F × Fin n)) (G' : ℕ → MvPolynomial (Pl F × Fin n) (MvPolynomial (Ix F n) ℂ)),
      admitted SF Φ' ∧ IsGen Φ' G' ∧ (∀ d, trunc d G' = bcPR F (trunc d G)) ∧
      ∀ (L' : Ix F n → ℂ) (t' : Pl F → Multiset ℂ), (∀ v ∉ SF, (t' v).card = n) →
        evK L' (hval t') Φ' = evK (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (hval (bcSat t')) Φ

def TruncSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (Pl K)) (Φ : KF (Ix K n) (Pl K × Fin n)), admitted S Φ →
    (∃ G, IsGen Φ G) ∧ ∀ G, IsGen Φ G →
      (∃ (κ : Finset (Pl K)) (D : ℕ), (∀ w ∈ κ, w ∉ S) ∧ ∀ d, Bd κ D d (trunc d G)) ∧
      (∀ (L : Ix K n → ℂ) (t : Pl K → Multiset ℂ), ∃ u : ℕ → ℂ, Tendsto u atTop (𝓝 (evK L (hval t) Φ)) ∧
        ∀ (x : ℝ) (d : ℕ), val x (msOf L) t (trunc d G) = (x : ℂ) ^ d * u d) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ev : PR K n →+* (H →L[ℂ] H)),
        (∀ c : ℂ, ev (C (C c)) = c • 1) → ∃ M : ℝ, ∀ d, ‖ev (trunc d G)‖ ≤ M ^ (d + 1)

def SepPoly : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (Pl K)) (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ)
    (I : Type) [Fintype I] (Λ' : I → (K →+* ℂ) → Multiset ℂ) (t' : I → Pl K → Multiset ℂ),
    (∀ τ, (Λ τ).card = n) → (∀ w ∉ S, (t w).card = n) → (∀ i τ, (Λ' i τ).card = n) → (∀ i, ∀ w ∉ S, (t' i w).card = n) →
    (∀ i, ¬ (Λ = Λ' i ∧ ∀ w ∉ S, t w = t' i w)) →
    ∃ (P : PR K n) (κ : Finset (Pl K)) (D : ℕ), (∀ w ∈ κ, w ∉ S) ∧ Bd κ D D P ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧
      ∀ i (x : ℝ), val x (Λ' i) (t' i) P = 0

def OneSide : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n l : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (ev : PR K n →+* (LL μ →L[ℂ] LL μ)),
      𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → ∃ N : ℕ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ≥ η, χ x = 1) →
      ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ p, p ∈ s ↔ η < p.1 ∧ IsSummand μ p.2 ∧ p.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = p.2 ∧ eigIn p.2 𝔰.toAmp.A p.1 ≠ ⊥) ∧
        (∀ p ∈ s, FiniteDimensional ℂ (eigIn p.2 𝔰.toAmp.A p.1)) ∧
        ∀ N' : ℕ, ∃ C₁ : ℝ, ∀ (Q : PR K n) (a : ℝ × Submodule ℂ (LL μ) → ℂ),
          (∀ p ∈ s, ∀ v ∈ eigIn p.2 𝔰.toAmp.A p.1, ev Q v = a p • v) →
          ∀ (m j : ℕ) (Z : ℝ) (f : TG K n), 1 ≤ Z → 𝔰.Rep (ev (chebP η m * Q)) j Z f →
            ‖twInt θ f - ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p *
                trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U))‖ ≤
              C₁ * ‖𝔰.Uq 0‖ ^ j * (Z ^ N * (‖ev Q‖ + (4 / η) ^ m * ‖ev Q ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)‖) +
                (4 / η) ^ m * (Z ^ N')⁻¹ * ‖ev Q‖)

end UpperTheory.ConvolutionTheory.Ci
