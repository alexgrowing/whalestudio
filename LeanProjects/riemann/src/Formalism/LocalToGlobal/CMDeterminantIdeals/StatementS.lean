import Formalism.LocalToGlobal.CMDeterminantIdeals.HadamardLoc0
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder

variable {B : Type} {m : B → ℕ}

def SubstEval : Prop :=
  ∀ (R : Type) [CommRing R] (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) R)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R),
    (∀ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R, evalFr (substFr U P) Y = evalFr P (fun b => (U b).transpose * Y b)) ∧
    ((∀ b, IsUnit (U b).det) → substFr U (substFr (fun b => (U b)⁻¹) P) = P) ∧ substFr (fun _ => 1) P = P

def CoeffIntegralLoc : Prop :=
  ∀ (V K' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']
    (B : Type) [Fintype B] (m : B → ℕ) (G : MvPolynomial (FrVar m) K') (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K')
    (c : ∀ b, Fin (m b) → K') (τ : K'),
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) → τ ≠ 0 → (∀ b, (U b).det ≠ 0) →
    (∀ b j k, c b j * U b j k ∈ Set.range (algebraMap V K')) →
    (∀ (W KW : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field KW] [Algebra W KW] [IsFractionRing W KW]
      [Algebra V W] (f : K' →+* KW), IsAdicComplete (maximalIdeal W) W → Finite (ResidueField W) →
      IsLocalHom (algebraMap V W) → (∀ a : V, f (algebraMap V K' a) = algebraMap W KW (algebraMap V W a)) →
      ∀ (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) KW) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) W), (∀ b, IsUnit (X b).det) →
        (∀ b, ((U b).map f).transpose * Y b = (X b).map (algebraMap W KW)) →
        ∃ w : W, evalFr (MvPolynomial.map f G) Y = f τ * algebraMap W KW w) →
    ∀ μ : FrVar m →₀ ℕ, ∃ w : V, MvPolynomial.coeff μ G * ∏ v : FrVar m, c v.1 v.2.2 ^ μ v = τ * algebraMap V K' w

def gramBlock {K : Type} [Field K] [NumberField K] {g : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K)
    (H : Matrix (Fin g) (Fin g) ℂ) (σ : K →+* ℂ) (b : B) : Matrix (Fin (m b)) (Fin (m b)) ℂ :=
  Matrix.of fun j j' => star (ReciprocityTheory.MultiplicativeHeights.embVec σ (U (e ⟨b, j⟩))) ⬝ᵥ (H.mulVec (ReciprocityTheory.MultiplicativeHeights.embVec σ (U (e ⟨b, j'⟩))))

def Step5Loc {K : Type} [Field K] [NumberField K] {g : ℕ} [Fintype B] (e : (Σ b, Fin (m b)) ≃ Fin g) (de abelian₂ : MLine K)
    (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K) (G : MvPolynomial (FrVar m) K) (n : ℕ)
    (p : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ (t cd : K) (cl : Fin g → K), IsLocGen p t de.I ∧ IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧
    p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd ∧
  ∃ (V K' : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K') (_ : Algebra V K')
    (_ : IsFractionRing V K') (f : K →+* K') (Ub : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K'),
    IsAdicComplete (maximalIdeal V) V ∧ Finite (ResidueField V) ∧
    (∀ y : K, f y ∈ Set.range (algebraMap V K') ↔ p.valuation K y ≤ 1) ∧ (∀ b, (Ub b).det ≠ 0) ∧
    (∀ b j k, f (cl (e ⟨b, j⟩)) * Ub b j k ∈ Set.range (algebraMap V K')) ∧
    ∀ (W KW : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field KW] [Algebra W KW] [IsFractionRing W KW]
      [Algebra V W] (fW : K' →+* KW), IsAdicComplete (maximalIdeal W) W → Finite (ResidueField W) →
      IsLocalHom (algebraMap V W) → (∀ a : V, fW (algebraMap V K' a) = algebraMap W KW (algebraMap V W a)) →
      ∀ (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) KW) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) W), (∀ b, IsUnit (X b).det) →
        (∀ b, ((Ub b).map fW).transpose * Y b = (X b).map (algebraMap W KW)) →
        ∃ w : W, evalFr (MvPolynomial.map fW (MvPolynomial.map f G)) Y = fW (f (t ^ n)) * algebraMap W KW w

def Step5Arch {K : Type} [Field K] [NumberField K] {g : ℕ} [DecidableEq B] (e : (Σ b, Fin (m b)) ≃ Fin g) (de abelian₂ : MLine K)
    (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n : ℕ)
    (La S : ℝ) (σ : K →+* ℂ) : Prop :=
  ∃ H : Matrix (Fin g) (Fin g) ℂ, H.PosDef ∧ abelian₂.n σ = Real.sqrt H.det.re ∧
    (∀ j, ReciprocityTheory.MultiplicativeHeights.hq H (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) ∧ IsEquiv a (MvPolynomial.map σ G) ∧
    ∀ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ, (∀ b, (Y b).conjTranspose * gramBlock e U H σ b * Y b = 1) →
      ‖evalFr (MvPolynomial.map σ G) Y‖ * de.n σ ^ n ≤ S

def Step5 : Prop :=
  KeyCore → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement →
  ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ)
    (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K)
    (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ),
    T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) →
    (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) →
    (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) →
    - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) -
        ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤
      (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)

end Formalism.L2.LamCM
