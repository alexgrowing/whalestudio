import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DiagAct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR
open Polynomial
open scoped Classical

namespace UpperTheory.Gal.W2

def SimDiag : Prop :=
  ∀ (g : ℕ) (I : Type) (M : I → Matrix (Fin g) (Fin g) ℂ), (∀ i j, M i * M j = M j * M i) →
    (∀ i, ∃ p : ℂ[X], p.Separable ∧ aeval (M i) p = 0) → ∃ (Sb : Matrix (Fin g) (Fin g) ℂ) (d : I → Fin g → ℂ),
      Sb.det ≠ 0 ∧ ∀ i, M i * Sb = Sb * Matrix.diagonal (d i)

def ExtendEmb : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (φ : 𝓞 F →+* ℂ), ∃ τ : F →+* ℂ, ∀ c : 𝓞 F, φ c = τ (c : F)

def KillsMat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ q : (𝓞 F)[X], Kills a ga q ↔ (q.sum fun i b => ρ (a b) * H ^ i) = 0

def HSep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (H : Matrix (Fin g) (Fin g) ℂ), (∀ c, ρ (a c) * H = H * ρ (a c)) → ∀ χ : F[X], χ.Monic → χ.Separable →
    (∀ q : (𝓞 F)[X], χ ∣ q.map (algebraMap (𝓞 F) F) → (q.sum fun i b => ρ (a b) * H ^ i) = 0) →
    ∃ p : ℂ[X], p.Separable ∧ aeval H p = 0

def DiagExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ χ : F[X], IsMinOf a ga χ → χ.Separable → ∃ Sb ty ev, IsDiag a ρ H Sb ty ev

def TypeCount : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ H : Matrix (Fin g) (Fin g) ℂ, ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ ∧ (evFull ty ev τ).card = n

def TraceLat : Prop :=
  ∀ (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (g : ℕ) (P : L →+ (Fin g → ℂ)), Function.Injective P →
    DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → ∀ (f : L →ₗ[ℤ] L) (H : Matrix (Fin g) (Fin g) ℂ),
    (∀ x, P (f x) = H *ᵥ P x) → ((LinearMap.trace ℤ L f : ℤ) : ℂ) = H.trace + (starRingEnd ℂ) H.trace

def TraceDual : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (s : (F →+* ℂ) → ℂ),
    (∀ c : 𝓞 F, ∃ m : ℤ, ∑ τ : F →+* ℂ, τ (c : F) * s τ = m) → ∃ b : F, ∀ τ, s τ = τ b

def NewtonPoly : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (m : (F →+* ℂ) → Multiset ℂ), (∀ τ, (m τ).card = n) →
    (∀ j : ℕ, ∃ b : F, ∀ τ, ((m τ).map fun r => r ^ j).sum = τ b) →
    ∃ χ : F[X], χ.Monic ∧ χ.natDegree = n ∧ ∀ τ, χ.map τ = ((m τ).map fun r => X - C r).prod

def PowSumRat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ j : ℕ, ∃ b : F, ∀ τ, ((evFull ty ev τ).map fun r => r ^ j).sum = τ b

def RootsFull : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ χ : F[X], IsMinOf a ga χ → χ.natDegree = n → ∀ τ, rts χ τ = evFull ty ev τ

def MarkDiag : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ H : Matrix (Fin g) (Fin g) ℂ, ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ mu, IsMark a ρ t₀ H mu ↔ evAt ty ev t₀ = {mu}

def TspDiag : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (ty : Fin g → (F →+* ℂ)) (t₀ : F →+* ℂ) (i₀ : Fin g), ComplexEmbedding.conjugate t₀ ≠ t₀ →
    (∀ i, ty i = t₀ ↔ i = i₀) → (∀ i j, ty j = ComplexEmbedding.conjugate (ty i) → i = i₀ ∨ j = i₀) →
    ∀ W : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ),
    (∀ S, S ∈ W ↔ Sᵀ = S ∧ ∀ (c : 𝓞 F) i j, S i j * ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) * S i j) →
    Function.Bijective (fun (S : W) (j : {j // ty j = ComplexEmbedding.conjugate t₀}) => S.1 i₀ j.1)

def BallChar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ H : Matrix (Fin g) (Fin g) ℂ, H.det ≠ 0 → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ mu, evAt ty ev t₀ = {mu} →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), IsCoordC bar ρ M₀ co →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) → d = n - 1 ∧
      ∀ y : ℂ, LinearMap.det (1 - y • T) =
        ((evAt ty ev (ComplexEmbedding.conjugate t₀)).map fun r => 1 - y * (mu / (starRingEnd ℂ) r)).prod

def CspDim : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∃ co : (Fin (n - 1) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, IsCoordC bar ρ M₀ co

def FibDet : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (H : Matrix (Fin g) (Fin g) ℂ), ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ (k : ℕ) (α : Fin k → 𝓞 F) (y : ℂ),
    LinearMap.det (1 - y • fibMap H (diagAct a ρ α)) = ∏ s, ∏ i, (1 - ty i (α s : F) * (y * ev i))

def FibW : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ)
    (χ : F[X]) (mu : ℂ), (∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ) → 1 ≤ n →
    (∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1) →
    (∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ) → (∀ τ, rts χ τ = evFull ty ev τ) → evAt ty ev t₀ = {mu} →
    ∀ (x : F) (y : ℂ), (∏ i, (1 - ty i x * (y * ev i))) * (starRingEnd ℂ) (∏ i, (1 - ty i x * ev i)) = fibW t₀ ε x y χ mu

def EvIntegral : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ i (x : 𝓞 F), 1 - ty i ((2 * x : 𝓞 F) : F) * ev i ≠ 0

def EigTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), FixesPer D P₀ ga H → ∀ χ : F[X], IsMinOf a ga χ → χ.natDegree = n → χ.Separable →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), IsCoordC bar ρ M₀ co →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 F), (∀ s, (2 : 𝓞 F) ∣ α s) → (∃ mu, IsMark a ρ t₀ H mu) ∧ ∀ mu, IsMark a ρ t₀ H mu →
      mu ∈ rts χ t₀ ∧ LinearMap.det (1 - T) ≠ 0 ∧ LinearMap.det (1 - fibMap H (diagAct a ρ α)) ≠ 0 ∧
      ∀ t : ℂ, LinearMap.det (1 - t • T) / LinearMap.det (1 - T) * (LinearMap.det (1 - t • fibMap H (diagAct a ρ α)) *
        (starRingEnd ℂ) (LinearMap.det (1 - fibMap H (diagAct a ρ α)))) = locW t₀ ε α t χ mu

def RootSumW : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (m : ℕ),
    ComplexEmbedding.conjugate t₀ ≠ t₀ → (∀ i, lam (ComplexEmbedding.conjugate t₀) i = m) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 F) ∣ α s) ∧
      ∀ (χ : F[X]) (r : (F →+* ℂ) → Fin n → ℂ), χ.Separable → (∀ τ, rts χ τ = Finset.univ.val.map (r τ)) → ∀ y : ℂ,
        (c.sum fun α w => w * ((rts χ t₀).map fun mu => locW t₀ ε α y χ mu).sum) =
          (∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ)) *
            (y ^ ((n - 1) * m + ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ i, lam τ i) *
              ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))

def RootSumWOff : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (m : ℕ),
    ComplexEmbedding.conjugate t₀ ≠ t₀ → (∀ i, lam t₀ i = m) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 F) ∣ α s) ∧
      ∀ (χ : F[X]) (r : (F →+* ℂ) → Fin n → ℂ), χ.Separable → (∀ τ, rts χ τ = Finset.univ.val.map (r τ)) → χ.coeff 0 ≠ 0 → (∃ q : ℝ, ∀ z ∈ rts χ t₀, z * (starRingEnd ℂ) z = q) → ∀ y : ℂ,
        (c.sum fun α w => w * ((rts χ t₀).map fun mu => locW t₀ ε α y χ mu).sum) =
          (∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ)) *
            (y ^ (m + ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ i, lam τ i) *
              ∑ i : Fin n, y ^ (∑ j ∈ Finset.univ.erase i, lam (ComplexEmbedding.conjugate t₀) j + (i : ℕ)))

end UpperTheory.Gal.W2
