import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ArchFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∃ kp σ, IsFMat L kp σ

def FForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) kp σ, IsFMat L kp σ → ∃ A : Matrix (Fin G.n) (Fin G.n) G.F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj G.F))ᵀ = -A ∧
    (∀ u w, D.EF.baseChange ℚ u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u))) ∧
    ∀ c, A * σ (sh G c) = ((σ c).map (IsCMField.complexConj G.F))ᵀ * A

def SN : Prop :=
  ∀ (F K : Type) [Field F] [Field K] (n : ℕ) (τ : F →+* K) (ψ : Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) K),
    (∀ x : F, ψ (Matrix.scalar (Fin n) x) = Matrix.scalar (Fin n) (τ x)) →
    ∃ S : Matrix (Fin n) (Fin n) K, S.det ≠ 0 ∧ ∀ M, ψ M * S = S * M.map τ

def ArchSpan : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ),
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) => v.embedding (x i)) = ⊤ ∧
    Module.finrank ℝ (InfinitePlace F → Fin n → ℂ) = n * Module.finrank ℚ F ∧
    ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re

def ArchEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → Nonempty (ArchFrame L)

def SigB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKCx.Form G) (v : InfinitePlace G.F), (GlobalTheory.LKCx.herm G v B.β).IsHermitian ∧
    (sigPosH (G.gram_herm v) = 1 → (∃ z, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re) ∧ ∀ z x, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re →
      x ≠ 0 → hv (GlobalTheory.LKCx.herm G v B.β) x z = 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → ∀ x, x ≠ 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0)

def PerExt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), ∀ w, Q w = R (A.th w)

def JStruct : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    (∀ v, (GlobalTheory.LKCx.herm G v β).IsHermitian) → ∀ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), (∀ w, Q w = R (A.th w)) →
    ∃ J : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ, (∀ x : Arch G, R (fun v => J v *ᵥ x v) = Complex.I • R x) ∧
      ∀ v, IsPosJ (GlobalTheory.LKCx.herm G v β) (J v) (sgnV L v)

def JLine : Prop :=
  ∀ (n : ℕ) (M J : Matrix (Fin n) (Fin n) ℂ) (s : ℂ), M.IsHermitian → (s = 1 ∨ s = -1) → IsPosJ M J s →
    (∀ z, z ≠ 0 → J *ᵥ z = (s * Complex.I) • z → 0 < (hv M z z).re) ∧
    ((∀ x, x ≠ 0 → (hv M x x).re < 0) → J = -(s * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    ((∃ z, 0 < (hv M z z).re) → ∃ z, z ≠ 0 ∧ J *ᵥ z = (s * Complex.I) • z) ∧
    ∀ z, 0 < (hv M z z).re → (∀ x, x ≠ 0 → hv M x z = 0 → (hv M x x).re < 0) → J *ᵥ z = (s * Complex.I) • z →
      ∀ x, J *ᵥ x = (s * Complex.I) • ((2 * (hv M x z / hv M z z)) • z - x)

def HermOfJ : Prop :=
  ∀ (g : ℕ) (E : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ), (∀ x, E x x = 0) → (∀ x y, E (Complex.I • x) (Complex.I • y) = E x y) →
    (∀ x, x ≠ 0 → 0 < E (Complex.I • x) x) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm x y).im = E x y

def LineBasis : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), M.IsHermitian → 0 < (hv M z z).re →
    ∃ (i₀ : Fin n) (S : Matrix (Fin n) (Fin n) ℂ), S.det ≠ 0 ∧ S *ᵥ Pi.single i₀ 1 = z ∧ ∀ i, i ≠ i₀ → hv M (S *ᵥ Pi.single i 1) z = 0

def PlaceT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    (∀ v', sigPosH (G.gram_herm v') = 1 → v' = v) ∧ t₀ (D.ω : D.F) = D.ρc ∧ (starRingEnd ℂ) D.ρc ≠ D.ρc ∧
    ((sgnV L v = 1 ∧ ∀ x, v.embedding (L.e x) = t₀ x) ∨
      (sgnV L v = -1 ∧ (¬ ∀ x, v.embedding (L.e x) = t₀ x) ∧ ∀ x, (starRingEnd ℂ) (v.embedding (L.e x)) = t₀ x))

def TypeIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ i₀ : Fin G.n, ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ),
      (∀ x : Arch G, R (fun v' i => (if v' = v ∧ i = i₀ then 1 else -1) * (sgnV L v' * Complex.I) * x v' i) = Complex.I • R x) ∧
      ∀ (c : 𝓞 D.F) (x : Arch G), R (fun v' => v'.embedding (L.e (c : D.F)) • x v') = ρ (algebraMap (𝓞 D.F) D.O c) *ᵥ R x

def RPer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (A : ArchFrame L) (B : GlobalTheory.LKCx.Form G) (z : GlobalTheory.LKCx.PosV G v B.β),
    ∃ (Q : VQ D →+ (Fin D.g → ℂ)) (R : Arch G →ₗ[ℝ] (Fin D.g → ℂ)), IsPerQ L B.β ρ Q ∧ (∀ w, Q w = R (A.th w)) ∧
      R (Pi.single v (Complex.I • z.1)) = (sgnV L v * Complex.I) • R (Pi.single v z.1)

end UpperTheory.Gal.W2
