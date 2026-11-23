import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto

noncomputable section

namespace GlobalTheory.MBModel

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA] [IsCommMonObj AA]
  {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {n : ℕ}

def RigIs (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) (σ : K →+* ℂ) {Q : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ P.A.left}
    (wσ : LB.Iso ((lbPow P.L n).pull ψ) (lbPow Q.L n)) {g : ℕ} (u : HolUnif Q.A Q.L g) (ρ : ℂ) : Prop :=
  ∀ (k : (lbPow Q.L n).ι) (j : ((lbPow P.L n).pull ψ).ι) (p : PUnit → MM.L.ι),
    ⊤ ≤ (u.ex 0).left ⁻¹ᵁ ((lbPow Q.L n).U k ⊓ ((lbPow P.L n).pull ψ).U j) →
    ⊤ ≤ ((u.ex 0).left ≫ ψ) ⁻¹ᵁ ((lbPow P.L n).U (j PUnit.unit) ⊓ (MM.L.pull φ).U p) →
    valAt' (u.ex 0).left ((lbPow Q.L n).U k ⊓ ((lbPow P.L n).pull ψ).U j) (wσ.s (k, j)).val *
      valAt' ((u.ex 0).left ≫ ψ) ((lbPow P.L n).U (j PUnit.unit) ⊓ (MM.L.pull φ).U p) (w.s (j PUnit.unit, p)).val *
      valAt' (X := (𝟙_ (Over (Sp (𝓞 K)))).left) (spMap (σ.comp (algebraMap (𝓞 K) K))) ((MM.L.pull (eSec AA)).U p)
        (MM.rig.s p).val = ρ * u.fr (k PUnit.unit) 0 ^ n

def IsThetaMeanSquareNorm (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) {r : ℕ} (b : Fin r → (lbPow P.L n).Sec)
    (hE : HermFam K (Fin r → K)) (g : ℕ) : Prop :=
  ∀ (σ : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P.A.left)
    (wσ : LB.Iso ((lbPow P.L n).pull ψ) (lbPow Q.L n)) (s : Fin r → (lbPow Q.L n).Sec)
    (u : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ρ : ℂ)
    (θ : Fin r → (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
    IsPolFibre σ P Q ψ → wσ.IsGen → (∀ i, SecMaps wσ (secPull (b i) ψ) (s i)) → u.IsAH Hm χ → RigIs w σ wσ u ρ →
    (∀ i, u.IsFnPow n (s i) (θ i)) → IsAddFundamentalDomain u.Λ Fd volume →
    ∀ i j, hE.form σ (Pi.single i 1) (Pi.single j 1) =
      (∫ z in Fd, starRingEnd ℂ (θ i z) * θ j z * (Real.exp (-(Real.pi * n * (hermForm Hm z z).re)) : ℝ)) /
        (((volume Fd).toReal * ‖ρ‖ ^ 2 : ℝ) : ℂ)

def IsModel (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) : Prop :=
  Smooth AA.hom ∧ IsSeparated AA.hom ∧ QuasiCompact AA.hom ∧ IsGrpPullback P.A AA (spMap (algebraMap (𝓞 K) K)) φ ∧
  (∃ (G : Over (Sp (𝓞 K))) (_ : GrpObj G) (j : G ⟶ AA) (φ₀ : P.A.left ⟶ G.left), IsSemiAbelian G ∧ IsMonHom j ∧
    IsOpenImmersion j.left ∧ φ₀ ≫ j.left = φ ∧ IsGrpPullback P.A G (spMap (algebraMap (𝓞 K) K)) φ₀) ∧
  Nonempty (CubicalStr AA MM) ∧ w.IsGen ∧
  ∃ (Z : Scheme.{0}) (ζ : Z ⟶ AA.left), IsClosedImmersion ζ ∧ IsFinite (ζ ≫ AA.hom) ∧ Flat (ζ ≫ AA.hom) ∧
    ∀ (T : Over (Sp K)) (x : T ⟶ P.A), x ^ (2 * n) = 1 ↔ ∃ y : T.left ⟶ Z, y ≫ ζ = x.left ≫ φ

end GlobalTheory.MBModel

namespace GlobalTheory.Published

open GlobalTheory.MBModel

def MoretBaillyModel : Prop := ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K)),
  F.IsHerm h → ∀ n : ℕ, 1 ≤ n → ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'],
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) (_ : GrpObj AA) (_ : IsCommMonObj AA)
      (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (w : LB.Iso (MM.L.pull φ) (lbPow P.L n))
      (b : Fin (n ^ F.P₀.g) → (lbPow P.L n).Sec) (E : Submodule (𝓞 K'') (Fin (n ^ F.P₀.g) → K''))
      (hE : HermFam K'' (Fin (n ^ F.P₀.g) → K'')),
      IsPolFibre (algebraMap K K'') F.P₀ P ψ ∧ IsModel w ∧
      Function.Bijective (fun c : Fin (n ^ F.P₀.g) → K'' => secComb P.A.hom c b) ∧
      (∀ c, c ∈ E ↔ ∃ t : MM.L.Sec, SecMaps w (secPull t φ) (secComb P.A.hom c b)) ∧
      IsThetaMeanSquareNorm w b hE F.P₀.g ∧ Full E ∧
      MuLe hE E (-F.falt h / 2 + (F.P₀.g : ℝ) / 4 * Real.log (n / (2 * Real.pi))) ∧
      deg hE E = (n ^ F.P₀.g : ℕ) * (-F.falt h / 2 + (F.P₀.g : ℝ) / 4 * Real.log (n / (2 * Real.pi)))

end GlobalTheory.Published

end
