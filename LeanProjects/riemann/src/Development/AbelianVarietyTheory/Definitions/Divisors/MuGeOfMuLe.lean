import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel

noncomputable section

namespace GlobalTheory.MBLow

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

def MuGe (h : HermFam K (Fin m → K)) (E : Submodule (𝓞 K) (Fin m → K)) (ν : ℝ) : Prop :=
  ∀ V : Submodule K (Fin m → K), ((m : ℝ) - Module.finrank K V) * ν ≤ deg h E - deg h (E ⊓ V.restrictScalars (𝓞 K))

def JetSysLow (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) (n : ℕ) (ν : ℝ)
    (β : ℕ → (K →+* ℂ) → ℝ) : Prop :=
  ∃ (r : ℕ) (hE : HermFam K (Fin r → K)) (E : Submodule (𝓞 K) (Fin r → K)) (Vf : ℕ → Submodule K (Fin r → K))
    (j : ℕ → (Fin r → K) →ₗ[K] K), Full E ∧ MuGe hE E ν ∧ Vf 0 = ⊤ ∧ ∀ i ≤ n,
      Vf (i + 1) = Vf i ⊓ LinearMap.ker (j i) ∧ (∃ v ∈ Vf i, j i v ≠ 0) ∧
      (∀ v ∈ E, v ∈ Vf i → ∀ a : K, a • x ∈ L → IsIntegral ℤ (a ^ i * j i v)) ∧
      ∀ (σ : K →+* ℂ) (q : ℕ) (v : Fin q → Fin r → K) (c : Fin q → ℂ), (∀ a, v a ∈ Vf i) →
        ‖∑ a, c a * σ (j i (v a))‖ ^ 2 ≤
          (β i σ * h.nrm σ x ^ i) ^ 2 * (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)).re

end Lat

def IsWeak {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA] [IsCommMonObj AA]
    {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {n : ℕ} (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) : Prop :=
  IsSemiAbelian AA ∧ IsGrpPullback P.A AA (spMap (algebraMap (𝓞 K) K)) φ ∧ Nonempty (CubicalStr AA MM) ∧ w.IsGen

def IsOver {K : Type} [Field K] [NumberField K] (F : SemiFib K) {K'' : Type} [Field K''] [NumberField K''] [Algebra K K'']
    {P : Out.PolAV (Sp K'')} (ψ : P.A.left ⟶ F.P₀.A.left) {AA : Over (Sp (𝓞 K''))} [GrpObj AA]
    (φ : P.A.left ⟶ AA.left) : Prop :=
  IsPolFibre (algebraMap K K'') F.P₀ P ψ ∧ ∃ j : AA.left ⟶ F.G.left,
    IsGrpPullback AA F.G (spMap (algebraMap (𝓞 K) (𝓞 K''))) j ∧ φ ≫ j = ψ ≫ F.φ

def SectionsLow : Prop := ∀ g : ℕ, 0 < g → ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g →
  ∀ h : HermFam K (Fin F.P₀.g → K), F.IsHerm h → ∀ m : ℕ, 1 ≤ m →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'],
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) (_ : GrpObj AA) (_ : IsCommMonObj AA)
      (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (w : LB.Iso (MM.L.pull φ) (lbPow P.L (4 * m ^ 2))) (r : ℕ)
      (b : Fin r → (lbPow P.L (4 * m ^ 2)).Sec) (E : Submodule (𝓞 K'') (Fin r → K'')) (hE : HermFam K'' (Fin r → K'')),
      IsOver F ψ φ ∧ IsWeak w ∧ Function.Bijective (fun c : Fin r → K'' => secComb P.A.hom c b) ∧
      (∀ c ∈ E, ∃ t : MM.L.Sec, SecMaps w (secPull t φ) (secComb P.A.hom c b)) ∧
      IsThetaMeanSquareNorm w b hE F.P₀.g ∧ Full E ∧ MuGe hE E (-F.falt h / 2 - C)

def SecJetsLow : Prop := ∀ g : ℕ, 0 < g → ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g →
  ∀ (h : HermFam K (Fin F.P₀.g → K)) (ρ : (K →+* ℂ) → ℝ), F.IsHerm h → F.IsRho ρ →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (x : Fin F.P₀.g → K'), x ≠ 0 → ∀ n : ℕ, 2 ≤ n →
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (h'' : HermFam K'' (Fin F.P₀.g → K'')), IsBC h h'' ∧
      JetSysLow h'' (latBC K'' F.lieLat) (fun i => algebraMap K' K'' (x i)) n (-F.falt h / 2 - C)
        fun i σ => jetBd F.P₀.g (4 * n ^ 2) i (ρ (σ.comp (algebraMap K K'')))

theorem muGe_of_muLe {K : Type} [Field K] [NumberField K] {m : ℕ} {h : HermFam K (Fin m → K)}
    {E : Submodule (𝓞 K) (Fin m → K)} {ν : ℝ} (h₁ : MuLe h E ν) (h₂ : deg h E = m * ν)
    (h₃ : ∀ V : Submodule K (Fin m → K), latRank K (E ⊓ V.restrictScalars (𝓞 K)) = Module.finrank K V) : MuGe h E ν := by
  intro V
  have := h₁ (E ⊓ V.restrictScalars (𝓞 K)) inf_le_left
  rw [h₃] at this
  rw [h₂]
  linarith

end GlobalTheory.MBLow

end
