import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GlobalLocalFactorization
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

def sph (α : kˣ) (n'' n' n : Type) [Fintype n''] [Fintype n'] [Fintype n] : Matrix n' n'' k × Matrix n n' k → ℂ :=
  tens (ind (stdL k n'') (scal α (stdL k n'))) (ind (stdL k n') (scal α (stdL k n)))

def moved (g : GL n' k) (Ξ : Matrix n' n'' k × Matrix n n' k → ℂ) (x : Matrix n' n'' k × Matrix n n' k) : ℂ :=
  Ξ ((g⁻¹ : GL n' k).val * x.1, x.2 * g.val)

def homLat (α : kˣ) (n'' n' n : Type) : AddSubgroup (Matrix n' n'' k × Matrix n n' k) where
  carrier := {x | (∀ r s, ((α⁻¹ : kˣ) : k) * x.1 r s ∈ 𝒪[k]) ∧ ∀ r s, ((α⁻¹ : kˣ) : k) * x.2 r s ∈ 𝒪[k]}
  add_mem' h h' := ⟨fun r s => by simpa [mul_add] using add_mem (h.1 r s) (h'.1 r s),
    fun r s => by simpa [mul_add] using add_mem (h.2 r s) (h'.2 r s)⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  neg_mem' h := ⟨fun r s => by simpa using h.1 r s, fun r s => by simpa using h.2 r s⟩

end Local

def GoodMoved : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k Circle) (ν : Measure k) (α α' : kˣ), HasConductor ψ (α * α') → IsUnitVol ν →
    ∀ (n'' n' n : Type) [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n] (σ j : ℕ),
      Even j →
      let Λ₀ := mono (2 * σ + 1 + 1 + 1) (stdL k n'') (idl α α' (σ + 2 + j / 2) j)
      let Λ₁ := mono (2 * σ + 1 + 1) (stdL k n') (idl α α' (σ + 2 + j / 2) (j + 1))
      let Λ₂ := mono (2 * σ + 1) (stdL k n) (idl α α' (σ + 2 + j / 2) (j + 1 + 1))
      ∃ e : ℤ, (valuation k (α : k) = 1 → valuation k (α' : k) = 1 → e = 0) ∧ ∀ μ₁ μ₂, IsUnram μ₁ → IsUnram μ₂ →
        OneCell ψ ν σ μ₁ μ₂ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) (stab Λ₁) (stab Λ₂) ∧
        ∀ L : Rec k n'' n' n σ, IsRec ψ μ₁ μ₂ (stab Λ₂) (fun _ => 1) L → ∀ g : GL n' k, GeneralLinearGroup.det g = 1 →
          CellValue ψ ν σ μ₁ μ₂ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) 1 (stab Λ₁) (stab Λ₂) (KO k n') (KO k n) L
            (((√(resCard k : ℝ) : ℝ) : ℂ) ^ e) (L (moved g (sph α n'' n' n)) 1)

def GoodConst : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k Circle) (ν : Measure k) (α α' : kˣ), HasConductor ψ (α * α') → IsUnitVol ν →
    ∀ (n'' n' n : Type) [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n] (σ j : ℕ),
      Even j →
      let Λ₀ := mono (2 * σ + 1 + 1 + 1) (stdL k n'') (idl α α' (σ + 2 + j / 2) j)
      let Λ₁ := mono (2 * σ + 1 + 1) (stdL k n') (idl α α' (σ + 2 + j / 2) (j + 1))
      let Λ₂ := mono (2 * σ + 1) (stdL k n) (idl α α' (σ + 2 + j / 2) (j + 1 + 1))
      ∃ r : ℝ, 0 < r ∧ (∃ e : ℤ, r = √(resCard k : ℝ) ^ e) ∧ (valuation k (α : k) = 1 → valuation k (α' : k) = 1 → r = 1) ∧
        ∀ μ₁ μ₂, IsUnram μ₁ → IsUnram μ₂ → ∀ L : Rec k n'' n' n σ, IsRec ψ μ₁ μ₂ (stab Λ₂) (fun _ => 1) L →
          CellValue ψ ν σ μ₁ μ₂ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) 1 (stab Λ₁) (stab Λ₂) (KO k n') (KO k n) L 1
            (L ((r : ℂ) • sph α n'' n' n) 1)

def GoodPoint : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k Circle) (ν : Measure k) (α α' : kˣ), HasConductor ψ (α * α') → IsUnitVol ν →
    ∀ (n'' n' n : Type) [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n] (σ j : ℕ),
      Even j →
      let Λ₀ := mono (2 * σ + 1 + 1 + 1) (stdL k n'') (idl α α' (σ + 2 + j / 2) j)
      let Λ₁ := mono (2 * σ + 1 + 1) (stdL k n') (idl α α' (σ + 2 + j / 2) (j + 1))
      let Λ₂ := mono (2 * σ + 1) (stdL k n) (idl α α' (σ + 2 + j / 2) (j + 1 + 1))
      ∃ e : ℤ, (valuation k (α : k) = 1 → valuation k (α' : k) = 1 → e = 0) ∧
        dSym ψ ν σ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) = ((√(resCard k : ℝ) : ℝ) : ℂ) ^ e • sph α n'' n' n

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

variable {c : Comm D}

def VacMid (v : VCom c) (t : Tup c) : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∉ v.tP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∉ v.tP) Ψ₂ →
    BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∉ v.tP) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)

end Global

end GlobalTheory.PlaceCompare.Spherical

end
