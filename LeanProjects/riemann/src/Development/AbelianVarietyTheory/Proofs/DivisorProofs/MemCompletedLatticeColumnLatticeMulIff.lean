import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatMulAd

variable {D : D7}

theorem mulVec_map_mem_hatL {n : ℕ} (g : Matrix (Fin n) (Fin n) D.host.E)
    (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hg : ∀ x ∈ Λ, g *ᵥ x ∈ Λ') (y : Fin n → EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    g.map (eToEAf D) *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨g *ᵥ x, hg x hx, ?_⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have : g.map (eToEAf D) *ᵥ (r • a) = r • (g.map (eToEAf D) *ᵥ a) := by
      show _ = (r : EAf D) • (g.map (eToEAf D) *ᵥ a)
      rw [← Matrix.mulVec_smul]
      rfl
    rw [this]; exact Submodule.smul_mem _ r ha

theorem mem_hatL_colLat_mul (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E) : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  intro v
  have h1 : ∀ x ∈ colLat B, (γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat (γ * B) := by
    intro x hx
    rw [colLat_mul]
    exact ⟨x, hx, rfl⟩
  have h2 : ∀ x ∈ colLat (γ * B), ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat B := by
    intro x hx
    rw [colLat_mul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ y) ∈ _
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy
  constructor
  · intro hv
    exact mulVec_map_mem_hatL _ _ _ h2 v hv
  · intro hv
    have := mulVec_map_mem_hatL _ _ _ h1 _ hv
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec] at this

end GlobalTheory.LatMulAd
