import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace GlobalTheory.DefLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Poly

variable {ι : Type} {m n : ℕ}

abbrev Pol (ι : Type) (m n : ℕ) : Type := MvPolynomial (ι × Fin m × Fin n) ℂ

def subst (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) : Pol ι m n →ₐ[ℂ] Pol ι m n :=
  MvPolynomial.aeval fun v => ∑ i, ∑ c, (b v.1 i v.2.1 * a v.1 v.2.2 c) • MvPolynomial.X (v.1, i, c)

open Classical in

def rowSub (n : ℕ) (τ : ι) (u : Matrix.unitaryGroup (Fin m) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun _ => 1) (fun ρ => if ρ = τ then (u : Matrix (Fin m) (Fin m) ℂ) else 1)).toLinearMap

open Classical in

def colSub (m : ℕ) (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun ρ => if ρ = τ then star (g : Matrix (Fin n) (Fin n) ℂ) else 1) (fun _ => 1)).toLinearMap

def rowLie (n : ℕ) (τ : ι) (k l : Fin m) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ c : Fin n, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, k, c)) ∘ₗ (MvPolynomial.pderiv (τ, l, c)).toLinearMap

def colLie (m : ℕ) (τ : ι) (k l : Fin n) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ i : Fin m, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, k)) ∘ₗ (MvPolynomial.pderiv (τ, i, l)).toLinearMap

theorem rowLie_apply (τ : ι) (k l : Fin m) (P : Pol ι m n) :
    rowLie n τ k l P = ∑ c : Fin n, MvPolynomial.X (τ, k, c) * MvPolynomial.pderiv (τ, l, c) P := by
  simp [rowLie, LinearMap.sum_apply]

theorem colLie_apply (τ : ι) (k l : Fin n) (P : Pol ι m n) :
    colLie m τ k l P = ∑ i : Fin m, MvPolynomial.X (τ, i, k) * MvPolynomial.pderiv (τ, i, l) P := by
  simp [colLie, LinearMap.sum_apply]

end Poly

def IrrFam {ι κ X : Type} [AddCommGroup X] [Module ℂ X] (π : ι → κ → Module.End ℂ X) : Prop :=
  ∀ U : Submodule ℂ X, (∀ τ u, ∀ x ∈ U, π τ u x ∈ U) → U = ⊥ ∨ U = ⊤

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def AllPlus (M : DSModel V S) : Prop := ∀ τ a, M.ε τ a = true

def unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (M.fr τ)⁻¹ * u * M.fr τ

def IsTensAct (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) : Prop :=
  ∀ τ u x, inclT M (π τ u x) = actT M τ (unfr M τ u) (inclT M x)

variable {M : DSModel V S}

theorem AllPlus.jm (h : AllPlus M) (τ : D.what₂.Tau) : Formalism.REAL.Jm (M.ε τ) = 1 := by
  unfold Formalism.REAL.Jm
  simp [h τ]

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem AllPlus.gram (h : AllPlus M) (τ : D.what₂.Tau) : gramAt D V τ = (M.fr τ)ᴴ * M.fr τ := by
  rw [← M.fr_gram τ, h.jm, Matrix.mul_one]

theorem AllPlus.posDef (h : AllPlus M) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  rw [h.gram]
  exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (M.fr_unit τ))

theorem AllPlus.cart (h : AllPlus M) (τ : D.what₂.Tau) : cart M τ = 1 := by
  unfold Links.cart
  rw [h.jm, Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem fr_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.fr τ * unfr M τ u * (M.fr τ)⁻¹ = u := by
  unfold unfr
  rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ),
    Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M τ)]

theorem rep_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.rep τ (unfr M τ u) = M.σ τ u := by
  unfold DSModel.rep
  rw [fr_unfr]

theorem AllPlus.unfr_mem (h : AllPlus M) (τ : D.what₂.Tau) (u : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    unfr M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hu : (u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  have e : M.fr τ * unfr M τ u = u * M.fr τ := by
    unfold unfr
    rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ)]
  show (unfr M τ u)ᴴ * gramAt D V τ * unfr M τ u = gramAt D V τ
  rw [h.gram]
  calc _ = (M.fr τ * unfr M τ u)ᴴ * (M.fr τ * unfr M τ u) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u) * M.fr τ := by
      rw [e]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hu, Matrix.mul_one]

theorem AllPlus.exists_unfr (h : AllPlus M) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : ∃ u : Matrix.unitaryGroup (Fin V.rank) ℂ, unfr M τ u = g := by
  have hg' : gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g = (M.fr τ)ᴴ * M.fr τ := by rw [← h.gram]; exact hg
  refine ⟨⟨M.fr τ * g * (M.fr τ)⁻¹, Matrix.mem_unitaryGroup_iff'.2 ?_⟩, ?_⟩
  · calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ (fr_det M τ)]; simp
  · show (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ = g
    rw [Matrix.mul_assoc (M.fr τ), Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M τ),
      Matrix.nonsing_inv_mul_cancel_right _ _ (fr_det M τ)]

end Model

end GlobalTheory.DefLift

end
