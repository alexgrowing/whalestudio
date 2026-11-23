import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralLinearFormOnBasis
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.PolFan

theorem exists_intLinear_on_cone : ∀ (g : ℕ) (φs : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFan id g φs → Module.finrank ℤ X ≤ g → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone id φs γ → ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ be : LinearMap.BilinForm ℤ X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be ∧ (ℓ be : ℝ) = φs.evalZ be := by
  intro g φs X _ _ _ hφ hX m γ hγ
  have hP : IsPolFanOn id φs X := hφ X hX
  have hn : ∀ i, ∃ n : ℕ, φs.evalZ (γ i) = n := fun i => hP.exists_nat (hγ.mem i) (hγ.nonneg i)
  choose n hn using hn
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.BalExt.exists_linearForm_ext id X m γ hγ.mem hγ.basis (fun i => (n i : ℤ))
  refine ⟨ℓ, fun be _ c hc hbe => ?_⟩
  have key : (ℓ be : ℝ) = ∑ i, c i * (n i : ℝ) := by
    have h0 : ∑ k : Fin m ⊕ Unit, (Sum.elim c (fun _ => (-1 : ℝ)) k) •
        toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] _) (Sum.elim γ (fun _ => be) k)) = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Finset.univ_unique, Finset.sum_singleton, neg_one_smul]
      rw [← hbe, add_neg_cancel]
    have h1 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h0
    rw [Fintype.sum_sum_type] at h1
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, hℓ] at h1
    push_cast at h1
    linarith
  have hnn : (0 : ℝ) ≤ ℓ be := key ▸ Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (Nat.cast_nonneg _)
  refine ⟨by exact_mod_cast hnn, ?_⟩
  rw [key, ← evalR_toReal, hbe, (linearOn_iff φs γ).1 hγ.linear c hc]
  simp only [hn]

end GlobalTheory.PolFan
