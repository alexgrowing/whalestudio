import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CovTop.VolUp.RatStab

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (V : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V) (δ : GL (Fin V.rank) D.host.E), (hat (maximalRealSubfield D.host.E) (L : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) = ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).mulVec '' (hat (maximalRealSubfield D.host.E) (Λ : Set (Fin V.rank → D.host.E)) : Set (Fin V.rank → RA (maximalRealSubfield D.host.E) D.host.E)) → IsUStab (-(V.gram)ᵀ) L δ → ∃ γ ∈ GQ V, (∀ τ θ, IsInfEmb τ θ → infMat D.sp.cm.sig V.gram θ γ = (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ) ∧ IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (Λ : Set (Fin V.rank → D.host.E)) 1 ((finHom V (g⁻¹ * γ * g)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V Λ L g δ hhat hδ
  have : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨γ₀, hQ, hfin, harch⟩ := GlobalTheory.RepConv.exists_rat V δ hδ.1
  refine ⟨γ₀, hQ, fun τ θ hθ => harch τ θ hθ, ?_⟩
  have hLδ : ∀ x ∈ L, ∃ y ∈ L, (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = (1 : ℕ) • y :=
    fun x hx => ⟨_, sub_mem ((hδ.2 x).1 hx) hx, by simp⟩
  have hLδi : ∀ x ∈ L, ∃ y ∈ L, ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = (1 : ℕ) • y := by
    intro x hx
    have hx' : ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x ∈ L := by
      rw [hδ.2]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact hx
    exact ⟨_, sub_mem hx' hx, by simp⟩
  have hf : (finHom V (g⁻¹ * γ₀ * g)).1 =
      ((finHom V g)⁻¹).1 * (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1 := by
    rw [← hfin]
    simp only [map_mul, map_inv, Units.val_mul]
  have hfi : (finHom V (g⁻¹ * γ₀⁻¹ * g)).1 =
      ((finHom V g)⁻¹).1 * ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1 := by
    have hfin' : ((finHom V γ₀)⁻¹).1 = ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) := by
      apply Units.inv_eq_of_mul_eq_one_left
      rw [hfin, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [← hfin']
    simp only [map_mul, map_inv, Units.val_mul]
  have c1 := GlobalTheory.RepConv.hat_cong_conj (F := D.host.F) (Λ : Set (Fin V.rank → D.host.E))
      (L : Set (Fin V.rank → D.host.E)) (finHom V g) hhat δ.1 1 hLδ
  have c2 := GlobalTheory.RepConv.hat_cong_conj (F := D.host.F) (Λ : Set (Fin V.rank → D.host.E))
      (L : Set (Fin V.rank → D.host.E)) (finHom V g) hhat (δ⁻¹ : GL (Fin V.rank) D.host.E).1 1 hLδi
  refine ⟨GlobalTheory.FinUA.isUA_finHom D V _, ?_, ?_⟩
  · intro x hx
    rw [hf]
    exact c1 x hx
  · intro x hx
    obtain ⟨y, hy, e⟩ := c2 x hx
    refine ⟨(finHom V (g⁻¹ * γ₀⁻¹ * g)).1 *ᵥ x, ?_, ?_⟩
    · rw [hfi]
      have : (((finHom V g)⁻¹).1 * ((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) * (finHom V g).1) *ᵥ x = x + (1 : ℕ) • y := by
        rw [← e]; abel
      rw [this]; exact add_mem hx (by simpa using hy)
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
      have : g⁻¹ * γ₀ * g * (g⁻¹ * γ₀⁻¹ * g) = 1 := by group
      rw [this, map_one, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.CovTop.VolUp.RatStab
