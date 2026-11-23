import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

open Classical in

theorem heisInv_forms_proportional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ l e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, l (ρ u m) = l m) → (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h l e hl he m
  have hH := h.isHeis

  have key : ∀ (f : M →ₗ[ℂ] ℂ), (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, f (ρ u m) = f m) →
      ∀ x : Matrix (Fin n') (Fin n) L, f (ρ x s) = if x ∈ intMat L (Fin n') (Fin n) then f s else 0 := by
    intro f hf x
    split_ifs with hx
    · rw [h.fixes x hx]
    · have : ∃ i j, x i j ∉ Formalism.UG.intL L := by
        by_contra hc
        push_neg at hc
        exact hx hc
      obtain ⟨i, j, hij⟩ := this
      obtain ⟨u, hu, hne⟩ := GlobalTheory.SphTheta.exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hij
      have hu' : Matrix.single i.rev j.rev u ∈ intMat L (Fin n') (Fin n) := by
        intro i' j'
        rw [Matrix.single_apply]
        split_ifs
        exacts [hu, zero_mem _]
      have hc := hH.comm (Matrix.single i.rev j.rev u) x s
      rw [h.fixes _ hu'] at hc
      have h1 := hf _ hu' (ρ x s)
      rw [hc, map_smul, smul_eq_mul, hH.swap] at h1
      have hz : (GlobalTheory.SphTheta.pairing σ δ ψ x (Matrix.single i.rev j.rev u))⁻¹ ≠ 1 := by
        intro h'; exact hne (inv_eq_one.1 h')
      have : ((GlobalTheory.SphTheta.pairing σ δ ψ x (Matrix.single i.rev j.rev u))⁻¹ - 1) * f (ρ x s) = 0 := by
        rw [sub_mul, one_mul, h1, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz)
  have hall : (l s) • e = (e s) • l := by
    refine LinearMap.ext_on_range h.2.2.2 fun x => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, key e he x, key l hl x]
    split_ifs <;> ring
  have := LinearMap.congr_fun hall m
  simp only [LinearMap.smul_apply, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

end GlobalTheory.ChainOnto

end
