import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

namespace GlobalTheory.ThetaRiesz

theorem thetaPair_of_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  intro k _ _ _ _ r n V W _ _ _ _ μ σ π hadm hunit hμ b hb hb_inv
  obtain ⟨Bf, hsym, hpos, hinv⟩ := hunit
  obtain ⟨hone, hmul, -, -, hop⟩ := om_isSmoothRepresentation k (Fin r) (Fin n) μ hμ

  have huniq : ∀ u u' : V, (∀ w, Bf u w = Bf u' w) → u = u' := by
    intro u u' h
    by_contra hne
    have hne' : u - u' ≠ 0 := sub_ne_zero.2 hne
    have hfun : Bf (u - u') = 0 := by rw [map_sub, LinearMap.ext h, sub_self]
    have h0 : Bf (u - u') (u - u') = 0 := by rw [hfun, LinearMap.zero_apply]
    have := hpos _ hne'
    rw [h0] at this
    simp at this

  let S : SB (Matrix (Fin n) (Fin r) k) → Subgroup (GL (Fin r) k) := fun Φ =>
    { carrier := {g | om μ g 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ}
      one_mem' := hone _
      mul_mem' := by
        intro x y hx hy
        show om μ (x * y) 1 _ = _
        have := hmul x y 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [mul_one] at this
        rw [this]
        have hy' : om μ y 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hy
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        rw [hy', hx']
      inv_mem' := by
        intro x hx
        have hx' : om μ x 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hx
        show om μ x⁻¹ 1 _ = _
        have := hmul x⁻¹ x 1 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ)
        rw [inv_mul_cancel, mul_one, hx', hone] at this
        exact this.symm }
  have hSo : ∀ Φ, IsOpen ((S Φ : Subgroup _) : Set (GL (Fin r) k)) := by
    intro Φ
    have h1 := hop _ Φ.2
    have hc : Continuous (fun g : GL (Fin r) k => (g, (1 : GL (Fin n) k))) :=
      continuous_id.prodMk continuous_const
    exact h1.preimage hc
  have hL : ∀ Φ a, ∀ s ∈ S Φ, ∀ w, b Φ a (σ s w) = b Φ a w := by
    intro Φ a s hs w
    have hs' : om μ s 1 (Φ : Matrix (Fin n) (Fin r) k → ℂ) = Φ := hs
    have := hb_inv s 1 Φ Φ hs'.symm a w
    simpa using this
  have hex : ∀ Φ a, ∃ u : V, ∀ w, b Φ a w = Bf u w := fun Φ a =>
    exists_vector_of_smooth_antilinear k r V σ Bf hadm hsym hpos hinv (b Φ a) (S Φ) (hSo Φ) (hL Φ a)
  choose f hf using hex
  have hadd1 : ∀ Φ Ψ a, f (Φ + Ψ) a = f Φ a + f Ψ a := fun Φ Ψ a =>
    huniq _ _ fun w => by rw [← hf, map_add, LinearMap.add_apply, LinearMap.add_apply, hf, hf, map_add, LinearMap.add_apply]
  have hsmul1 : ∀ (z : ℂ) Φ a, f (z • Φ) a = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  have hadd2 : ∀ Φ a a', f Φ (a + a') = f Φ a + f Φ a' := fun Φ a a' =>
    huniq _ _ fun w => by rw [← hf, map_add, LinearMap.add_apply, hf, hf, map_add, LinearMap.add_apply]
  have hsmul2 : ∀ (z : ℂ) Φ a, f Φ (z • a) = z • f Φ a := fun z Φ a =>
    huniq _ _ fun w => by rw [← hf, map_smul, LinearMap.smul_apply, hf, map_smul, LinearMap.smul_apply]
  let B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V :=
    LinearMap.mk₂ ℂ f hadd1 hsmul1 hadd2 hsmul2
  have hB : ∀ Φ a, B Φ a = f Φ a := fun _ _ => rfl
  refine ⟨B, ?_, ?_⟩
  · intro h0
    apply hb
    ext Φ a w
    rw [hf, ← hB, h0]
    simp
  · intro g h Φ Φ' hΦ F
    rw [hB, hB]
    apply huniq
    intro c
    have hc : σ g (σ g⁻¹ c) = c := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [← hf, ← hc, hb_inv g h Φ Φ' hΦ F, hf, ← hinv g (f Φ F) (σ g⁻¹ c)]

end GlobalTheory.ThetaRiesz
