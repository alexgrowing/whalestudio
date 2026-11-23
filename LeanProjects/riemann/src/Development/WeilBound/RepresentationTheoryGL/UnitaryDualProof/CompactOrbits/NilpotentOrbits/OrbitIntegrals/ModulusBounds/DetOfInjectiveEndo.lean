import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.MemK

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def RatioP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) : Prop :=
  ∀ (V : Submodule k (Matrix (Fin n) (Fin n) k)) (γ : ValueGroupWithZero k), γ ≠ 0 →
    ∀ (φ : V ≃ₗ[k] V) (X Y : AddSubgroup (Matrix (Fin n) (Fin n) k)),
    (∀ y, y ∈ X ↔ y ∈ V ∧ ∀ i j, valuation k (y i j) ≤ γ) →
    (∀ y, y ∈ Y ↔ ∃ x : V, (x : Matrix (Fin n) (Fin n) k) ∈ X ∧ ((φ x : V) : Matrix (Fin n) (Fin n) k) = y) →
    (X ⊓ Y).relIndex X ≠ 0 ∧ (X ⊓ Y).relIndex Y ≠ 0 ∧
      ((X ⊓ Y).relIndex Y : ℝ) / ((X ⊓ Y).relIndex X : ℝ) = (distribHaarChar k (LinearEquiv.det φ) : ℝ)

theorem adL_restrict_inj (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) : Function.Injective ((adL g).restrict hW) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun z : W => g⁻¹.val * (z : Matrix (Fin n) (Fin n) k) * g.val) hab
  simp only [LinearMap.coe_restrict_apply, adL_apply, adL_inv_adL] at h
  exact h

theorem mem_cj_iff_exists (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) (γ : ValueGroupWithZero k) (y : Matrix (Fin n) (Fin n) k) :
    y ∈ cj g (lat W γ) ↔ ∃ z : W, (z : Matrix (Fin n) (Fin n) k) ∈ lat W γ ∧
      ((LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g W hW) z : W) : Matrix (Fin n) (Fin n) k) = y := by
  rw [mem_cj]
  constructor
  · intro h
    refine ⟨⟨_, (mem_lat.1 h).1⟩, h, ?_⟩
    rw [LinearEquiv.coe_ofInjectiveEndo, LinearMap.coe_restrict_apply, adL_apply, adL_adL_inv]
  · rintro ⟨z, hz, rfl⟩
    rw [LinearEquiv.coe_ofInjectiveEndo, LinearMap.coe_restrict_apply, adL_apply, adL_inv_adL]
    exact hz

theorem det_ofInjectiveEndo (g : GL (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (hW : ∀ a ∈ W, adL g a ∈ W) :
    ((LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g W hW)) : kˣ) : k) =
      LinearMap.det ((adL g).restrict hW) := by
  rw [LinearEquiv.coe_det]
  congr 1

theorem comm_of_mem_cS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (u : GL (Fin n) k) (h : u.val - 1 ∈ cS Z x v) : u.val * x = x * u.val := by
  have h2 := h.1.2
  rw [sub_mul, mul_sub, one_mul, mul_one] at h2
  exact sub_left_inj.1 h2

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
