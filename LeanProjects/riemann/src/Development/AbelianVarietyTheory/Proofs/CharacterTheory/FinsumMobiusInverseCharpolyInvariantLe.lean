import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsiStatement

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_psi_le (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2)
      = s (LinearMap.charpoly (g.restrict hg)) := by
  rw [GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F A s (g.restrict hg)]
  let e : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W} ≃
      {W' : Submodule F A // ∀ x ∈ W', g.restrict hg x ∈ W'} :=
    { toFun := fun W => ⟨W.1.comap A.subtype, fun x hx => by
        simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply] at hx ⊢
        exact W.2.2 _ hx⟩
      invFun := fun W' => ⟨W'.1.map A.subtype, Submodule.map_subtype_le _ _, fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
        exact Submodule.mem_map.2 ⟨_, W'.2 y hy, rfl⟩⟩
      left_inv := fun W => Subtype.ext (by
        change (W.1.comap A.subtype).map A.subtype = W.1
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.2 W.2.1)
      right_inv := fun W' => Subtype.ext (Submodule.comap_map_eq_of_injective A.injective_subtype _) }
  rw [← finsum_comp_equiv e]
  congr 1
  funext W
  have hc : (Submodule.comapSubtypeEquivOfLe W.2.1).conj
      ((g.restrict hg).restrict (e W).2) = g.restrict W.2.2 := by
    ext x
    simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe]
  rw [← hc, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]
  rfl

end GlobalTheory.CuspGL
