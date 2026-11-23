import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.FlagQ

theorem eq_genericPoint_of_dim_zero {F : Type} [Field F] (B : GlobalTheory.ProjVar.Var F) (h : B.dim = 0) (z : B.X) :
    z = genericPoint B.X := by
  have hd : Order.krullDim (TopologicalSpace.IrreducibleCloseds B.X) ≤ 0 := by
    have := B.topologicalKrullDim_eq
    rw [h] at this
    exact this.le
  have hm := Order.krullDim_nonpos_iff_forall_isMax.1 hd
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hle := hm (b := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩) (Set.subset_univ _)
  have hz : IsGenericPoint z (Set.univ : Set B.X) := Set.eq_univ_of_univ_subset hle
  exact hz.eq (genericPoint_spec B.X)

theorem keepsRad_toPt : ∀ (Y : GlobalTheory.ProjVar.Var ℚ) (φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →ₐ[ℚ] Y.Fn), (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).IsHom (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) → GlobalTheory.FlagBundle.KeepsRad (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)) (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) := by
  intro Y φ h z g hg
  have hall (x : (GlobalTheory.ProjVar.proj ℚ 0).Fn) :
      x ∈ (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).O (GlobalTheory.FlagQ.toPt Y z) := by
    have e : GlobalTheory.FlagQ.toPt Y z = genericPoint (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).Z :=
      eq_genericPoint_of_dim_zero (GlobalTheory.ProjVar.proj ℚ 0) rfl _
    have e' := (congrArg (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).O e).trans
      (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).O_genericPoint
    exact e'.ge trivial
  refine ⟨(map_ne_zero φ).2 hg.1, h.map_mem_O (hall g), fun x n hx _ => ?_⟩
  rw [div_eq_mul_inv, ← map_inv₀]
  exact mul_mem hx (h.map_mem_O (hall g⁻¹))

end GlobalTheory.FlagQ
