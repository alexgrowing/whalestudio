import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagQ

theorem eq_genericPoint_of_krullDim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) (x : X) :
    x = genericPoint X := by
  by_contra hx
  have hlt : (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ : TopologicalSpace.IrreducibleCloseds X) <
      ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    refine lt_of_le_of_ne ?_ ?_
    · exact (specializes_iff_closure_subset.1 (genericPoint_specializes x))
    · intro he
      have : closure ({x} : Set X) = closure {genericPoint X} := congrArg TopologicalSpace.IrreducibleCloseds.carrier he
      exact hx ((specializes_iff_closure_subset.2 this.ge).antisymm (genericPoint_specializes x)).eq
  have : (0 : WithBot ℕ∞) < topologicalKrullDim X := Order.krullDim_pos_iff.2 ⟨_, _, hlt⟩
  rw [h] at this
  exact lt_irrefl _ this

theorem toPt_comp_str (Y : GlobalTheory.ProjVar.Var ℚ) : toPt Y ≫ (GlobalTheory.ProjVar.proj ℚ 0).str = Y.str := by
  have e : @inv _ _ _ _ (GlobalTheory.ProjVar.proj ℚ 0).ι (GlobalTheory.ProjVar.isIso_proj_ι ℚ 0) ≫ (GlobalTheory.ProjVar.proj ℚ 0).str =
      PSpace.str ℚ 0 := by
    haveI := GlobalTheory.ProjVar.isIso_proj_ι ℚ 0
    exact IsIso.inv_hom_id_assoc (GlobalTheory.ProjVar.proj ℚ 0).ι (PSpace.str ℚ 0)
  rw [toPt, Category.assoc, Category.assoc]
  erw [e]
  rw [ptQ, GlobalTheory.ProjSpace.pt_str, show spMap (RingHom.id ℚ) = 𝟙 _ from Spec.map_id _, Category.comp_id]

theorem exists_isHom_toPt : ∀ (Y : GlobalTheory.ProjVar.Var ℚ), ∃ φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →ₐ[ℚ] Y.Fn,
    (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).IsHom (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) := by
  intro Y
  refine GlobalTheory.FlagBundle.exists_isHom_of_generic (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)) (GlobalTheory.FlagBundle.ratOf Y) (toPt Y) (toPt_comp_str Y) ?_
  refine eq_genericPoint_of_krullDim_zero ?_ _
  exact (GlobalTheory.ProjVar.Var.topologicalKrullDim_eq _).trans (by rw [GlobalTheory.ProjVar.proj_dim]; rfl)

end GlobalTheory.FlagQ
