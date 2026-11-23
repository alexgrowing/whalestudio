import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

theorem isAbelianScheme_of_proper (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) [IsProper G.hom] :
    IsAbelianScheme G :=
  ⟨hG.comm, hG.smooth, inferInstance, hG.geomConnected⟩

theorem isAbelianScheme_tensor (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsAbelianScheme G)
    (hH : IsAbelianScheme H) : IsAbelianScheme (G ⊗ H) := by
  have := hG.comm
  have := hH.comm
  have := hG.smooth
  have := hH.smooth
  have := hG.proper
  have := hH.proper
  have := hG.geomConnected
  have := hH.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, pullback.condition]
    exact GeometricallyConnected.comp _ _

theorem isAbelianScheme_tensor_unit (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    IsAbelianScheme (G ⊗ 𝟙_ (Over S)) := by
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hc : (G ⊗ 𝟙_ (Over S)).hom = pullback.snd G.hom (𝟙_ (Over S)).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    exact Category.comp_id _
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [hc]; infer_instance
  · rw [hc]; infer_instance
  · rw [hc]; infer_instance

theorem isAbelianScheme_powObj (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    ∀ n : ℕ, IsAbelianScheme (powObj G (n + 1))
  | 0 => isAbelianScheme_tensor_unit G hG
  | n + 1 => isAbelianScheme_tensor G (powObj G (n + 1)) hG (isAbelianScheme_powObj G hG n)

theorem globalFns_powObj (hGF : GlobalFnsSt) (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    [IsProper G.hom] (n : ℕ) : Function.Bijective (powObj G n).hom.appTop.hom := by
  cases n with
  | zero =>
    show Function.Bijective (𝟙 S : S ⟶ S).appTop.hom
    simp only [Scheme.Hom.id_appTop, CommRingCat.hom_id]
    exact Function.bijective_id
  | succ n => exact hGF _ _ (isAbelianScheme_powObj G (isAbelianScheme_of_proper G hG) n)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
