import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.Poinc

theorem mem_map_idealSheaf_of_forall_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), (∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → valF M₁.pt V.1 g / f' ∈ M.O x') → g ∈ (D.idealSheaf.map π).ideal V := by
  intro o Ω _ _ _ M₁ M π hπ hprop D V g hg
  haveI : QuasiCompact π := inferInstance
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker]
  change (D.idealSheaf.subschemeι.app (π ⁻¹ᵁ V.1)).hom ((π.app V.1).hom g) = 0
  rw [GlobalTheory.Cartier.app_subschemeι_eq_zero_iff]
  intro W hW
  show _ ∈ (EffCartierData.locIdeal D.U D.f D.exists_mem D.associated_germ).ideal W
  rw [EffCartierData.mem_locIdeal_iff]
  intro i x hx hi
  have hxV : x ∈ π ⁻¹ᵁ V.1 := hW hx
  have hV : (V.1 : Set M₁.Z).Nonempty := ⟨π x, hxV⟩
  rw [GlobalTheory.Cartier.germ_resG]
  have hval : valF M.pt (π ⁻¹ᵁ V.1) ((π.app V.1).hom g) = valF M₁.pt V.1 g := hπ.valF_app hV g
  have hq := hg x hxV _ ⟨i, hi, rfl⟩
  have hne : valF M.pt (D.U i) (D.f i) ≠ 0 := by
    intro h0
    have hnz := GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) x hi
    have : (M.Z.presheaf.germ (D.U i) x hi).hom (D.f i) = 0 := by
      apply M.stalkHom_injective x
      rw [map_zero]
      exact (RatModel.stalkHom_germ hi (D.f i)).trans h0
    rw [this] at hnz
    exact zero_notMem_nonZeroDivisors hnz
  rw [← map_dvd_iff (M.stalkEquiv x)]
  have e1 := RatModel.stalkEquiv_germ hi (D.f i)
  have e2 := RatModel.stalkEquiv_germ hxV ((π.app V.1).hom g)
  refine ⟨⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  change (M.stalkEquiv x ((M.Z.presheaf.germ _ x hxV) ((π.app V.1).hom g)) : Ω) =
    (M.stalkEquiv x ((M.Z.presheaf.germ _ x hi) (D.f i)) : Ω) * (valF M₁.pt V.1 g / valF M.pt (D.U i) (D.f i))
  rw [e1, e2]
  simp only
  rw [hval, mul_div_cancel₀ _ hne]

end GlobalTheory.Poinc
