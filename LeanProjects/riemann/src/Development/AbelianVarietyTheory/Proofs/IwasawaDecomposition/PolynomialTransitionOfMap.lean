import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open GlobalTheory.Models

namespace GlobalTheory.TorRef

theorem polTransSt_of_polMapSt (hM : PolMapSt) : PolTransSt := by
  intro E _ _ _ H D l l₂ Xo Xo₂ c c₂ Y Y₂ T T₂ φ b _ htw hm hpol hpol₂ hd hb
  have := c.fin
  have := c₂.fin
  have : NumberField c.F := {}
  have : NumberField c₂.F := {}
  have hc : c.F ≤ c₂.F := by
    intro z hz
    obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) (⟨z, hz⟩ : c.F)
    have key : ∀ x : 𝓞 c.F, ((x : c.F) : ℂ) ∈ c₂.F := fun x => hb x ▸ ((b x : 𝓞 c₂.F) : c₂.F).2
    have e : z = ((x : c.F) : ℂ) / ((y : c.F) : ℂ) := (congrArg Subtype.val h).symm
    exact e ▸ div_mem (key x) (key y)
  obtain ⟨r, ν, hr, hl⟩ := GlobalTheory.FiniteTransition.exists_levelMap_coeff T.Z T₂.Z hd hc
  have hbβ : (algebraMap (𝓞 c₂.F) c₂.F).comp b =
      (IntermediateField.inclusion hc).toRingHom.comp (algebraMap (𝓞 c.F) c.F) :=
    RingHom.ext fun x => Subtype.ext (hb x)
  obtain ⟨hβ, -, -⟩ := CoeffRings.coeff_isDedFrac E H l c
  obtain ⟨hβ₂, hft, -⟩ := CoeffRings.coeff_isDedFrac E H l₂ c₂
  have hrs : r ≫ T.Z.j ≫ T.Z.s = T₂.Z.j ≫ T₂.Z.s ≫ spMap b := by
    rw [GlobalTheory.FiniteTransition.openImmersion_comp_structure_eq_generic, reassoc_of% hr, ← Category.assoc T₂.Z.j, GlobalTheory.FiniteTransition.openImmersion_comp_structure_eq_generic,
      Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hbβ]
  rw [← hm] at hpol₂
  obtain ⟨π, hπ, mu, hfin, hj, hφ, hBD⟩ := hM E H D l l₂ Xo Xo₂ c c₂ _ _ _ _ T.Z T₂.Z T.BD T₂.BD φ T₂.m0 b
    (RingEquiv.refl _) r ((TwMap.reflEquiv _ _ _).symm ν) hβ hβ₂ hft htw rfl (hm ▸ hpol) hpol₂ hrs
  have hφ' : T₂.Z.m.φ ≫ (TwMap.reflEquiv _ _ _ mu).φ = ν.φ ≫ T.Z.m.φ := hφ
  refine ⟨hm, π, ⟨pullback.lift π T₂.Z.s hπ, TwMap.reflEquiv _ _ _ mu, r, pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, hfin, hj, fun x => ?_, fun x => ?_⟩, hBD⟩
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ T.Z.m.φ) (hl.1 x)).trans (Category.assoc _ _ _)))
  · exact (congrArg (_ ≫ ·) hφ').trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ T.Z.m.φ) (hl.2 x)).trans (Category.assoc _ _ _)))

end GlobalTheory.TorRef
