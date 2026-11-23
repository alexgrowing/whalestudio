import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open GlobalTheory.Models

namespace GlobalTheory.FiniteTransition

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l l₂ : Level H}

theorem exists_levelMap (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hd : l.Dvd l₂) :
    ∃ (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r),
      r ≫ Xo.s = Xo₂.s ≫ spMap (levelFieldIncl hd.2.2) ∧ LevComp Xo₂.univ Xo.univ r m := by
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o, m₁, h₁, h₁A⟩ := obj_lower_level E H D l l₂ (KA l₂) (baseOfFinerLevel hA) (baseKA l₂) Xo₂.X Xo₂.s Xo₂.univ
    hd (baseOfFinerLevel_rho hA) (baseOfFinerLevel_zeta hA)
  have hred : IsReduced Xo₂.X := by
    have := Xo₂.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo₂.s
      (SmoothOfRelativeDimension.smooth D.dim Xo₂.s)).1
  obtain ⟨r, ⟨hr, ⟨m₂⟩⟩, -⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo (KA l₂) (baseOfFinerLevel hA)
    (levelFieldIncl hA) Xo₂.X Xo₂.s o hred (levelFieldIncl_rho hA) (levelFieldIncl_zeta hA)
  obtain ⟨n, hφ⟩ := LevelCover.sab_comp m₁ m₂.toSABMap (Category.id_comp r)
  refine ⟨r, n, hr, fun a => ?_, fun a => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁ a).trans (Category.id_comp _))).trans (m₂.eta a)))
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁A a).trans (Category.id_comp _))).trans (m₂.etaA a)))

theorem exists_levelMap_coeff {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {c : Coeff l} {c₂ : Coeff l₂} {O O₂ : Type}
    [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c₂.F} (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂)
    (hd : l.Dvd l₂) (hc : c.F ≤ c₂.F) :
    ∃ (r : Xo₂.XF c₂ ⟶ Xo.XF c) (ν : SABMap Y₂.oF.t Y.oF.t r),
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom ∧
        LevComp Y₂.oF Y.oF r ν := by
  obtain ⟨r, m, hr, hm₁, hm₂⟩ := exists_levelMap Xo Xo₂ hd
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp (levelFieldIncl hd.2.2) =
      (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (coe_levelFieldIncl hd.2.2 x)
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc).toRingHom) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  obtain ⟨r', hr₁, hr₂⟩ : ∃ r' : Xo₂.XF c₂ ⟶ Xo.XF c, r' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r ∧
      r' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom :=
    ⟨_, pullback.lift_fst _ _ w, pullback.lift_snd _ _ w⟩
  obtain ⟨ν, hν⟩ := LevelCover.sab_comp Y₂.m0.toSABMap m rfl
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m0.toSABMap ν _ hr₁
  refine ⟨r', ν', hr₂, fun a => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ ?_,
    fun a => LevelCover.sec_cancel ν' Y.m0.toSABMap _ _ ?_⟩
  · rw [hν', hν, ← Category.assoc, LevelCover.sec_pow Y₂.m0.toSABMap _ _ (Y₂.m0.eta a), Category.assoc, hm₁,
      ← Category.assoc, ← hr₁, Category.assoc]
    exact congrArg _ (Y.m0.eta a).symm
  · rw [hν', hν, ← Category.assoc, LevelCover.sec_pow Y₂.m0.toSABMap _ _ (Y₂.m0.etaA a), Category.assoc, hm₂,
      ← Category.assoc, ← hr₁, Category.assoc]
    exact congrArg _ (Y.m0.etaA a).symm

theorem openImmersion_comp_structure_eq_generic {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

end GlobalTheory.FiniteTransition
