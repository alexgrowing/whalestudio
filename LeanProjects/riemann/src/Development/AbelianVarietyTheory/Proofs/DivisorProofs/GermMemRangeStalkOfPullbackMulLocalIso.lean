import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory

theorem germToFunctionField_mem_range_stalk_of_mul_pull : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  intro k _ Y X _ _ p σ U _ _ L P N C J g s hrel x hbij hJ i hi _
  obtain ⟨t, ha, hb, hc⟩ := C.cover x
  have hjx : σ x ∈ L.U (C.b t PUnit.unit) := mem_pull.1 hb
  have hξx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hne : Nonempty (σ ⁻¹ᵁ U) := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
    obtain ⟨z, -⟩ := (σ ∣_ U).surjective ⟨y, hy⟩
    exact ⟨z⟩
  have hξU : genericPoint X ∈ σ ⁻¹ᵁ U := genericPoint_mem_opens _
  have hσξη : σ (genericPoint X) ⤳ genericPoint Y := by
    obtain ⟨z, hz⟩ := (σ ∣_ U).surjective ⟨genericPoint Y, genericPoint_mem_opens U⟩
    have e : σ z.1 = genericPoint Y := (morphismRestrict_base_coe σ U z).symm.trans (congrArg Subtype.val hz)
    rw [← e]
    exact σ.base.hom.map_specializes ((genericPoint_spec X).specializes trivial)
  have hσξ : σ (genericPoint X) ∈ U ⊓ L.U (C.b t PUnit.unit) :=
    ⟨hξU, (σ.base.hom.map_specializes hξx).mem_open (L.U _).isOpen hjx⟩
  have haξ := hξx.mem_open (P.U (C.a t)).isOpen ha
  have hbξ := hξx.mem_open ((L.pull σ).U (C.b t)).isOpen hb
  have hcξ := hξx.mem_open (N.U (C.c t)).isOpen hc
  have e1 := congrArg (H0.germ (C.c t) (genericPoint X) hξU hcξ) hrel
  rw [C.germ_mul _ _ t _ hξU haξ hbξ hcξ, H0.germ_restr, H0.germ_restr, H0.germ_pull] at e1
  have hsp (B : LB X) (f : H0 (σ ≫ p) B ⊤) (a : B.ι) (hx : x ∈ B.U a) (hξ : genericPoint X ∈ B.U a) :
      H0.germ a (genericPoint X) (memTop _) hξ f =
        X.presheaf.stalkSpecializes hξx (H0.germ a x (memTop x) hx f) := by
    rw [H0.germ_apply, H0.germ_apply]
    exact (X.presheaf.germ_stalkSpecializes_apply _ hξx _).symm
  have hJu := hJ (C.a t) ha
  obtain ⟨h, hh⟩ := hbij.2 (H0.germ (C.c t) x (memTop x) hc g * ↑hJu.unit⁻¹)
  have : Nonempty (L.U (C.b t PUnit.unit)) := ⟨⟨σ x, hjx⟩⟩
  have := nonempty_inf_of_isIntegral U (L.U (C.b t PUnit.unit))
  refine germToFunctionField_mem_range_stalk_of_secOn (LB.coord_mem s) hi hjx ⟨h, ?_⟩
  let φ : Y.functionField →+* X.presheaf.stalk (genericPoint X) :=
    (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.stalkSpecializes hσξη).hom
  refine φ.injective ?_
  have eA : φ (algebraMap _ _ h) = X.presheaf.stalkSpecializes hξx (σ.stalkMap x h) := by
    change (σ.stalkMap _).hom ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Y.presheaf.stalkSpecializes hσξη).hom h) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply σ _ _ hξx h
  have eB : φ (Y.germToFunctionField _ (LB.coord s (C.b t PUnit.unit))) =
      (σ.stalkMap (genericPoint X)).hom (H0.germ (C.b t PUnit.unit) (σ (genericPoint X)) hσξ.1 hσξ.2 s) := by
    change (σ.stalkMap _).hom (Y.presheaf.stalkSpecializes hσξη
      (Y.presheaf.germ _ (genericPoint Y) _ (LB.coord s _))) = _
    rw [Y.presheaf.germ_stalkSpecializes_apply _ hσξη]
    rfl
  rw [eA, eB, hh]
  rw [hsp P J (C.a t) ha haξ, hsp N g (C.c t) hc hcξ] at e1
  have hu : IsUnit (X.presheaf.stalkSpecializes hξx (H0.germ (C.a t) x (memTop x) ha J)) := hJu.map _
  apply hu.mul_left_cancel
  rw [e1, ← map_mul]
  exact congrArg _ (by rw [mul_left_comm, hJu.mul_val_inv, mul_one])

end GlobalTheory
