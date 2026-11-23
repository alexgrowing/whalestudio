import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem valF_gen {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) (s : Γ(X, U)) :
    ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U ∧
      valF (F := X.functionField) (X.fromSpecStalk (genericPoint X)) U s = fnOf U h s := by
  have h0 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := by
    intro p _
    have hp : X.fromSpecStalk (genericPoint X) p ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hp
    exact hp.mem_open U.isOpen h
  refine ⟨h0, ?_⟩
  have e : (X.fromSpecStalk (genericPoint X)).appLE U ⊤ h0 ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom = X.presheaf.germ U _ h := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h, Category.assoc, Category.assoc, Category.assoc,
      ← Functor.map_comp_assoc]
    have : (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map
        ((homOfLE le_top).op ≫ (homOfLE h0).op) = 𝟙 _ := (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map_id _
    rw [this, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  exact (dif_pos h0).trans (congrArg (fun g => g.hom s) e)

private theorem valAt_fnOf' {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (y : Sp K ⟶ X) {U : X.Opens}
    (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(X, U)) :
    TrueGeo.valAt y (fnOf U (gen_mem hU) a) = valF y U a := by
  have e : X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, Base.valAt_stalk, valF, dif_pos h]
  exact congrArg (fun g => g.hom a) e

theorem UpperTheory.generic_stalk_section_unit :
    ∀ (X X' : Scheme.{0}) [IsIntegral X] (q : X ⟶ X') (V : X'.Opens) (r : Γ(X', V)), (∀ h : genericPoint X ∈ q ⁻¹ᵁ V, valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) V r = fnOf _ h (q.app V r)) ∧ ∀ (k : Type) [Field k] (z : Sp k ⟶ X), ⊤ ≤ (z ≫ q) ⁻¹ᵁ V → IsUnit r → UnitAt (below z) (valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) V r) ∧ TrueGeo.valAt z (valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) V r) = valF (z ≫ q) V r := by
  intro X X' _ q V r
  have e : (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom r = q.app V r := by rw [← Scheme.Hom.app_eq_appLE]
  have h1 : ∀ h : genericPoint X ∈ q ⁻¹ᵁ V,
      valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) V r = fnOf _ h (q.app V r) := by
    intro h
    obtain ⟨h0, h2⟩ := valF_gen (q ⁻¹ᵁ V) h (q.app V r)
    rw [← h2, ← e]
    exact (Pull.valF_appLE (F := X.functionField) q V le_rfl h0 r).symm
  refine ⟨h1, fun k _ z hz hr => ?_⟩
  have hz' : ⊤ ≤ z ⁻¹ᵁ (q ⁻¹ᵁ V) := hz
  have hb : below z ∈ q ⁻¹ᵁ V := hz' trivial
  rw [h1 (gen_mem hb)]
  refine ⟨unitAt_fnOf hb _ (hr.map (q.app V).hom).unit, ?_⟩
  rw [valAt_fnOf' z hb hz', ← e]
  exact Pull.valF_appLE q V le_rfl hz' r
