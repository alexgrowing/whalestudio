import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompProdOfFn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertSpan

theorem exists_coeffs_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
  intro E _ _ _ H X t U n v hv hb S _ φ g₀ w hg hred hw
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', ← Spec.map_id]
    congr 1
  let g' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  let w' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G := Over.homMk w hw
  let s : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ _ ≫ _ = g₀ ≫ t.G.hom
      rw [← Category.assoc, e, Category.id_comp])
  have hs : s ≫ g' = s ≫ w' := by
    refine Over.OverMorphism.ext ?_
    change spMap _ ≫ spMap _ ≫ g₀ = spMap _ ≫ w
    rw [hred, ← Category.assoc, e, Category.id_comp]
  have hτ : IsTanAtG t (g₀ ≫ t.G.hom) (g'⁻¹ * w').left := by
    refine ⟨Over.w (g'⁻¹ * w'), ?_⟩
    change (s ≫ (g'⁻¹ * w')).left = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, hs, inv_mul_cancel]
  have hbas := (GlobalTheory.LineNorm.isTanBasis_of_basis E H X t _ (chart U) n v hv hb).2 S φ (g'⁻¹ * w').left
  rw [← hg] at hbas
  obtain ⟨c, ⟨u, hu, hux⟩, -⟩ := hbas hτ
  have hwu : w' = g' * (List.ofFn u).prod := by
    rw [show (List.ofFn u).prod = g'⁻¹ * w' from Over.OverMorphism.ext hux, mul_inv_cancel_left]
  refine ⟨c, fun S' _ ρ φ' wt hg' hwt O hO f => ?_⟩
  have h₃ : (spMap ρ ≫ g₀) ≫ t.G.hom = spMap (ρ.comp φ) ≫ chart U := by
    rw [Category.assoc, hg, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
  have hU : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    change ⊤ ≤ ((spMap ρ ≫ g₀) ≫ t.G.hom) ⁻¹ᵁ U.1
    rw [hg']
    exact GlobalTheory.Points.le_preimage_specMap_fromSpec U.2 (CommRingCat.ofHom φ')
  obtain rfl : φ' = ρ.comp φ := RingHom.ext fun r =>
    (GlobalTheory.LogKSLin.valR_base U le_rfl hg' hU r).symm.trans (GlobalTheory.LogKSLin.valR_base U le_rfl h₃ hU r)
  choose g'' v'' hg'' hv'' hw'' using hwt
  have e' : spMap (dualMap ρ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ρ := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp']
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : tEpsG ((spMap ρ ≫ g₀) ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) := Over.homMk (spMap (dualMap ρ)) (by
    change _ ≫ _ ≫ _ = _ ≫ (_ ≫ _) ≫ _
    rw [← Category.assoc, e']
    simp only [Category.assoc])
  have hkg : (k ≫ g').left = spMap (algebraMap S' (DualNumber S')) ≫ spMap ρ ≫ g₀ := by
    change spMap _ ≫ spMap _ ≫ g₀ = _
    rw [← Category.assoc, e', Category.assoc]
  have hgg : ∀ a, g'' a = k ≫ g' := fun a => Over.OverMorphism.ext ((hg'' a).trans hkg.symm)
  have hy0 : ∀ a, smT ((spMap ρ ≫ g₀) ≫ t.G.hom) 0 (v'' a) = 1 := fun a => by
    have ht := GlobalTheory.LieMet.isTan_map (ρ.comp φ) h₃.symm (hv a)
    rw [show v'' a = ovT ht from Over.OverMorphism.ext (hv'' a)]
    exact smT_zero_ovT ht
  have hku : ∀ a, k ≫ u a = smT ((spMap ρ ≫ g₀) ≫ t.G.hom) (ρ (c a)) (v'' a) := fun a => by
    refine Over.OverMorphism.ext ?_
    change spMap (dualMap ρ) ≫ (u a).left = spMap (epsMul (ρ (c a))) ≫ (v'' a).left
    rw [hu a, hv'' a]
    simp only [← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap]
    congr 2
    refine RingHom.ext fun z => ?_
    ext <;> simp [epsMul, dualMap]
  have hmain : spMap (dualMap ρ) ≫ w = ((k ≫ g') * (List.ofFn fun a =>
      smT ((spMap ρ ≫ g₀) ≫ t.G.hom) (ρ (c a)) (v'' a)).prod).left := by
    change (k ≫ w').left = _
    rw [hwu, MonObj.comp_mul, GlobalTheory.FirstOrderValue.comp_prod_ofFn]
    simp only [hku]
  rw [hmain]
  refine (GlobalTheory.KSLin.snd_valR_translate_prod _ t.G (spMap ρ ≫ g₀) (k ≫ g') hkg v'' (fun a => ρ (c a)) hy0 O f
    hO).trans (Finset.sum_congr rfl fun a _ => ?_)
  rw [← hw'' a, hgg a]

end GlobalTheory.VertSpan
