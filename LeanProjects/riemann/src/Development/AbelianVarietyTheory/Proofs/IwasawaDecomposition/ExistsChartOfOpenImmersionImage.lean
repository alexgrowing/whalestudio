import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsPushforwardOpenImmersionStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

namespace GlobalTheory.ChartTransport

theorem image_fromSpec : ∀ {X X' : Scheme.{0}} (v : X' ⟶ X) [IsOpenImmersion v] (U' : X'.Opens) (hU' : IsAffineOpen U'), ∃ e : Γ(X, v ''ᵁ U') ≃+* Γ(X', U'), (hU'.image_of_isOpenImmersion v).fromSpec = spMap e.symm.toRingHom ≫ hU'.fromSpec ≫ v := by
  intro X X' v _ U' hU'
  have hW := hU'.image_of_isOpenImmersion v
  have hle : U' ≤ v ⁻¹ᵁ (v ''ᵁ U') := by
    rw [Scheme.Hom.preimage_image_eq]
  let e : Γ(X, v ''ᵁ U') ≃+* Γ(X', U') := (v.appIso U').commRingCatIsoToRingEquiv
  have he : CommRingCat.ofHom e.toRingHom = v.appLE (v ''ᵁ U') U' hle := by
    change CommRingCat.ofHom (v.appIso U').hom.hom = _
    rw [CommRingCat.ofHom_hom, Scheme.Hom.appIso_hom, Scheme.Hom.appLE]
    rfl
  refine ⟨e, ?_⟩
  have key := IsAffineOpen.SpecMap_appLE_fromSpec v hW hU' hle
  rw [← key, ← he, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simp only [RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id]
  erw [Spec.map_id, Category.id_comp]

theorem sab_cast_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (h : f = g) (m : SABMap t' t f) :
    (h ▸ m : SABMap t' t g).φ = m.φ := by
  subst h; rfl

theorem exists_chart_image : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), IsOpenImmersion v → Nonempty (SABMap Y'.t Y.t v) → ∀ (M' : MChart Y') (y : Y'.X), y ∈ M'.U → ∃ M : MChart Y, v y ∈ M.U := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' v hv ⟨n⟩ M' y hy
  obtain ⟨e, he⟩ := image_fromSpec v M'.U M'.hU
  obtain ⟨θ, hθ, hne⟩ := GlobalTheory.T.sections_pushforward_open_immersion Y.t Y'.t v n M'.U M'.θ M'.θ_mem
  have hsq : n.φ ≫ Y.t.G.hom = Y'.t.G.hom ≫ v := n.cart.1.w
  haveI : IsDomain Γ(Y'.X, M'.U) := M'.dom
  have hne' : ∀ z ∈ v ''ᵁ M'.U, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = z ∧ g ∈ Y.t.G.left.basicOpen (θ i) := by
    rintro _ ⟨y', hy', rfl⟩
    obtain ⟨g, j, hg, hgj⟩ := M'.θ_ne y' hy'
    obtain ⟨i, hi⟩ := hne g j hgj
    refine ⟨n.φ.base g, i, ?_, hi⟩
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hg]
    rfl
  have hlie : ∀ (R' : Type) [CommRing R'] (f : Γ(Y.X, v ''ᵁ M'.U) →+* R') (t' : SAB H (Sp R'))
      (m : SABMap t' Y.t (spMap f ≫ (M'.hU.image_of_isOpenImmersion v).fromSpec)), ∃ v' : Fin M'.n → (epsR R' ⟶ t'.G),
      (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR e.symm.toRingHom) ≫ M'.v₀ j ≫ n.φ)) ∧ IsLieBasis v' ∧
        ∀ a j, IsLieComb (fun i => f (((M'.ρ a).map e.symm) i j)) v' (v' j ≫ t'.act.act a) := by
    intro R' _ f t' m
    have key : spMap f ≫ (M'.hU.image_of_isOpenImmersion v).fromSpec = (spMap (f.comp e.symm.toRingHom) ≫ M'.hU.fromSpec) ≫ v := by
      rw [he]
      simp only [Category.assoc]
      rw [← Category.assoc (spMap f), ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel n (key ▸ m)
    rw [sab_cast_φ] at hm'
    obtain ⟨v', h1, h2, h3⟩ := M'.lie R' (f.comp e.symm.toRingHom) t' m'
    refine ⟨v', fun j => ?_, h2, fun a j => h3 a j⟩
    rw [hm', ← Category.assoc, h1, Category.assoc, ← Category.assoc (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f))]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  let M : MChart Y :=
    { U := v ''ᵁ M'.U
      hU := M'.hU.image_of_isOpenImmersion v
      dom := Function.Injective.isDomain e.toRingHom e.injective
      θ := θ
      θ_mem := hθ
      θ_ne := hne'
      n := M'.n
      v₀ := fun j => spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR e.symm.toRingHom) ≫ M'.v₀ j ≫ n.φ
      ρ := fun a => (M'.ρ a).map e.symm
      lie := hlie }
  exact ⟨M, ⟨y, hy, rfl⟩⟩

end GlobalTheory.ChartTransport
