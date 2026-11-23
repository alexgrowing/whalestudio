import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLocallyNoetherianOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleOpenIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRestrictOpenStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem geomIrr_restrict : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (s : X ⟶ Sp V) (U Xw : X.Opens), Xw ≤ U →
    GeomIrr s Xw → GeomIrr (U.ι ≫ s) (U.ι ⁻¹ᵁ Xw) := by
  intro V _ X s U Xw hle h k _ f hf
  have hr : Set.range ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι) = Set.range Xw.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have : ((U.ι ⁻¹ᵁ Xw : U.toScheme.Opens) : Set U.toScheme) = U.ι ⁻¹' (Xw : Set X) := rfl
    rw [this, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.2 hle
  let e := IsOpenImmersion.isoOfRangeEq ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι) Xw.ι hr
  have he : e.hom ≫ Xw.ι = (U.ι ⁻¹ᵁ Xw).ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h0 := h k f hf
  let m := pullback.map (Xw.ι ≫ s) (spMap f) ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι ≫ s) (spMap f) e.inv (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc _ U.ι s, ← he]; simp) (by simp)
  haveI : IsIso m := by unfold m; infer_instance
  exact Function.Surjective.irreducibleSpace m.homeomorph.continuous m.homeomorph.surjective

theorem range_subset_of_bot_mem {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (g : Sp R ⟶ X) {C : Set X}
    (hC : IsClosed C) (h : g (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ C) : Set.range g ⊆ C := by
  rintro _ ⟨z, rfl⟩
  have h1 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ z := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact (h1.map g.continuous).mem_closed hC h

theorem isTest_comp {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} (U Xw : X.Opens) {yb : Sp 𝓞_ℂ_[p] ⟶ U.toScheme}
    (h : IsTest p (U.ι ⁻¹ᵁ Xw) yb) : IsTest p Xw (yb ≫ U.ι) := by
  obtain ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, e]⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  have := hr ⟨z, rfl⟩
  rw [← Category.assoc]
  exact this

theorem restrictSt : RestrictSt := by
  intro F _ _ V p _ hpV X s Xw hnorm hproj hflat hXw hirr n K hK hchart
  haveI : IsNoetherianRing V := GlobalTheory.ModelNoeth.isNoetherianRing_valuationSubring V
  haveI : IsLocallyNoetherian X := GlobalTheory.ZM.isLocallyNoetherian_of_isQProjOver (by
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, i, inferInstance, inferInstance, e⟩)
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hnorm
  haveI : Flat s := hflat
  have hXi : IsIrreducible (Xw : Set X) := GlobalTheory.T.geometrically_irreducible_open_irreducible F V p hpV X s Xw hXw hirr
  obtain ⟨W, hW, hXwW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hXi
  have hWcl : W ⊆ closure (Xw : Set X) := by
    have h1 := subset_closure_inter_of_isPreirreducible_of_isOpen hW.1.2 Xw.isOpen
      (by rw [Set.inter_eq_right.2 hXwW]; exact hXi.nonempty)
    rwa [Set.inter_eq_right.2 hXwW] at h1
  let Z : irreducibleComponents X := ⟨W, hW⟩
  let U : X.Opens := GlobalTheory.IsNormalScheme.component Z
  have hU : (U : Set X) = W := rfl
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  refine ⟨U.toScheme, U.ι ≫ s, U.ι ⁻¹ᵁ Xw, fun yb => K (yb ≫ U.ι), inferInstance,
    GlobalTheory.IsNormalScheme.pred U.toScheme, ?_, inferInstance, ?_, geomIrr_restrict V X s U Xw hXwW hirr,
    fun yb hyb => hK _ (isTest_comp U Xw hyb), fun x => GlobalTheory.T.chart_restrict_open p n X U Xw K x (hchart _ (hWcl x.2)), ?_⟩
  · obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  · intro x hx
    have h := hXw hx
    have e := Scheme.preimage_basicOpen_top U.ι (p : Γ(X, ⊤))
    rw [map_natCast] at e
    rw [← e]
    exact h
  · intro yb ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩
    have hb : yb (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum 𝓞_ℂ_[p]) ∈ (Xw : Set X) := by
      rw [← bot_map (φ := algebraMap 𝓞_ℂ_[p] ℂ_[p]) (fun a b h => Subtype.ext h) yb]
      exact hr ⟨_, rfl⟩
    have hbT : yT (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ W := by
      rw [← bot_map hk yT, e]; exact hXwW hb
    have r1 : Set.range yb ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact range_subset_of_bot_mem yb hWc (hXwW hb)
    have r2 : Set.range yT ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact range_subset_of_bot_mem yT hWc hbT
    have f1 := IsOpenImmersion.lift_fac U.ι yb r1
    have f2 := IsOpenImmersion.lift_fac U.ι yT r2
    refine ⟨IsOpenImmersion.lift U.ι yb r1, ⟨⟨T, kO, IsOpenImmersion.lift U.ι yT r2, hT, hk, ?_⟩, ?_⟩, ?_⟩
    · rw [← cancel_mono U.ι, Category.assoc, f2, f1, e]
    · rintro _ ⟨z, rfl⟩
      show _ ∈ Xw
      rw [← Scheme.Hom.comp_apply, Category.assoc, f1]
      exact hr ⟨z, rfl⟩
    · simp only [f1]; exact le_rfl

end GlobalTheory.FlatModel
