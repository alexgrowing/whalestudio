import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ExistsG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ExistsV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.WCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.CoverComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.InjField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.OntoField

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.pBEx : UpperTheory.Gal.KunnethLefschetz.G.PBEx := by
  intro K _ W Z Y T q i π D d hB j r hsq
  obtain ⟨B⟩ := hB
  obtain ⟨g, gn, gc, gs⟩ := existsG B
  obtain ⟨v, hv, hu⟩ := existsV B j
  obtain ⟨sc, uc⟩ := wCover B
  obtain ⟨se, ue⟩ := tCover B j r hsq
  obtain ⟨cm, ct⟩ := coverComm B j r hsq.w
  have hτ : ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j), a ≫ eP B j = b ≫ eP B j →
      (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f := fun a b h => by
    rw [Category.assoc, Category.assoc, ct, reassoc_of% h]
  have hone : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (e : a = b) (h : a ≫ cP B = b ≫ cP B), g a b h = 1 := by
    intro V a b e h
    subst e
    have := gc a a a h h
    exact mul_eq_left.1 this
  let P : PBData r d :=
    { W' := WP B
      c := cP B
      g := g
      g_nat := gn
      g_coc := gc
      T' := TP B j
      e := eP B j
      ρ := rhoP B j r hsq.w
      comm := cm
      v := fun a => ⟨a.appTop.hom ∘ v, by
        rw [Set.range_comp, ← Ideal.map_span, hu, Ideal.map_top]⟩
      v_nat := fun s a => by
        funext m
        simp only [Function.comp_apply, Scheme.Hom.comp_appTop]
        rfl
      w := fun a b h => (D.u _ _ (hτ a b h))⁻¹
      gv := fun a b h h' => gvField B j r hsq v hv a b h (hτ a b h) _ (gs _ _ h')
      inj := fun a b h' u hh => injField B j r hsq v hv a b _ h' (gs _ _ h') u hh
      onto := fun a₀ v₀ x => by
        obtain ⟨U, a, u, hx, ha, hv'⟩ := ontoField B j r hsq v hv a₀ v₀ x
        have h : (a ≫ rhoP B j r hsq.w) ≫ cP B = (U.ι ≫ a₀) ≫ cP B := by rw [ha]
        refine ⟨U, a, h, u, hx, ?_⟩
        rw [hone _ _ ha h]
        simpa using hv' }
  exact ⟨P, tauP B j, ct, fun a b h h' => rfl⟩
