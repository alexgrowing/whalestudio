import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem isChartG_reindex (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left))
    (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (h : IsChartG t x0 d F act tg uvec x) (e : κ' ≃ κ) :
    IsChartG t x0 d F act (fun ℓ => tg (e ℓ)) (fun ℓ => uvec (e ℓ)) x where
  zero := h.zero
  trunc := h.trunc
  law := h.law
  act := h.act
  tan := fun ℓ => h.tan (e ℓ)
  basis := fun v => by
    obtain ⟨b, hb, hbu⟩ := h.basis v
    refine ⟨fun ℓ => b (e ℓ), fun j => ?_, fun a ha => ?_⟩
    · rw [← hb j]
      exact Equiv.sum_comp e (fun ℓ => b ℓ * uvec ℓ j)
    · have h1 : (fun ℓ => a (e.symm ℓ)) = b := hbu _ fun j => by
        rw [← ha j, ← Equiv.sum_comp e (fun ℓ => a (e.symm ℓ) * uvec ℓ j)]
        simp only [Equiv.symm_apply_apply]
      funext ℓ
      rw [← h1]
      simp only [Equiv.symm_apply_apply]

variable {V : Type} [CommRing V] (t : SAB H (Sp V))

theorem combAt_iff {n : ℕ} {x} (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart t.G n x) {m : ℕ}
    (f : Fin m → (Sp (DualNumber V) ⟶ t.G.left)) (hf : ∀ i, f i ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (hft : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t (f i) (hf i))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    IsCombAtG t (𝟙 (Sp V)) f a w ↔ ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw),
      ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ h = ∑ i, a i • ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ (hft i) := by
  constructor
  · intro hc
    have e := prodPts_of_combAt (t := t) f hf a w hw hc
    obtain ⟨h, hh⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    have hT : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw) := by rw [e]; exact h
    exact ⟨hT, (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e hT h).trans hh⟩
  · rintro ⟨h, hh⟩
    apply combAt_of_prodPts (t := t) f hf a w hw
    obtain ⟨h', hh'⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    exact ReciprocityTheory.ChartRestriction.G.Chart.tan_ext hx h h' (hh.trans hh'.symm)

theorem dir_tan {d : ℕ} (xc : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (hz : ∀ m, homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ xc m = 1) (j : Fin d)
    (ho : (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫
      xc 1).left ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t _ ho) := by
  apply chartTan_of
  refine ⟨ho.trans (Category.comp_id _).symm, ?_⟩
  have h1 := congrArg CommaMorphism.left (hz 1)
  simp only [Over.comp_left] at h1 ⊢
  have h2 : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫
      (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V)).left =
      (homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V)).left := by
    show spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg (fun φ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V => φ.toRingHom) (fst_comp_jetTan ((0 : Fin 1), j))
  rw [← Category.assoc, h2, h1]
  have hobj : spMap (algebraMap V V) ≫ 𝟙 (Sp V) = 𝟙 (Sp V) := by
    rw [Category.comp_id]
    first
      | (rw [Algebra.algebraMap_self]; exact Spec.map_id _)
      | simp [spMap]
  have h3 : ∀ (f g : Sp V ⟶ Sp V), f = g →
      (1 : Over.mk f ⟶ t.G).left = (1 : Over.mk g ⟶ t.G).left := by
    rintro f g rfl; rfl
  exact h3 _ _ hobj

end Lemmas

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1
