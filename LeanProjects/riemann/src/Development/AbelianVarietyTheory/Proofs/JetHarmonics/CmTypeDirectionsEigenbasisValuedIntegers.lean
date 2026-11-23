import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsIsEigenBasisStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsEigenBasisMapFlatBaseChangeStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth.EigExt

theorem res_surjective_of_extends {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) {d s : ℕ}
    (u : Fin s → Fin d → R) (w : Fin d → Fin d → R) (emb : Fin s ↪ Fin d) (hw : ∀ i, w (emb i) = u i)
    (hb : ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j) :
    Function.Surjective (res (fun i j => ι (u i j))) := by
  classical
  have h1 : IsUnit (Matrix.of w) := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    obtain ⟨a, ha, -⟩ := hb v
    exact ⟨a, funext fun j => ha j⟩
  have h2 : IsUnit (ι.mapMatrix (Matrix.of w)) := h1.map _
  rw [← Matrix.mulVec_surjective_iff_isUnit] at h2
  intro g
  obtain ⟨f, hf⟩ := h2 (Function.extend emb g 0)
  refine ⟨f, funext fun i => ?_⟩
  have h3 := congrFun hf (emb i)
  rw [emb.injective.extend_apply] at h3
  rw [← h3]
  show ∑ j, ι (u i j) * f j = ∑ j, ι (w (emb i) j) * f j
  rw [hw]

theorem ι_injective {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) : Function.Injective X.ι := by
  intro a b h
  apply IsFractionRing.injective T.V T.Fr
  apply X.ιF.injective
  rw [X.comp, X.comp, h]

theorem flat {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) :
    letI := X.ι.toAlgebra; Module.Flat T.V X.O := by
  letI := X.ι.toAlgebra
  haveI : IsDomain X.O := Function.Injective.isDomain (algebraMap X.O X.C) X.ints.hom_inj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : X.ι a * x = 0 := hx
  have ha' : X.ι a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (ι_injective X (h.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hx').resolve_left ha'

theorem linPart_add {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (Ch : IntegralChartA3 Xo c T io y) (a b : 𝓞 E) :
    linPart (Ch.actT (a + b)) = linPart (Ch.actT a) + linPart (Ch.actT b) := by
  letI := io.toAlgebra
  have key : ∀ a i j, ReciprocityTheory.ChartRestriction.G.TB.dAct T.Fr Ch.ch.B a i j = algebraMap T.V T.Fr (linPart (Ch.actT a) i j) := by
    intro a i j
    show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.A.act a i)) = _
    rw [MvPowerSeries.coeff_map, Ch.gen.1.2.1 a i, MvPowerSeries.coeff_map]
    rfl
  ext i j
  apply IsFractionRing.injective T.V T.Fr
  rw [Matrix.add_apply, map_add, ← key, ← key, ← key, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, Matrix.add_apply]

end GlobalTheory.CharDepth.EigExt

open GlobalTheory.CharDepth.EigExt in

theorem GlobalTheory.CharDepth.isEigBasis_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → ∀ τ : E →+* ℂ, IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) ∧ Function.Surjective (res (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X τO hτ τ
  constructor
  · obtain ⟨τT, hT, hT', -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
    have he : τO τ = X.ι.comp (τT τ) := by
      ext a
      apply X.ints.hom_inj
      rw [hτ τ a]
      exact (hT' τ a).symm
    letI := X.ι.toAlgebra
    haveI := flat X
    rw [he]
    exact GlobalTheory.T.isEigenBasis_map_flat_baseChange T.V X.O (𝓞 E) _ _ Ch.actT (linPart_add Ch) (τT τ) _
      (GlobalTheory.T.integral_chart_directions_isEigenBasis E H Dw l Xo c T io y Ch τ (τT τ) (hT τ))
  · obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
    exact res_surjective_of_extends X.ι _ w emb hw hb
