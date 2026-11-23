import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrFin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.UpperBoundDescent

theorem desc : ∀ (p : ℕ) [Fact p.Prime] (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ¬ IsUnit (p : T.V) → ∀ (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ) (FT : Fin dd → PS T.V 2 dd) (actT : OE → Fin dd → PS T.V 1 dd), UpFBr.UpFLaw p T'.V OE dd (fun i => MvPowerSeries.map φ (FT i)) (fun a i => MvPowerSeries.map φ (actT a i)) → UpFBr.UpFLaw p T.V OE dd FT actT := by
  intro p _ T T' φ hφ hfin hp OE _ _ dd FT actT h C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hb hf r W hW j
  have hinj : Function.Injective ((algebraMap O C).comp iota) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hp0 : (p : T.V) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    obtain ⟨m, u', hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
    have h1 : ((algebraMap O C).comp iota) ϖ = 0 := by
      rw [map_mul, map_pow, mul_eq_zero] at ha
      rcases ha with ha | ha
      · exact absurd ha (u.isUnit.map _).ne_zero
      · exact pow_eq_zero_iff'.1 ha |>.1
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp (by rw [hm]; simp)
    have h2 := congrArg ((algebraMap O C).comp iota) hm
    rw [map_natCast, map_mul, map_pow, h1, zero_pow hm0, mul_zero] at h2
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨ι', hl, hc⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ hφ hfin.to_isIntegral iota hinj
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map iota f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hc, RingHom.comp_apply]
  have := h C v O hv ι' hl w t hb hf r W (by simpa only [key] using hW) j
  simpa only [key] using this

end GlobalTheory.UpperBoundDescent
