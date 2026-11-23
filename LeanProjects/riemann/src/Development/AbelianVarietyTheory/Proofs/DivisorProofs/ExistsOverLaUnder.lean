import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.PlaceBelow

theorem exists_overLa_under : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (i : K →+* K') (q : ℕ) (la' : HeightOneSpectrum (𝓞 K')), q.Prime → ((q : ℕ) : 𝓞 K') ∈ la'.asIdeal → ∀ (T : CDVR) (io' : K' →+* T.Fr) (e' : ℕ), OverLa la' T.V io' e' → ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), ((q : ℕ) : 𝓞 K) ∈ la.asIdeal ∧ OverLa la T.V (io'.comp i) e := by
  intro K K' _ _ _ _ i q la' hq hmem T io' e' h
  letI : Algebra K K' := i.toAlgebra

  set la : HeightOneSpectrum (𝓞 K) := la'.under (𝓞 K) with hla
  set r : ℕ := la.asIdeal.ramificationIdx' la'.asIdeal with hr
  have hr0 : r ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la'.asIdeal la.ne_bot
  refine ⟨la, e' * r, ?_, ?_⟩
  ·
    show ((q : ℕ) : 𝓞 K) ∈ la'.asIdeal.under (𝓞 K)
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  · unfold OverLa vLa at h ⊢
    obtain ⟨he', hv⟩ := h
    refine ⟨Nat.mul_pos he' (Nat.pos_of_ne_zero hr0), fun a => ?_⟩

    have key : la.valuation K a ^ r = la'.valuation K' (algebraMap K K' a) :=
      HeightOneSpectrum.valuation_liesOver K' la la' a
    rw [RingHom.comp_apply, hv, show i a = algebraMap K K' a from rfl, ← key, WithZero.log_pow]
    push_cast
    ring

end GlobalTheory.PlaceBelow
