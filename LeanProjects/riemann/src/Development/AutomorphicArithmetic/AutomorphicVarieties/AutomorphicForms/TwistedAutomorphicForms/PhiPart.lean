import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.SplitIso
import Development.AbelianVarietyTheory.Definitions.Foundations.DiagUnitsEqLocalIdele

open NumberField IsDedekindDomain Neutral.B1 GlobalTheory.Mem.Chr.Model
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap)

private def evAt (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    AdeleRing (𝓞 L) L →* w.adicCompletion L where
  toFun a := a.2 w
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem evAt_continuous (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (evAt L w) :=
  (RestrictedProduct.continuous_eval w).comp continuous_snd

private theorem exists_local (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (h2 : Module.finrank F L = 2) (l : ℕ) (Φ : Set (HeightOneSpectrum (𝓞 L))) (hΦ : UpperTheory.V.Af.Tw.IsType F l Φ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ q : Ideles L →* (v.adicCompletion F)ˣ, Continuous q ∧ (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      (∀ a : Ideles F, (q (ideleMap F L a)).val = a.val.2 v) ∧
      ∀ x : Ideles L, (∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w ∈ Φ → x.val.2 w = 1) → q x = 1) := by
  by_cases hv : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  swap
  · exact ⟨1, continuous_const, fun h => absurd h hv⟩
  have hl : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := fun w hw => by
    rw [← hw] at hv
    have : algebraMap (𝓞 F) (𝓞 L) ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := hv
    rwa [map_natCast] at this
  obtain ⟨w, w', hw, hne, hw', hin⟩ : ∃ w w' : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v ∧ w' ≠ w ∧
      w'.under (𝓞 F) = w.under (𝓞 F) ∧ w ∈ Φ := by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
    let u : HeightOneSpectrum (𝓞 L) := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
    have hu : u.under (𝓞 F) = v := HeightOneSpectrum.ext hP'.over.symm
    obtain ⟨u', h1, h3, h4⟩ := hΦ u (hl u hu)
    by_cases hin : u ∈ Φ
    · exact ⟨u, u', hu, h1, h3, hin⟩
    · exact ⟨u', u, h3.trans hu, h1.symm, h3.symm, by_contra fun h => hin (h4.2 h)⟩
  have hlw := hl w hw
  subst hw
  obtain ⟨r, hr, hr'⟩ := UpperTheory.V.Af.Tw.splitIso F L h2 w w' hne hw'
  refine ⟨Units.map (r.toMonoidHom.comp (evAt L w)), Continuous.units_map _ (hr.comp (evAt_continuous L w)),
    fun _ => ⟨fun a => hr' _, fun x hx => Units.ext ?_⟩⟩
  show r (x.val.2 w) = 1
  rw [hx w hlw hin, map_one]

theorem UpperTheory.V.Af.Tw.phiPart :
    UpperTheory.V.Af.Tw.PhiPart := by
  intro F L _ _ _ _ _ h2 l hl Φ hΦ
  classical
  choose q hq hq' using exists_local F L h2 l Φ hΦ
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 hl
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let p : Ideles L →* Ideles F := ∏ v ∈ hfin.toFinset, (GlobalTheory.Mem.Chr.localIdele F v).comp (q v)
  have hp : ∀ x, p x = ∏ v ∈ hfin.toFinset, GlobalTheory.Mem.Chr.localIdele F v (q v x) := fun x =>
    MonoidHom.finset_prod_apply _ _ x
  have hc : ∀ x u, (p x).val.2 u = ∏ v ∈ hfin.toFinset, (GlobalTheory.Mem.Chr.localIdele F v (q v x)).val.2 u := fun x u => by
    rw [hp]
    exact map_prod ((evAt F u).comp (Units.coeHom _)) _ _
  refine ⟨p, ?_, fun a v hv => ?_, fun x v hv => ?_, fun x hx => ?_⟩
  · rw [show (p : Ideles L → Ideles F) = _ from funext hp]
    exact continuous_finset_prod _ fun v _ => (localIdele_continuous F v).comp (hq v)
  · rw [hc, Finset.prod_eq_single_of_mem v (hfin.mem_toFinset.2 hv)
      fun u _ hu => localIdele_snd_ne F u v hu.symm _, GlobalTheory.Mem.Chr.Model.localIdele_snd_self, (hq' v hv).1]
  · rw [hc]
    refine Finset.prod_eq_one fun u hu => localIdele_snd_ne F u v ?_ _
    rintro rfl
    exact hv (hfin.mem_toFinset.1 hu)
  · rw [hp]
    exact Finset.prod_eq_one fun u hu => by rw [(hq' u (hfin.mem_toFinset.1 hu)).2 x hx, map_one]
