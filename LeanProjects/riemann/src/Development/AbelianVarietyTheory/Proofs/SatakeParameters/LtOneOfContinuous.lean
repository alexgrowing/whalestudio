import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Filter Topology Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneLift

section Val

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem tendsto_pow {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (s : v.adicCompletion K →+* w.adicCompletion M) (hs : Continuous s) {z : v.adicCompletion K}
    (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion M | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion M) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  have hN' : Valued.v (s z ^ N) < 1 := hN
  rw [map_pow] at hN'
  exact absurd hN' (not_lt.2 (one_le_pow₀ hc))

theorem mem_iff_lt_one (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ v.asIdeal ↔ Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have h : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) = v.valuation K (algebraMap (𝓞 K) K x) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem over_of_continuous (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K →+* w.adicCompletion M) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (e x)) : Over e v w := by
  have h1 : v.asIdeal ≤ (src e w).asIdeal := by
    intro x hx
    rw [ringEquivPlaceCorrespondence_placeUnder e w x, mem_iff_lt_one]
    rw [mem_iff_lt_one] at hx
    have := lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  have h2 : v = src e w := HeightOneSpectrum.ext (v.isMaximal.eq_of_le (src e w).isPrime.ne_top h1)
  rw [h2]
  exact ringEquivPlaceCorrespondence_placeUnder e w

theorem normV_eq_absNorm (v : HeightOneSpectrum (𝓞 K)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem two_le_normV (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  rw [normV_eq_absNorm]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

end Val

end GlobalTheory.DegOneLift

namespace GlobalTheory.DegOneLift

section Rep

variable {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M]
  {a : ℕ}

theorem pull_pull (e : K ≃+* M) (φ : Sm K a) : pull a e (pull a e.symm φ) = φ :=
  Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e g)

theorem pullSub_pullSub (e : K ≃+* M) (π : CuspSub K a) : pullSub e (pullSub e.symm π) = π := by
  refine CuspSub.ext ?_
  change (π.V.map (pull a e.symm).toLinearMap).map (pull a e).toLinearMap = π.V
  rw [← Submodule.map_comp]
  convert Submodule.map_id π.V
  refine LinearMap.ext fun φ => ?_
  exact pull_pull e φ

def SmIrr.comap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (σ : SmIrr H)
    (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp f
  smooth x := (σ.smooth x).preimage hf
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => ?_⟩
    obtain ⟨g, rfl⟩ := hs g
    exact hW g x hx

theorem locRep_pullSub (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (hO : Over e v w)
    (π : CuspSub K a) (g : GL (Fin a) (v.adicCompletion K)) (x : π.V) :
    (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) ((pull a e.symm).submoduleMap π.V x) =
      (pull a e.symm).submoduleMap π.V (π.locRep v g x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (pull_act e.symm (.fin (locGL K a v g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e) (locGL K a v g))) (pull a e.symm x.1)
  rw [cFin_locGL hO]
  rfl

end Rep

theorem isLift : ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ) (π : CuspSub K a), ∃ P : CuspSub M a, GlobalTheory.GalCut.IsLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a π
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  refine ⟨pullSub e.symm π, ?_, ?_, ?_⟩
  · intro w f B hf hB
    have hO : Over e.symm w (w.under (𝓞 K)) := fun x => by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
      have : algebraMap (𝓞 K) (𝓞 M) (RingOfIntegers.mapRingEquiv e.symm x) = x := by
        apply RingOfIntegers.ext
        change algebraMap K M (e.symm (x : M)) = x
        rw [← he]
        exact e.apply_symm_apply _
      rw [this]
    have hq : normV w = normV (w.under (𝓞 K)) := by
      rw [normV_eq_absNorm, normV_eq_absNorm]
      exact (qV_eq hO).symm
    have h2 := two_le_normV (w.under (𝓞 K))
    have hf1 : f = 1 := Nat.pow_right_injective h2 (by
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ 1
      rw [pow_one, ← hf, hq])
    subst hf1
    simp only [pow_one, Multiset.map_id']
    exact hasSat_pullSub e.symm hO hB
  · intro τ
    have hτ : (τ.comp e.toRingHom).comp e.symm.toRingHom = τ := by
      ext x
      simp
    have key : ∀ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m ↔
        (CG.mk (pullSub e.symm π)).HasInfChar τ m := by
      intro m
      constructor
      · intro h
        exact hasInfChar_pullSub e.symm (π := π) (σ := τ) h
      · intro h
        have h3 : (pullSub e (pullSub e.symm π)).HasInfChar (τ.comp e.toRingHom) m :=
          hasInfChar_pullSub e (σ := τ.comp e.toRingHom) (by rw [hτ]; exact h)
        rw [pullSub_pullSub] at h3
        exact h3
    by_cases h : ∃ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m
    · obtain ⟨m, hm⟩ := h
      rw [((key m).1 hm).infChar_eq, hm.infChar_eq]
    · have h' : ¬ ∃ m, (CG.mk (pullSub e.symm π)).HasInfChar τ m := fun ⟨m, hm⟩ => h ⟨m, (key m).2 hm⟩
      unfold CG.infChar
      rw [dif_neg h, dif_neg h']
  · intro v w i hi hie σ σ' hσ hσ'
    have hO : Over e v w := over_of_continuous e i.toRingHom hi fun x => hie x
    have hiL : ∀ y, i y = cLoc hO y := fun y => congrFun
      ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer hi (continuous_cLoc hO)
        (funext fun x => (hie x).trans (cLoc_algebraMap hO x).symm)) y
    have hsurj : Function.Surjective (GeneralLinearGroup.map (n := Fin a) (cLoc hO)) := fun g =>
      ⟨GeneralLinearGroup.map (locEquiv hO).symm.toRingHom g, Units.ext (Matrix.ext fun _ _ =>
        (locEquiv hO).apply_symm_apply _)⟩
    let σ'' := SmIrr.comap σ' (GeneralLinearGroup.map (n := Fin a) (cLoc hO))
      (continuous_mapGL _ (continuous_cLoc hO)) hsurj
    let T := (pull a e.symm).submoduleMap π.V
    have h'' : π.IsLocComp v σ'' := by
      obtain ⟨f, h0, hf⟩ := hσ'
      refine ⟨T.symm.toLinearMap ∘ₗ f, fun hz => h0 (LinearMap.ext fun x => T.symm.injective ?_), fun g x => ?_⟩
      · exact (LinearMap.congr_fun hz x).trans (map_zero T.symm).symm
      · have e1 := hf (GeneralLinearGroup.map (cLoc hO) g) x
        have e2 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (T (T.symm (f x))) =
            T (π.locRep v g (T.symm (f x))) := locRep_pullSub e hO π g (T.symm (f x))
        have e3 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (f x) =
            T (π.locRep v g (T.symm (f x))) := by
          refine Eq.trans ?_ e2
          exact congrArg _ (T.apply_symm_apply (f x)).symm
        exact (congrArg T.symm (e1.trans e3)).trans (T.symm_apply_apply _)
    obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v σ σ'' hσ h''
    refine ⟨E.toLinearEquiv, fun g x => ?_⟩
    have hg : GeneralLinearGroup.map i.toRingHom g = GeneralLinearGroup.map (cLoc hO) g :=
      Units.ext (Matrix.ext fun _ _ => hiL _)
    rw [hg]
    exact LinearMap.congr_fun (E.isIntertwining' g) x

end GlobalTheory.DegOneLift
