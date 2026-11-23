import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistPdeltaPlaces

theorem isIntegral_of_sq_eq_neg {A : Type} [CommRing A] (x : A) (d : ℕ) (h : x ^ 2 = -(d : A)) :
    IsIntegral ℤ x :=
  ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by simp [h]⟩

theorem exists_nat_sub_mem {E : Type} [Field E] [NumberField E] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    {q : ℕ} (hq : q.Prime) (hc : Nat.card (𝓞 E ⧸ P.asIdeal) = q) (x : 𝓞 E) :
    ∃ n : ℕ, x - (n : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hq.ne_zero)
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  let e : ZMod q ≃+* (𝓞 E ⧸ P.asIdeal) :=
    ZMod.ringEquivOfPrime _ hq (Nat.card_eq_fintype_card.symm.trans hc)
  refine ⟨(e.symm (Ideal.Quotient.mk _ x)).val, ?_⟩
  rw [← Ideal.Quotient.eq, map_natCast]
  have h1 : ((e.symm (Ideal.Quotient.mk P.asIdeal x)).val : ZMod q) = e.symm (Ideal.Quotient.mk _ x) := by
    haveI : Fact q.Prime := ⟨hq⟩
    exact ZMod.natCast_zmod_val _
  have h2 : e (((e.symm (Ideal.Quotient.mk P.asIdeal x)).val : ℕ) : ZMod q) =
      ((e.symm (Ideal.Quotient.mk P.asIdeal x)).val : 𝓞 E ⧸ P.asIdeal) := map_natCast e _
  rw [← h2, h1, RingEquiv.apply_symm_apply]

theorem main : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (μ0 : T), Rl.toLevCh.Is μ0 → ∀ i : D.ntw.Tw, (∀ P ∈ {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i}, ∀ P' ∈ {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i}, Formalism.BasicNotions.IsConjPl D.host P P' → P = P') ∧ (∀ P ∈ {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i}, ∀ P' ∈ {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i}, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ P.asIdeal ∧ (p : 𝓞 D.host.E) ∈ P'.asIdeal) → P.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl μ0 hL i
  set H := D.host
  set p : ℕ := if D.ntw.l i = H.pde then H.pde' else H.pde with hpdef
  have hp : p ∈ ({H.pde, H.pde'} : Set ℕ) := by
    rw [hpdef]; split_ifs <;> simp
  obtain ⟨𝔭, h𝔭⟩ := hL.Q_de p hp
  have hmemp : ∀ P : Pl H.E, P ∈ D.ntw.pD i → ((p : ℕ) : 𝓞 H.E) ∈ P.asIdeal := by
    intro P hP
    have h := (Set.ext_iff.mp (D.ntw.pD_eq i) P).mp (Finset.mem_coe.mpr hP)
    exact h
  have hunder : ∀ P ∈ {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i},
      P.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = 𝔭.asIdeal := by
    rintro P ⟨t, ht, hpi⟩
    have := h𝔭 t P ht (hmemp P hpi)
    rw [← this]
    rfl
  refine ⟨?_, ?_⟩
  · rintro P hP P' hP' hc
    exfalso
    obtain ⟨t, ht, hpi⟩ := hP
    obtain ⟨t', ht', hpi'⟩ := hP'
    have hsq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqrtMinusD_sq
    let s : 𝓞 H.E := ⟨H.sqrtMinusD, isIntegral_of_sq_eq_neg _ H.d hsq⟩
    have hsK : H.sqrtMinusD ∈ H.K := H.toHostRaw.sqd_mem_K
    let sK0 : H.K := ⟨H.sqrtMinusD, hsK⟩
    have hsqK : sK0 ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa using hsq)
    let sK : 𝓞 H.K := ⟨sK0, isIntegral_of_sq_eq_neg _ H.d hsqK⟩
    have hsmap : algebraMap (𝓞 H.K) (𝓞 H.E) sK = s := rfl
    obtain ⟨⟨q, hq, hcard, -, -⟩, -⟩ := hL.Q_pl t P ht
    obtain ⟨n, hn⟩ := exists_nat_sub_mem P hq hcard s
    have hxK : sK - (n : 𝓞 H.K) ∈ P.asIdeal.comap (algebraMap (𝓞 H.K) (𝓞 H.E)) := by
      rw [Ideal.mem_comap, map_sub, map_natCast, hsmap]; exact hn
    rw [hunder P ⟨t, ht, hpi⟩, ← hunder P' ⟨t', ht', hpi'⟩, Ideal.mem_comap, map_sub, map_natCast, hsmap] at hxK
    have hy : -s - (n : 𝓞 H.E) ∈ P'.asIdeal := by
      refine (hc (s - n) (-s - n) ?_).mp hn
      push_cast
      rw [map_sub, map_natCast]
      change -H.sqrtMinusD - _ = H.conj H.sqrtMinusD - _
      rw [H.conj_sqrtMinusD]
    have h2s : (2 : 𝓞 H.E) * s ∈ P'.asIdeal := by
      have := P'.asIdeal.sub_mem hxK hy
      convert this using 1; ring
    have hoff := (hL.Q_off t' P' ht').1
    apply hoff
    rw [Nat.cast_mul]
    refine P'.asIdeal.mul_mem_right _ ?_
    rcases P'.isPrime.mem_or_mem h2s with h2 | hs
    · exact P'.asIdeal.mem_of_dvd (Nat.cast_dvd_cast (α := 𝓞 H.E) H.toHostRaw.two_dvd_condN) (by exact_mod_cast h2)
    · have hss : s * s = -(H.d : 𝓞 H.E) := by
        apply RingOfIntegers.coe_injective
        push_cast
        rw [← pow_two]; exact hsq
      have hd : ((H.d : ℕ) : 𝓞 H.E) ∈ P'.asIdeal := by
        have := P'.asIdeal.mul_mem_left s hs
        rw [hss] at this
        simpa using this
      exact P'.asIdeal.mem_of_dvd (Nat.cast_dvd_cast (α := 𝓞 H.E) (Dvd.intro_left (H.QS * H.q) rfl)) hd
  · rintro P hP P' hP' -
    rw [hunder P hP, hunder P' hP']

end GlobalTheory.TwistPdeltaPlaces
