import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoefMove
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxIdealExactPowDvdSpanPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalCharPLocalCardStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntCastTraceEqTraceQuotientOfMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNeZeroFiniteLocalZmodPrimePowStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerDifferent

theorem not_pow_dvd_differentIdeal_int : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsPrime], la ≠ ⊥ → ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ¬ la ^ (e * e + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  intro L _ _ l e hl la _ hla h1 h2 hD
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : la.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hla
  obtain ⟨e', J, he0, hee, hcop, hfac⟩ := GlobalTheory.T.exists_span_prime_eq_pow_mul_coprime L l e hl la h1 h2
  obtain ⟨hchar, hfin, ϖ, hϖ, hlϖ, hcard⟩ := GlobalTheory.T.quotient_pow_finite_uniformizer_card_eq L la J l e' e' hl he0 he0 hcop hfac
  letI : Algebra (ZMod (l ^ e')) (𝓞 L ⧸ la ^ (e' * e')) := ZMod.algebra _ _
  have hnd : ¬ l ^ e' ∣ e' := fun h => (Nat.lt_pow_self hl.one_lt).not_ge (Nat.le_of_dvd he0 h)
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_trace_ne_zero_finite_local_zmod_prime_pow l e' e' (𝓞 L ⧸ la ^ (e' * e')) ϖ he0 hϖ hlϖ hcard hnd
  obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hIQ : la ^ (e' * e') ⊔ J ^ e' = ⊤ := by
    have h' : IsCoprime la J := Ideal.isCoprime_iff_sup_eq.mpr hcop
    exact Ideal.isCoprime_iff_sup_eq.mp (h'.pow)
  have hmul : la ^ (e' * e') * J ^ e' = Ideal.span {((l ^ e' : ℕ) : 𝓞 L)} := by
    rw [pow_mul, ← mul_pow, ← hfac, Ideal.span_singleton_pow, Nat.cast_pow]
  obtain ⟨i, hi, q, hq, hiq⟩ : ∃ i ∈ la ^ (e' * e'), ∃ q ∈ J ^ e', i + q = 1 := by
    have : (1 : 𝓞 L) ∈ la ^ (e' * e') ⊔ J ^ e' := hIQ ▸ Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hx : q * c0 ∈ J ^ e' := Ideal.mul_mem_right _ _ hq
  have hxc : Ideal.Quotient.mk (la ^ (e' * e')) (q * c0) = Ideal.Quotient.mk (la ^ (e' * e')) c0 := by
    rw [Ideal.Quotient.eq]
    have : q * c0 - c0 = -(i * c0) := by linear_combination c0 * hiq
    rw [this]; exact neg_mem (Ideal.mul_mem_right _ _ hi)
  have htr := GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' L l e' (la ^ (e' * e')) (J ^ e') hIQ hmul (q * c0) hx
  rw [hxc] at htr
  have hnot : Algebra.intTrace ℤ (𝓞 L) (q * c0) ∉ Ideal.span {((l ^ e' : ℕ) : ℤ)} := by
    intro hm
    rw [Algebra.intTrace_eq_trace, Ideal.mem_span_singleton] at hm
    apply hc
    rw [← htr, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hm)]
  have hmap : la ^ (e' * e') * J ^ e' = Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((l ^ e' : ℕ) : ℤ)}) := by
    rw [hmul, Ideal.map_span, Set.image_singleton, map_natCast]
  have := not_dvd_differentIdeal_of_intTrace_not_mem (A := ℤ) (la ^ (e' * e')) (J ^ e') hmap (q * c0) hx hnot
  apply this
  refine dvd_trans (pow_dvd_pow _ ?_) hD
  have := Nat.mul_le_mul hee hee
  omega

theorem differentIdeal_dvd_int (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    differentIdeal (𝓞 K) (𝓞 L) ∣ differentIdeal ℤ (𝓞 L) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 L)]
  exact dvd_mul_right _ _

theorem relDifferent_order_bounded : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  intro l e hl
  refine ⟨e * e, ?_⟩
  intro K L _ _ _ _ _ p la _ h1 h2 h3
  exact not_pow_dvd_differentIdeal_int L l e hl la.asIdeal la.ne_bot h1 h2 (dvd_trans h3 (differentIdeal_dvd_int K L))

end GlobalTheory.TowerDifferent
