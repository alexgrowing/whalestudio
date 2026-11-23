import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidueCard

theorem absNorm_eq_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    {w : Ideal (𝓞 E)} (hwp : w.IsPrime) (hw : ((p : ℕ) : 𝓞 E) ∈ w) :
    Ideal.absNorm w = p := by
  classical
  obtain ⟨hc, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard hp h
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hN : Ideal.absNorm I = p ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hprod : M.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hge : ∀ P ∈ M, p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    have hd : Ideal.absNorm P ∣ p ^ Module.finrank ℚ E := hN ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
    have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
    rw [hj] at h1 ⊢
    exact Nat.le_self_pow (by rintro rfl; simp at h1) p
  have hwM : w ∈ M := (Ideal.mem_normalizedFactors_iff hI0).2
    ⟨hwp, by rw [hI, Ideal.span_singleton_le_iff_mem]; exact hw⟩
  refine le_antisymm ?_ (hge _ hwM)
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hwM
  have h2 : p ^ M'.card ≤ (M'.map Ideal.absNorm).prod := by
    have := Multiset.pow_card_le_prod (s := M'.map Ideal.absNorm) (a := p) (fun x hx => by
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
      exact hge P (hM' ▸ Multiset.mem_cons_of_mem hP))
    simpa using this
  have h3 : Ideal.absNorm w * (M'.map Ideal.absNorm).prod = p * p ^ M'.card := by
    rw [← pow_succ', ← Multiset.card_cons w, ← hM', hc, ← hN, ← hprod, hM', Multiset.prod_cons, map_mul,
      map_multiset_prod]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < p ^ M'.card := pow_pos hp.pos _
  nlinarith

theorem card_quotient_of_ncard {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = p := by
  have := v.isPrime
  have := v.isMaximal
  obtain ⟨w, hwm, hwo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hw : ((p : ℕ) : 𝓞 E) ∈ w := by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ w.under (𝓞 F) := by rw [← hwo.over]; exact hv
    simpa using (show algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w from h1)
  have hN : Nat.card (𝓞 E ⧸ w) = p := by
    rw [← absNorm_eq_of_ncard hp h hwm.isPrime hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hd : Nat.card (𝓞 F ⧸ v.asIdeal) ∣ p := by
    rw [← hN]
    exact AddSubgroup.card_dvd_of_injective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w)).toAddMonoidHom
      (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w))
  refine ((Nat.dvd_prime hp).1 hd).resolve_left fun h1 => ?_
  have := (Nat.card_eq_one_iff_unique.1 h1).1
  exact not_subsingleton (𝓞 F ⧸ v.asIdeal) this

theorem card_kv : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  intro D i v hv
  rw [← card_quotient_of_ncard (D.host.g_prime i) (D.nd.g_split i) v hv]
  have h := Formalism.UG.P.tjcosets_card_residue v
  rw [h]
  simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.SplitResidueCard
