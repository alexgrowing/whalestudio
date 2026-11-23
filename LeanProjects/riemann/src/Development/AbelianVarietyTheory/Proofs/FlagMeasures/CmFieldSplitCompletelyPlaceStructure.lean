import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.SplitPrime

open Formalism.MainNotions.Gaps.LevGap Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem span_natPrime_isMaximal (p : ℕ) (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  exact ((Ideal.span_singleton_prime hpz.ne_zero).mpr hpz).isMaximal
    (by simpa [Ideal.span_singleton_eq_bot] using hpz.ne_zero)

private theorem liesOver_span_of_natCast_mem_flag_measures {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 K)) [hQ : Q.IsPrime] (h : (p : 𝓞 K) ∈ Q) : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hmax := span_natPrime_isMaximal p hp
  constructor
  refine hmax.eq_of_le (Ideal.comap_ne_top _ hQ.ne_top) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ Q
  simpa using h

private theorem ncard_places_dvd_eq_ncard_primesOver (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard =
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [← Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  congr 1
  ext Q
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_span_of_natCast_mem_flag_measures p hp v.asIdeal hv⟩
  · rintro ⟨hQ, hl⟩
    have hne : Q ≠ ⊥ := by
      rintro rfl
      have h1 := hl.over
      rw [Ideal.under_bot] at h1
      exact (by simpa [Ideal.span_singleton_eq_bot] using hpz.ne_zero : Ideal.span {(p : ℤ)} ≠ ⊥) h1
    refine ⟨⟨Q, hQ, hne⟩, ?_, rfl⟩
    have h2 : ((p : ℤ)) ∈ Q.under ℤ := hl.over ▸ Ideal.subset_span rfl
    simpa [Ideal.mem_comap] using h2

private theorem sum_ramificationIdx_mul_inertiaDeg_primesOver (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    haveI := span_natPrime_isMaximal p hp
    ∑ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ =
      Module.finrank ℚ K := by
  have := span_natPrime_isMaximal p hp
  rw [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank]

private theorem eq_one_of_pos_of_sum_eq_card {ι : Type} [Fintype ι] (f : ι → ℕ) (hpos : ∀ i, 0 < f i)
    (hs : ∑ i, f i = Fintype.card ι) (i : ι) : f i = 1 := by
  by_contra h
  have hlt : ∑ j, 1 < ∑ j, f j :=
    Finset.sum_lt_sum (fun j _ => hpos j) ⟨i, Finset.mem_univ _, by have := hpos i; omega⟩
  simp [hs] at hlt

private theorem ramificationIdx_inertiaDeg_eq_one_of_ncard_eq_finrank (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (Q : Ideal (𝓞 K)) [hQ : Q.IsPrime] (h : (p : 𝓞 K) ∈ Q) :
    Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1 := by
  have := span_natPrime_isMaximal p hp
  have := liesOver_span_of_natCast_mem_flag_measures p hp Q h
  have key := eq_one_of_pos_of_sum_eq_card (fun q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) => q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ)
    (fun q => by
      have := q.2.1
      exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _))
    (by rw [sum_ramificationIdx_mul_inertiaDeg_primesOver K p hp, ← hs, ncard_places_dvd_eq_ncard_primesOver K p hp, Set.ncard_eq_toFinset_card', Set.toFinset_card]) ⟨Q, hQ, inferInstance⟩
  exact mul_eq_one.mp key

theorem ram_inertia_tower (p : ℕ) (hp : p.Prime) (hs : SplitsIn E p) (v : Ideal (𝓞 F)) [v.IsPrime]
    (hv : (p : 𝓞 F) ∈ v) (w : Ideal (𝓞 E)) [hw : w.IsPrime] [hl : w.LiesOver v] :
    (v.ramificationIdx ℤ = 1 ∧ v.inertiaDeg ℤ = 1) ∧
      w.ramificationIdx (𝓞 F) = 1 ∧ w.inertiaDeg (𝓞 F) = 1 := by
  unfold SplitsIn placesOver at hs
  have hwp : (p : 𝓞 E) ∈ w := by
    have h1 : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w := by
      have h2 : (p : 𝓞 F) ∈ w.under (𝓞 F) := hl.over ▸ hv
      simpa [Ideal.mem_comap] using h2
    simpa using h1
  obtain ⟨he, hf⟩ := ramificationIdx_inertiaDeg_eq_one_of_ncard_eq_finrank E p hp hs w hwp
  have te := Ideal.ramificationIdx_tower (R := ℤ) (q := v) (r := w)
  have tf := Ideal.inertiaDeg_tower (R := ℤ) (q := v) (r := w)
  rw [he, eq_comm, mul_eq_one] at te
  rw [hf, eq_comm, mul_eq_one] at tf
  exact ⟨⟨te.1, tf.1⟩, te.2, tf.2⟩

theorem ncard_base (p : ℕ) (hp : p.Prime) (hs : SplitsIn E p) :
    {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F := by
  have := span_natPrime_isMaximal p hp
  rw [ncard_places_dvd_eq_ncard_primesOver F p hp, ← sum_ramificationIdx_mul_inertiaDeg_primesOver F p hp, Set.ncard_eq_toFinset_card', Set.toFinset_card,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hq1 : q.1.IsPrime := q.2.1
  have hq2 : q.1.LiesOver (Ideal.span {(p : ℤ)}) := q.2.2
  have hpne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hqmax : q.1.IsMaximal := hq1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hpne q.1)
  have hpq : (p : 𝓞 F) ∈ q.1 := by
    have h1 : ((p : ℤ)) ∈ q.1.under ℤ := hq2.over ▸ Ideal.subset_span rfl
    simpa [Ideal.mem_comap] using h1
  obtain ⟨w, hwm, hw⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) q.1
  have hwp : w.IsPrime := hwm.isPrime
  obtain ⟨⟨he, hf⟩, -⟩ := ram_inertia_tower (E := E) p hp hs q.1 hpq w
  rw [he, hf]

theorem exists_two (h2 : Module.finrank F E = 2) (p : ℕ) (hp : p.Prime) (hs : SplitsIn E p)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) :
    ∃ w w' : v.asIdeal.primesOver (𝓞 E), w ≠ w' := by
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hsum
  have hcard : Fintype.card (v.asIdeal.primesOver (𝓞 E)) = 2 := by
    rw [Fintype.card_eq_sum_ones, ← hsum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hq1 : q.1.IsPrime := q.2.1
    have hq2 : q.1.LiesOver v.asIdeal := q.2.2
    obtain ⟨-, he, hf⟩ := ram_inertia_tower (E := E) p hp hs v.asIdeal hv q.1
    rw [he, hf]
  exact Fintype.one_lt_card_iff.mp (by omega)

theorem exists_int (y : 𝓞 E) (hy : ∃ b, algebraMap F E b = (y : E)) :
    ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = y := by
  obtain ⟨b, hb⟩ := hy
  have hint : IsIntegral ℤ b := by
    have h1 : IsIntegral ℤ (algebraMap F E b) := hb ▸ RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).mp h1
  refine ⟨⟨b, hint⟩, ?_⟩
  apply RingOfIntegers.ext
  exact hb

theorem nonempty_splitCore (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → ∃ a, algebraMap F E a = x) (h2 : Module.finrank F E = 2)
    (v : HeightOneSpectrum (𝓞 F)) (w w' : v.asIdeal.primesOver (𝓞 E)) (hne : w ≠ w') :
    Nonempty (SplitCore σ v) := by
  have hw1 : w.1.IsPrime := w.2.1
  have hl : w.1.LiesOver v.asIdeal := w.2.2
  have hw1' : w'.1.IsPrime := w'.2.1
  have hl' : w'.1.LiesOver v.asIdeal := w'.2.2
  have hwmax : w.1.IsMaximal := hw1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot w.1)
  have hnle : ¬ w.1 ≤ w'.1 := fun hle => hne (Subtype.ext (hwmax.eq_of_le hw1'.ne_top hle))
  obtain ⟨a, haw, haw'⟩ := SetLike.not_le_iff_exists.mp hnle
  have hsa : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map (σ.restrictScalars ℤ)
  let sa : 𝓞 E := ⟨σ a, hsa⟩
  have hsa' : (sa : E) = σ a := rfl
  have hfixed : ∀ y : 𝓞 E, σ (y : E) = y → ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = y :=
    fun y hy => exists_int y (hfix _ hy)
  obtain ⟨t, ht⟩ := hfixed (a + sa) (by simp [hsa', hσ, add_comm])
  obtain ⟨N, hN⟩ := hfixed (a * sa) (by simp [hsa', hσ, mul_comm])
  have hmem : ∀ (P : Ideal (𝓞 E)), P.LiesOver v.asIdeal → ∀ b : 𝓞 F,
      b ∈ v.asIdeal → algebraMap (𝓞 F) (𝓞 E) b ∈ P := by
    intro P hP b hb
    have h1 : b ∈ P.under (𝓞 F) := hP.over ▸ hb
    exact h1
  have hmem' : ∀ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b ∈ w.1 → b ∈ v.asIdeal := by
    intro b hb
    have h1 : b ∈ w.1.under (𝓞 F) := hb
    exact hl.over ▸ h1
  have hNv : N ∈ v.asIdeal := hmem' N (by rw [hN]; exact w.1.mul_mem_right _ haw)
  refine sc_core σ hσ hfix h2 v a t N ?_ ?_ hNv ?_
  · show ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) = _
    rw [ht]
    rfl
  · show ((algebraMap (𝓞 F) (𝓞 E) N : 𝓞 E) : E) = _
    rw [hN]
    rfl
  · intro htv
    have h1 : a + sa ∈ w'.1 := ht ▸ hmem w'.1 hl' t htv
    have h2' : a * sa ∈ w'.1 := hN ▸ hmem w'.1 hl' N hNv
    rcases hw1'.mem_or_mem h2' with h | h
    · exact haw' h
    · exact haw' (by simpa using w'.1.sub_mem h1 h)

private theorem natCast_not_mem_sq_of_ramificationIdx_eq_one (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) (he : v.asIdeal.ramificationIdx ℤ = 1) :
    (p : 𝓞 K) ∉ v.asIdeal ^ 2 := by
  intro h2
  have := liesOver_span_of_natCast_mem_flag_measures p hp v.asIdeal hv
  have hpne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (R := ℤ) (p := Ideal.span {(p : ℤ)}) (q := v.asIdeal) hpne] at he
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal ^ 2 := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    simpa using h2
  unfold Ideal.ramificationIdx' at he
  by_cases hb : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal ^ n}
  · have h3 := le_csSup hb (show 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal ^ n} from hmap)
    omega
  · rw [Nat.sSup_of_not_bddAbove hb] at he
    exact zero_ne_one he

private theorem val_lemma_7 (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) (hnot : (p : 𝓞 K) ∉ v.asIdeal ^ 2) :
    Valued.v ((p : ℕ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  have hc : ((p : ℕ) : v.adicCompletion K) = (((p : ℕ) : K) : v.adicCompletion K) := by
    first
      | exact (map_natCast (algebraMap K (v.adicCompletion K)) p).symm
      | norm_cast
      | rfl
  rw [hc, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 K) K) p,
    HeightOneSpectrum.valuation_of_algebraMap]
  have h0 : v.intValuation (p : 𝓞 K) ≠ 0 := v.intValuation_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have h1 := (v.intValuation_le_pow_iff_mem (p : 𝓞 K) 1).mpr (by simpa using hv)
  have h2 : ¬ v.intValuation (p : 𝓞 K) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hnot ((v.intValuation_le_pow_iff_mem _ 2).mp h)
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

private theorem maximalIdeal_adicCompletionIntegers_eq_span_of_valued (K : Type) [Field K] [NumberField K] (p : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hval : Valued.v ((p : ℕ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {(p : v.adicCompletionIntegers K)} := by
  have hu : IsUnifV K v ((p : ℕ) : v.adicCompletion K) := hval
  have hne := Formalism.UG.P.tjcosets_ne_zero v _ hu
  have hpc : ((p : v.adicCompletionIntegers K) : v.adicCompletion K) = ((p : ℕ) : v.adicCompletion K) := by
    simp
  have hpm : (p : v.adicCompletionIntegers K) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    refine (Formalism.UG.P.tjcosets_mem_max v _).mpr ?_
    rw [hpc, hval, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  ext x
  constructor
  · intro hx
    have h0 : IsLocalRing.residue _ x = 0 := (IsLocalRing.residue_eq_zero_iff x).mpr hx
    have hm := (Formalism.UG.P.tjcosets_hmax v _ hu x).mpr h0
    refine Ideal.mem_span_singleton'.mpr ⟨⟨_, hm⟩, ?_⟩
    apply Subtype.ext
    show (((p : ℕ) : v.adicCompletion K)⁻¹ * (x : v.adicCompletion K)) *
      ((p : v.adicCompletionIntegers K) : v.adicCompletion K) = x
    rw [hpc]
    field_simp
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mul_mem_left _ a hpm

theorem split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (p : ℕ), p.Prime → SplitsIn E p → ({v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → Nat.card (kv F v) = p ∧ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {(p : v.adicCompletionIntegers F)} ∧ ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F, (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) ∧ ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a) := by
  intro F E _ _ _ _ _ _ cm p hp hs
  have hσ : ∀ x, cm.sig (cm.sig x) = x := fun x => star_star x
  have hfix : ∀ x, cm.sig x = x → ∃ a, algebraMap F E a = x := fun x hx => (cm.fixed x).mp hx
  have hF := ncard_base (F := F) (E := E) p hp hs
  refine ⟨hF, fun v hv => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨-, hf⟩ := ramificationIdx_inertiaDeg_eq_one_of_ncard_eq_finrank F p hp hF v.asIdeal hv
    have := span_natPrime_isMaximal p hp
    have := v.isMaximal
    have hlo := liesOver_span_of_natCast_mem_flag_measures p hp v.asIdeal hv
    rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) v.asIdeal] at hf
    letI := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
    have : Module.Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 F ⧸ v.asIdeal) := Module.finite_of_finrank_eq_succ hf
    let e := LinearEquiv.ofFinrankEq (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 F ⧸ v.asIdeal)
      (by rw [Module.finrank_self, hf])
    unfold kv
    rw [fm_card_residue v, ← Nat.card_congr e.toEquiv,
      Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  · obtain ⟨he, -⟩ := ramificationIdx_inertiaDeg_eq_one_of_ncard_eq_finrank F p hp hF v.asIdeal hv
    exact maximalIdeal_adicCompletionIntegers_eq_span_of_valued F p v (val_lemma_7 F p hp v hv (natCast_not_mem_sq_of_ramificationIdx_eq_one F p hp v hv he))
  · obtain ⟨w, w', hne⟩ := exists_two (F := F) (E := E) cm.deg2 p hp hs v hv
    obtain ⟨s⟩ := nonempty_splitCore cm.sig hσ hfix cm.deg2 v w w' hne
    exact ⟨s.φ, s.sig, s.alg⟩

end GlobalTheory.St.G.SplitPrime
