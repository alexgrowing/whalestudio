import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.NormEqOneOfValuationEqOne
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelicStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminantStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElementStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmFieldStatement

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

namespace Num

theorem value_bound (p q : ℕ) (l L : ℝ) (h7 : Real.log 7 / 2 ≤ l) :
    |((p : ℝ) - q) / 2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - l - L)| +
      ((p + q : ℕ) : ℝ) * Real.log 2 ≤ ((p + q : ℕ) : ℝ) * (3 / 2 * l + |L| / 2) := by
  have hc := OnHodge.const_le
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h70 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h4 : 2 * Real.log 2 ≤ Real.log (2 * Real.pi) := by
    have : Real.log (2 ^ 2) ≤ Real.log (2 * Real.pi) :=
      Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hL := le_abs_self L
  have hL' := neg_abs_le L
  have hp : (0 : ℝ) ≤ p := p.cast_nonneg
  have hq : (0 : ℝ) ≤ q := q.cast_nonneg
  set c := Real.eulerMascheroniConstant + Real.log (2 * Real.pi) with hcdef
  set b := 3 / 2 * l + |L| / 2 - Real.log 2 with hb
  have a1 : 0 ≤ b - (c - l - L) / 2 := by linarith
  have a2 : 0 ≤ b + (c - l - L) / 2 := by linarith
  have : |((p : ℝ) - q) / 2 * (c - l - L)| ≤ (p + q) * b :=
    abs_le.2 ⟨by nlinarith [mul_nonneg hp a2, mul_nonneg hq a1], by nlinarith [mul_nonneg hp a1, mul_nonneg hq a2]⟩
  push_cast
  nlinarith

theorem near_of (n : ℕ) (bad : Finset ℕ) (h2 : 2 ∈ bad) (rd L h₀ : ℝ) (d v : ℕ → ℝ)
    (hb : |h₀| + (n : ℝ) * Real.log 2 ≤ (n : ℝ) * (3 / 2 * Real.log rd + |L| / 2))
    (hd : ∀ r ∈ bad, 0 ≤ v r ∧ |d r| ≤ ((n : ℝ) * cP r + (n : ℝ) * v r) * Real.log r)
    (hv : ∑ r ∈ bad, v r * Real.log r ≤ Real.log rd) : NearRecord n bad rd L (h₀ + ∑ r ∈ bad, d r) := by
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 ≤ N * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_pos one_lt_two).le
  obtain ⟨hv2, hd2⟩ := hd 2 h2
  have hv2' := mul_nonneg hN0 hv2
  simp only [cP, if_true, Nat.cast_ofNat] at hd2
  obtain ⟨e, he, he'⟩ : ∃ e : ℝ, |e| ≤ N * Real.log 2 ∧ |d 2 - e| ≤ (N + N * v 2) * Real.log 2 := by
    rw [abs_le] at hd2
    rcases le_total 0 (d 2) with h | h
    · exact ⟨N * Real.log 2, (abs_of_nonneg hN0).le, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
    · exact ⟨-(N * Real.log 2), by rw [abs_neg, abs_of_nonneg hN0], abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩
  refine ⟨_ + e, fun r => d r - if r = 2 then e else 0, v, (abs_add_le _ _).trans ((add_le_add le_rfl he).trans hb), ?_,
    fun r hr => ⟨(hd r hr).1, ?_⟩, hv⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' bad 2, if_pos h2]; ring
  · by_cases h : r = 2
    · subst h
      have : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
      simp only [if_true, this, div_one]
      exact_mod_cast he'
    · have := (hd r hr).2
      simp only [cP, if_neg h] at this ⊢
      rwa [sub_zero, div_eq_mul_one_div]

def extP (g : Nat.Primes → ℝ) (n : ℕ) : ℝ := if h : n.Prime then g ⟨n, h⟩ else 0

theorem extendFromPrimes_coe (g : Nat.Primes → ℝ) (ℓ : Nat.Primes) : extP g ℓ = g ℓ := dif_pos ℓ.2

theorem exists_primes (bad : Finset ℕ) (hb : ∀ ℓ ∈ bad, ℓ.Prime) :
    ∃ B : Finset Nat.Primes, (∀ ℓ, ℓ ∈ B ↔ (ℓ : ℕ) ∈ bad) ∧ ∀ G : ℕ → ℝ, ∑ ℓ ∈ bad, G ℓ = ∑ ℓ ∈ B, G ℓ := by
  refine ⟨bad.preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) Subtype.val_injective.injOn, fun ℓ => Finset.mem_preimage,
    fun G => ?_⟩
  exact (Finset.sum_preimage (fun ℓ : Nat.Primes => (ℓ : ℕ)) bad Subtype.val_injective.injOn G
    fun x hx hn => absurd ⟨⟨x, hb x hx⟩, rfl⟩ hn).symm

theorem place_eq {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (κ : F →+* ℂ_[p])
    (v : HeightOneSpectrum (𝓞 F)) (h : ∀ a : F, v.valuation F a ≤ 1 ↔ ‖κ a‖ ≤ 1) : v = placeOf κ := by
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  rw [h, valuation_placeOf_le_one_iff]

theorem logIdeal_nonpos {E : Type} [Field E] [NumberField E] (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) :
    logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ≤ 0 := by
  obtain ⟨a, -, -, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    (j.injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
  rw [e]
  refine Real.log_nonpos (norm_nonneg _) ?_
  exact (valuation_placeOf_le_one_iff j (a : E)).1 ((placeOf j).valuation_le_one a)

end Num

open Num in
theorem numerics : Numerics := by
  intro E _ _ _ H p q F F' _ _ _ _ ι σ N r bad hσ h2 hbp hAd hdeg hloc
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  let N' : LogNorms F' := ⟨fun s => N.inf (s.comp ι), fun ℓ κ' => (r (placeOf κ') : ℝ) * Real.log ‖κ' (π (placeOf κ'))‖⟩
  obtain ⟨hAd', hdeg'⟩ := deg_eq_places F' N' r (by
    intro ℓ κ' v π' hv hπ'
    obtain rfl := place_eq κ' v hv
    have h0 : π' ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have := log_norm_eq_of_valuation κ' (n := 1) (hπ _) hπ' h0
    show _ * _ = _
    rw [this]
    simp)
  have hgoal : ((r.sum fun v x => (x : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ s : F' →+* ℂ, N.inf (s.comp ι)) /
      (Module.finrank ℚ F' : ℝ) = N'.deg := hdeg'.symm
  rw [hgoal]
  obtain ⟨hext, hextA⟩ := GlobalTheory.T.logNorms_ext_degree_adelic F F' ι N
  have hAdx : (N.ext ι).IsAdelic := hextA.2 hAd
  have hl := fun (ℓ : Nat.Primes) (κ' : F' →+* ℂ_[ℓ]) =>
    hloc ℓ κ' (placeOf κ') (π _) (valuation_placeOf_le_one_iff κ') (hπ _)
  have hn' : (0 : ℝ) < Module.finrank ℚ F' := by exact_mod_cast Module.finrank_pos
  have hnE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  obtain ⟨B, hB, hBs⟩ := exists_primes bad hbp
  let f : E →+* F' := IsFractionRing.lift (A := 𝓞 E) (g := ι.comp σ) (ι.injective.comp hσ)
  have hf : ∀ a : 𝓞 E, f (algebraMap (𝓞 E) E a) = ι (σ a) := fun a => IsFractionRing.lift_algebraMap _ a
  let g : Nat.Primes → ℝ := fun ℓ => -(N'.finSum ℓ - (N.ext ι).finSum ℓ) / Module.finrank ℚ F'
  let w : Nat.Primes → ℝ := fun ℓ =>
    -∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ => neg_nonneg.2 (Finset.sum_nonpos fun j _ => logIdeal_nonpos ℓ j)
  have hlog : ∀ ℓ : Nat.Primes, 0 < Real.log (ℓ : ℕ) := fun ℓ => Real.log_pos (by exact_mod_cast ℓ.2.one_lt)
  have hsupp : ∀ M : LogNorms F', M.IsAdelic → (Function.support M.finSum).Finite := fun M hM =>
    Set.Finite.subset hM fun ℓ hℓ => by
      by_contra hc
      simp only [Set.mem_setOf_eq, not_exists, not_not] at hc
      exact hℓ (by simp [LogNorms.finSum, hc])
  have hsplit : N'.deg = N.deg + ∑ ℓ ∈ bad, extP g ℓ := by
    rw [hBs, ← hext]
    simp only [extendFromPrimes_coe, g]
    have e1 : ∑ᶠ ℓ, (N'.finSum ℓ - (N.ext ι).finSum ℓ) = ∑ ℓ ∈ B, (N'.finSum ℓ - (N.ext ι).finSum ℓ) := by
      refine finsum_eq_sum_of_support_subset _ fun ℓ hℓ => ?_
      by_contra hc
      refine hℓ (sub_eq_zero.2 (Finset.sum_congr rfl fun κ' _ => ?_))
      exact (hl ℓ κ').1 fun h => hc ((hB ℓ).2 h)
    rw [finsum_sub_distrib (hsupp _ hAd') (hsupp _ hAdx)] at e1
    rw [← Finset.sum_div, Finset.sum_neg_distrib, ← e1]
    have e2 : ∑ s, N'.inf s = ∑ s, (N.ext ι).inf s := rfl
    simp only [LogNorms.deg]
    rw [e2]
    ring
  rw [hsplit]
  have hrd : hostRd E = rootDiscr E := OnHodge.hostRd_eq E
  refine near_of (p + q) bad h2 _ _ _ _ (extP fun ℓ => w ℓ / Module.finrank ℚ E / Real.log (ℓ : ℕ)) ?_ ?_ ?_
  · rw [hdeg]
    refine value_bound p q _ _ ?_
    have h7 : (7 : ℝ) ≤ H.d := by
      have := H.d_mod
      have : 7 ≤ H.d := by omega
      exact_mod_cast this
    have h1 := (GlobalTheory.T.sqrt_discriminant_bounds_cm_field E H).2
    rw [hrd, ← Real.log_sqrt (by norm_num)]
    exact Real.log_le_log (Real.sqrt_pos.2 (by norm_num)) ((Real.sqrt_le_sqrt h7).trans h1)
  · intro n hn
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ : Nat.Primes, (ℓ : ℕ) = n := ⟨⟨n, hbp n hn⟩, rfl⟩
    rw [extendFromPrimes_coe, extendFromPrimes_coe]
    refine ⟨div_nonneg (div_nonneg (hw0 ℓ) hnE.le) (hlog ℓ).le, ?_⟩
    have hk : ∀ κ' : F' →+* ℂ_[ℓ], |N'.fin ℓ κ' - (N.ext ι).fin ℓ κ'| ≤ ((p + q : ℕ) : ℝ) * (cP ℓ * Real.log (ℓ : ℕ) -
        logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := fun κ' => by
      obtain ⟨a, ha, ha0, -, e⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
        ((κ'.comp f).injective.comp RingOfIntegers.coe_injective) differentIdeal_ne_bot
      rw [e, RingHom.comp_apply, RingHom.comp_apply, hf]
      exact (hl ℓ κ').2 hn a ha ha0
    have hfib := GlobalTheory.T.sum_embeddings_base_change E F' ℂ_[ℓ] f
      fun j => logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
    have hs : |N'.finSum ℓ - (N.ext ι).finSum ℓ| ≤ ((p + q : ℕ) : ℝ) * (Module.finrank ℚ F' * (cP ℓ * Real.log (ℓ : ℕ)) -
        ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := by
      simp only [LogNorms.finSum]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun κ' _ => hk κ').trans (le_of_eq ?_))
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
    have hS : ∑ κ' : F' →+* ℂ_[ℓ], logIdeal ((κ'.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
        -(Module.finrank ℚ F' * (w ℓ / Module.finrank ℚ E)) := by
      apply mul_left_cancel₀ hnE.ne'
      rw [hfib]
      simp only [w]
      field_simp
    rw [hS] at hs
    simp only [g]
    rw [abs_div, abs_neg, abs_of_pos hn', div_le_iff₀ hn']
    refine hs.trans (le_of_eq ?_)
    have := (hlog ℓ).ne'
    field_simp
    ring
  · rw [hBs]
    simp only [extendFromPrimes_coe]
    obtain ⟨hfin, hsum⟩ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hwf : (Function.support w).Finite := hfin.subset fun ℓ hℓ => fun h => hℓ (by simp only [w]; rw [h, neg_zero])
    have hws : ∑ᶠ ℓ, w ℓ = Module.finrank ℚ E * Real.log (rootDiscr E) := by
      simp only [w]
      rw [finsum_neg_distrib, hsum]
      ring
    have hle : ∑ ℓ ∈ B, w ℓ ≤ ∑ᶠ ℓ, w ℓ := by
      rw [finsum_eq_sum_of_support_subset w (s := B ∪ hwf.toFinset) (fun ℓ hℓ => by simp [hℓ])]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun ℓ _ _ => hw0 ℓ
    rw [Finset.sum_congr rfl fun ℓ _ => div_mul_cancel₀ _ (hlog ℓ).ne', ← Finset.sum_div, div_le_iff₀ hnE, hrd]
    linarith

end RootFieldNumerics.RF
