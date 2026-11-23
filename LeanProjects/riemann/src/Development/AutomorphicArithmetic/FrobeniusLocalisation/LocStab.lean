import Mathlib
open NumberField IsDedekindDomain
open scoped Pointwise

namespace UpperTheory.HF.LocStab

open Polynomial

variable {E : Type} [Field E] [NumberField E]

theorem exists_compare (v : HeightOneSpectrum (𝓞 E)) (a b : 𝓞 E) :
    ∃ d t : 𝓞 E, d ∉ v.asIdeal ∧ (d * b = t * a ∨ d * a = t * b) := by
  let A := Localization.AtPrime v.asIdeal
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) v.ne_bot A
  have hinj : Function.Injective (algebraMap (𝓞 E) A) :=
    IsLocalization.injective A v.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨z, hz⟩ := ValuationRing.cond (algebraMap (𝓞 E) A a) (algebraMap (𝓞 E) A b)
  obtain ⟨⟨t, d⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl z
  refine ⟨d, t, d.2, ?_⟩
  have hs := IsLocalization.mk'_spec A t d
  rcases hz with hz | hz
  · left
    apply hinj
    simp only [map_mul]
    rw [← hz, ← hs]
    ring
  · right
    apply hinj
    simp only [map_mul]
    rw [← hz, ← hs]
    ring

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (c (x : E)) := by
    have h : IsIntegral ℤ (x : E) := x.2
    exact h.map (c.toIntAlgHom)
  have h : c (x : E) ∈ (NormedField.valuation (K := PadicAlgCl l)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral
      hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_unit (c : E →+* PadicAlgCl l) (v : HeightOneSpectrum (𝓞 E))
    (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) {d : 𝓞 E} (hd : d ∉ v.asIdeal) :
    ‖c (d : E)‖ = 1 :=
  le_antisymm (norm_int_le c d) (not_lt.1 fun h => hd ((hc d).2 h))

theorem lt_one_of_lt_one (c c' : E →+* PadicAlgCl l) (v : HeightOneSpectrum (𝓞 E))
    (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1)
    (hc' : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c' (x : E)‖ < 1) (x : E) (hx : ‖c x‖ < 1) :
    ‖c' x‖ < 1 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
  have hb0 : (b : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : ((b : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hb0
  have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hx0
    change ((a : 𝓞 E) : E) / ((b : 𝓞 E) : E) = 0
    simp [h]
  obtain ⟨d, t, hd, h | h⟩ := exists_compare v a b
  · exfalso
    have hdE : ((d : 𝓞 E) : E) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      simp [this]
    have hE : ((d : 𝓞 E) : E) * (b : E) = (t : E) * (a : E) := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h
    have htE : ((t : 𝓞 E) : E) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hE
      exact (mul_ne_zero hdE hbE) hE
    have hxe : (algebraMap (𝓞 E) E a) / (algebraMap (𝓞 E) E b) = (d : E) / (t : E) := by
      change ((a : 𝓞 E) : E) / ((b : 𝓞 E) : E) = _
      field_simp
      linear_combination -hE
    rw [hxe, map_div₀, norm_div, norm_unit c v hc hd] at hx
    have ht := norm_int_le c t
    have ht0 : 0 < ‖c (t : E)‖ := norm_pos_iff.2 (by simpa using htE)
    rw [div_lt_one ht0] at hx
    linarith
  · have hdE : ((d : 𝓞 E) : E) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      simp [this]
    have hE : ((d : 𝓞 E) : E) * (a : E) = (t : E) * (b : E) := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h
    have hxe : (algebraMap (𝓞 E) E a) / (algebraMap (𝓞 E) E b) = (t : E) / (d : E) := by
      change ((a : 𝓞 E) : E) / ((b : 𝓞 E) : E) = _
      field_simp
      linear_combination hE
    rw [hxe] at hx ⊢
    rw [map_div₀, norm_div, norm_unit c v hc hd, div_one] at hx
    rw [map_div₀, norm_div, norm_unit c' v hc' hd, div_one]
    exact (hc' t).1 ((hc t).2 hx)

theorem approx (β γ : PadicAlgCl l) (f : ℚ_[l][X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℚ[X], ‖aeval β G - aeval β f‖ < ε ∧ ‖aeval γ G - aeval γ f‖ < ε := by
  induction f using Polynomial.induction_on' generalizing ε with
  | add p q hp hq =>
    obtain ⟨G, h1, h2⟩ := hp (half_pos hε)
    obtain ⟨H, h3, h4⟩ := hq (half_pos hε)
    refine ⟨G + H, ?_, ?_⟩
    · simp only [map_add]
      rw [add_sub_add_comm]
      exact (norm_add_le _ _).trans_lt (by linarith)
    · simp only [map_add]
      rw [add_sub_add_comm]
      exact (norm_add_le _ _).trans_lt (by linarith)
  | monomial n a =>
    set M : ℝ := ‖β‖ ^ n + ‖γ‖ ^ n + 1 with hM
    have hMpos : 0 < M := by positivity
    obtain ⟨r, hr⟩ := Padic.rat_dense l a (div_pos hε hMpos)
    have key : ∀ δ : PadicAlgCl l, ‖δ‖ ^ n ≤ M → ‖aeval δ (monomial n r : ℚ[X]) - aeval δ (monomial n a : ℚ_[l][X])‖ < ε := by
      intro δ hδ
      have e1 : aeval δ (monomial n r : ℚ[X]) = algebraMap ℚ_[l] (PadicAlgCl l) (r : ℚ_[l]) * δ ^ n := by
        rw [aeval_monomial]
        simp
      have e2 : aeval δ (monomial n a : ℚ_[l][X]) = algebraMap ℚ_[l] (PadicAlgCl l) a * δ ^ n := by
        rw [aeval_monomial]
      rw [e1, e2, ← sub_mul, ← map_sub, norm_mul, norm_pow, PadicAlgCl.norm_extends, norm_sub_rev]
      calc ‖a - (r : ℚ_[l])‖ * ‖δ‖ ^ n ≤ ‖a - (r : ℚ_[l])‖ * M := by gcongr
        _ < ε / M * M := by gcongr
        _ = ε := by field_simp
    refine ⟨monomial n r, key β ?_, key γ ?_⟩
    · have := pow_nonneg (norm_nonneg γ) n
      linarith
    · have := pow_nonneg (norm_nonneg β) n
      linarith

theorem adjoin_eq_top {α : E} (hα : IntermediateField.adjoin ℚ {α} = ⊤) :
    Algebra.adjoin ℚ {α} = ⊤ := by
  have h := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) α)
  rw [← h, hα, IntermediateField.top_toSubalgebra]

theorem ringHom_ext {α : E} (hα : IntermediateField.adjoin ℚ {α} = ⊤) {B : Type} [Field B]
    [CharZero B] (f g : E →+* B) (h : f α = g α) : f = g := by
  have := AlgHom.ext_of_adjoin_eq_top (adjoin_eq_top hα) (φ₁ := f.toRatAlgHom) (φ₂ := g.toRatAlgHom)
    (by rintro _ rfl; exact h)
  ext x
  exact DFunLike.congr_fun this x

theorem norm_natCast_pow (c : E →+* PadicAlgCl l) (m : ℕ) :
    ‖c ((l : E) ^ m)‖ = ((l : ℝ)⁻¹) ^ m := by
  rw [map_pow, map_natCast, norm_pow]
  congr 1
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem root_of_stab (c : E →+* PadicAlgCl l) (α : E) (s : E ≃ₐ[ℚ] E)
    (v : HeightOneSpectrum (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1)
    (hs : s • v.asIdeal = v.asIdeal) :
    aeval (c (s α)) (minpoly ℚ_[l] (c α)) = 0 := by
  by_contra hne
  let c' : E →+* PadicAlgCl l := c.comp (s : E →+* E)
  have hc' : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c' (x : E)‖ < 1 := fun x => by
    have h1 : s • x ∈ v.asIdeal ↔ x ∈ v.asIdeal := by
      have := Ideal.smul_mem_pointwise_smul_iff (a := s) (S := v.asIdeal) (x := x)
      rwa [hs] at this
    rw [← h1, hc (s • x)]
    rfl
  set β := c α with hβ
  set γ := c (s α) with hγ
  set g := minpoly ℚ_[l] β with hgdef
  have ha : 0 < ‖aeval γ g‖ := norm_pos_iff.2 hne
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hl1
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (half_pos ha) hlinv
  have hδ : 0 < ((l : ℝ)⁻¹) ^ m := by positivity
  obtain ⟨G, h1, h2⟩ := approx β γ g hδ
  have hg : aeval β g = 0 := minpoly.aeval _ _
  rw [hg, sub_zero] at h1
  have hy1 : c (aeval α G) = aeval β G := (aeval_algHom_apply c.toRatAlgHom α G).symm
  have hy2 : c' (aeval α G) = aeval γ G := (aeval_algHom_apply c'.toRatAlgHom α G).symm
  have hlE : ((l : E) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hx : ‖c (aeval α G / (l : E) ^ m)‖ < 1 := by
    rw [map_div₀, norm_div, norm_natCast_pow, hy1, div_lt_one hδ]
    exact h1
  have hx' := lt_one_of_lt_one c c' v hc hc' _ hx
  rw [map_div₀, norm_div, norm_natCast_pow, hy2, div_lt_one hδ] at hx'
  have h3 : ‖aeval γ g‖ ≤ ‖aeval γ G‖ + ‖aeval γ G - aeval γ g‖ := by
    have := norm_sub_le (aeval γ G) (aeval γ G - aeval γ g)
    simpa using this
  linarith

theorem stab_of_root (c : E →+* PadicAlgCl l) {α : E}
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) (s : E ≃ₐ[ℚ] E)
    (v : HeightOneSpectrum (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1)
    (hroot : aeval (c (s α)) (minpoly ℚ_[l] (c α)) = 0) :
    s • v.asIdeal = v.asIdeal := by
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := ℚ_[l]) (L := PadicAlgCl l)
    (Algebra.IsAlgebraic.isAlgebraic (c α)) hroot
  have hcomp : ((σ : PadicAlgCl l →+* PadicAlgCl l).comp c) = c.comp (s : E →+* E) :=
    ringHom_ext hα _ _ hσ
  have hn : ∀ x : E, ‖c (s x)‖ = ‖c x‖ := fun x => by
    have h := DFunLike.congr_fun hcomp x
    change σ (c x) = c (s x) at h
    rw [← h]
    exact (spectralNorm_eq_of_equiv σ (c x)).symm
  have hmem : ∀ x : 𝓞 E, s • x ∈ v.asIdeal ↔ x ∈ v.asIdeal := fun x => by
    rw [hc, hc]
    exact iff_of_eq (congrArg (· < (1 : ℝ)) (hn x))
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hmem (s⁻¹ • y), smul_inv_smul]

theorem adjoin_range_eq (c : E →+* PadicAlgCl l) {α : E}
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) :
    IntermediateField.adjoin ℚ_[l] (Set.range c) = IntermediateField.adjoin ℚ_[l] {c α} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    have hle : Algebra.adjoin ℚ {α} ≤
        (((IntermediateField.adjoin ℚ_[l] {c α}).toSubalgebra.restrictScalars ℚ).comap
          c.toRatAlgHom) := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[l] (c α)
    have hx : x ∈ Algebra.adjoin ℚ {α} := by
      rw [adjoin_eq_top hα]
      exact Algebra.mem_top
    exact hle hx
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro _ rfl; exact ⟨α, rfl⟩)

theorem exists_aut_of_root (c : E →+* PadicAlgCl l) [IsGalois ℚ E] (α : E)
    {r : PadicAlgCl l} (hr : aeval r (minpoly ℚ_[l] (c α)) = 0) :
    ∃ s : E ≃ₐ[ℚ] E, c (s α) = r := by
  have hmin : minpoly ℚ (c α) = minpoly ℚ α :=
    minpoly.algHom_eq c.toRatAlgHom c.injective α
  have hdvd := minpoly.dvd_map_of_isScalarTower ℚ ℚ_[l] (c α)
  have hr' : aeval r (minpoly ℚ α) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    have : aeval r (map (algebraMap ℚ ℚ_[l]) (minpoly ℚ (c α))) = 0 := by
      rw [hq, map_mul, hr, zero_mul]
    rwa [aeval_map_algebraMap, hmin] at this
  have hsplit : (map (algebraMap ℚ E) (minpoly ℚ α)).Splits := Normal.splits inferInstance α
  have hne : minpoly ℚ α ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)
  have hmem : r ∈ (minpoly ℚ α).rootSet (PadicAlgCl l) := mem_rootSet.2 ⟨hne, hr'⟩
  rw [← hsplit.image_rootSet c.toRatAlgHom] at hmem
  obtain ⟨e, he, rfl⟩ := hmem
  obtain ⟨s, hs⟩ := minpoly.exists_algEquiv_of_root' (K := ℚ) (L := E)
    (Algebra.IsAlgebraic.isAlgebraic α) (mem_rootSet.1 he).2
  exact ⟨s, by rw [hs]; rfl⟩

theorem finrank_adjoin_range_eq_card_stabilizer :
    ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l)
      [IsGalois ℚ E] (v : HeightOneSpectrum (𝓞 E)),
      (∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) →
      Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range c)) =
        Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) := by
  intro l _ E _ _ c _ v hc
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have hint : IsIntegral ℚ_[l] (c α) := Algebra.IsIntegral.isIntegral _
  rw [adjoin_range_eq c hα, IntermediateField.adjoin.finrank hint]
  set g := minpoly ℚ_[l] (c α) with hg
  have hg0 : g ≠ 0 := minpoly.ne_zero hint
  have hsep : g.Separable := (minpoly.irreducible hint).separable
  have hcard : Fintype.card (g.rootSet (PadicAlgCl l)) = g.natDegree :=
    card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)
  rw [← hcard, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun s => ⟨c (s.1 α), mem_rootSet.2 ⟨hg0, root_of_stab c α s.1 v hc s.2⟩⟩) ⟨?_, ?_⟩)
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    have h1 : c (s α) = c (t α) := congrArg Subtype.val h
    have h2 : s α = t α := c.injective h1
    have h3 := ringHom_ext hα (s : E →+* E) (t : E →+* E) h2
    apply Subtype.ext
    ext x
    exact DFunLike.congr_fun h3 x
  · rintro ⟨r, hr⟩
    obtain ⟨s, rfl⟩ := exists_aut_of_root c α (mem_rootSet.1 hr).2
    exact ⟨⟨s, stab_of_root c hα s v hc (mem_rootSet.1 hr).2⟩, rfl⟩

end UpperTheory.HF.LocStab
