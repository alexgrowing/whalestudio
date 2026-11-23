import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.LocStab

open Polynomial

variable {E : Type} [Field E] [NumberField E]

theorem exists_compare (v : HeightOneSpectrum (𝓞 E)) (a b : 𝓞 E) :
    ∃ d t : 𝓞 E, d ∉ v.asIdeal ∧ (d * b = t * a ∨ d * a = t * b) := by

  haveI := v.isPrime
  let Rv := Localization.AtPrime v.asIdeal
  haveI : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) v.ne_bot Rv
  obtain ⟨q, hq⟩ := ValuationRing.cond (algebraMap (𝓞 E) Rv a) (algebraMap (𝓞 E) Rv b)
  obtain ⟨⟨t, d⟩, hq'⟩ := IsLocalization.surj v.asIdeal.primeCompl q
  have hinj := IsLocalization.injective Rv (Ideal.primeCompl_le_nonZeroDivisors v.asIdeal)
  rcases hq with h | h
  · refine ⟨d, t, d.2, Or.inl (hinj ?_)⟩
    rw [map_mul, map_mul, ← hq', ← h]
    ring
  · refine ⟨d, t, d.2, Or.inr (hinj ?_)⟩
    rw [map_mul, map_mul, ← hq', ← h]
    ring

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hI : IsIntegral ℤ (c (x : E)) := (NumberField.RingOfIntegers.isIntegral_coe x).map c.toIntAlgHom
  obtain ⟨P, hPm, hP⟩ := hI
  set y := c (x : E) with hy
  by_contra hlt
  push_neg at hlt
  have hcoef : ∀ z : ℤ, ‖((z : PadicAlgCl l))‖ ≤ 1 := fun z => by
    rw [← map_intCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_int_le_one z
  set n := P.natDegree with hndef
  have hn : 0 < n := by
    by_contra h0
    push_neg at h0
    have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hPm (by omega)
    rw [h1] at hP
    simp at hP

  have heq : y ^ n = -∑ i ∈ Finset.range n, (P.coeff i : PadicAlgCl l) * y ^ i := by
    have h := hP
    rw [hPm.as_sum] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
    rw [eq_neg_iff_add_eq_zero]
    simpa using h
  have hle : ‖y ^ n‖ ≤ ‖y‖ ^ (n - 1) := by
    rw [heq, norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖(P.coeff i : PadicAlgCl l)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (n - 1) :=
          mul_le_mul (hcoef _) (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
      _ = ‖y‖ ^ (n - 1) := one_mul _
  rw [norm_pow] at hle
  have hlt2 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
  linarith

theorem norm_unit (c : E →+* PadicAlgCl l) (v : HeightOneSpectrum (𝓞 E))
    (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) {d : 𝓞 E} (hd : d ∉ v.asIdeal) :
    ‖c (d : E)‖ = 1 :=
  le_antisymm (norm_int_le c d) (not_lt.mp fun h => hd ((hc d).mpr h))

theorem lt_one_of_lt_one (c c' : E →+* PadicAlgCl l) (v : HeightOneSpectrum (𝓞 E))
    (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1)
    (hc' : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c' (x : E)‖ < 1) (x : E) (hx : ‖c x‖ < 1) :
    ‖c' x‖ < 1 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨a, b, hbm, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb : (b : E) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbm
  subst hab
  have hcb : ∀ φ : E →+* PadicAlgCl l, ‖φ (b : E)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hb
  obtain ⟨d, t, hd, h | h⟩ := exists_compare v a b
  ·
    exfalso
    have ha : (a : E) ≠ 0 := by
      intro ha
      apply hx0
      show (a : E) / (b : E) = 0
      rw [ha, zero_div]
    have hE : (d : E) * b = t * a := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) h
    have hmul : ‖c (d : E)‖ * ‖c (b : E)‖ = ‖c (t : E)‖ * ‖c (a : E)‖ := by
      rw [← norm_mul, ← norm_mul, ← map_mul c, ← map_mul c, hE]
    rw [norm_unit c v hc hd, one_mul] at hmul
    have hca : 0 < ‖c (a : E)‖ := norm_pos_iff.mpr ((map_ne_zero c).mpr ha)
    have hct : 0 < ‖c (t : E)‖ := by
      rcases (norm_nonneg (c (t : E))).lt_or_eq with h' | h'
      · exact h'
      · rw [← h', zero_mul] at hmul
        exact absurd hmul (hcb c)
    have htle := norm_int_le c t
    change ‖c ((a : E) / (b : E))‖ < 1 at hx
    rw [map_div₀, norm_div, hmul, div_lt_one (mul_pos hct hca)] at hx
    nlinarith
  ·
    have hE : (d : E) * a = t * b := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) h
    have hmul : ∀ φ : E →+* PadicAlgCl l, (∀ y : 𝓞 E, y ∈ v.asIdeal ↔ ‖φ (y : E)‖ < 1) →
        ‖φ (a : E)‖ = ‖φ (t : E)‖ * ‖φ (b : E)‖ := by
      intro φ hφ
      have h1 : ‖φ (d : E)‖ * ‖φ (a : E)‖ = ‖φ (t : E)‖ * ‖φ (b : E)‖ := by
        rw [← norm_mul, ← norm_mul, ← map_mul φ, ← map_mul φ, hE]
      rwa [norm_unit φ v hφ hd, one_mul] at h1
    change ‖c ((a : E) / (b : E))‖ < 1 at hx
    rw [map_div₀, norm_div, hmul c hc, mul_div_assoc, div_self (hcb c), mul_one] at hx
    have ht : t ∈ v.asIdeal := (hc t).mpr hx
    have h2 := (hc' t).mp ht
    show ‖c' ((a : E) / (b : E))‖ < 1
    rw [map_div₀, norm_div, hmul c' hc', mul_div_assoc, div_self (hcb c'), mul_one]
    exact h2

theorem approx (β γ : PadicAlgCl l) (f : ℚ_[l][X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℚ[X], ‖aeval β G - aeval β f‖ < ε ∧ ‖aeval γ G - aeval γ f‖ < ε := by

  set n := f.natDegree with hn
  set M : ℝ := max 1 (max ‖β‖ ‖γ‖) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMn : 0 < M ^ n := pow_pos (by linarith) n
  set δ : ℝ := ε / (2 * M ^ n) with hδ
  have hδpos : 0 < δ := by positivity
  choose g hg using fun i => Padic.rat_dense l (f.coeff i) hδpos
  let G : ℚ[X] := ∑ i ∈ Finset.range (n + 1), C (g i) * X ^ i
  have key : ∀ x : PadicAlgCl l, ‖x‖ ≤ M → ‖aeval x G - aeval x f‖ < ε := by
    intro x hx
    have e1 : aeval x G = ∑ i ∈ Finset.range (n + 1),
        algebraMap ℚ_[l] (PadicAlgCl l) (g i : ℚ_[l]) * x ^ i := by
      simp only [G, map_sum, map_mul, map_pow, aeval_C, aeval_X, map_ratCast, eq_ratCast]
    have e2 : aeval x f = ∑ i ∈ Finset.range (n + 1),
        algebraMap ℚ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i := by
      rw [aeval_eq_sum_range, ← hn]
      simp only [Algebra.smul_def]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    have hle : ‖∑ i ∈ Finset.range (n + 1), (algebraMap ℚ_[l] (PadicAlgCl l) (g i : ℚ_[l]) * x ^ i -
        algebraMap ℚ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i)‖ ≤ δ * M ^ n := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← sub_mul, ← map_sub, norm_mul, PadicAlgCl.norm_extends, norm_pow, norm_sub_rev]
      have hxi : ‖x‖ ^ i ≤ M ^ n :=
        (pow_le_pow_left₀ (norm_nonneg x) hx i).trans (pow_le_pow_right₀ hM1 hi')
      exact mul_le_mul (hg i).le hxi (by positivity) hδpos.le
    have hlt : δ * M ^ n < ε := by
      rw [hδ, div_mul_eq_mul_div, mul_div_assoc]
      have : M ^ n / (2 * M ^ n) = 1 / 2 := by field_simp
      rw [this]
      linarith
    exact lt_of_le_of_lt hle hlt
  exact ⟨G, key β (le_trans (le_max_left _ _) (le_max_right _ _)),
    key γ (le_trans (le_max_right _ _) (le_max_right _ _))⟩

theorem adjoin_eq_top {α : E} (hα : IntermediateField.adjoin ℚ {α} = ⊤) :
    Algebra.adjoin ℚ {α} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα,
    IntermediateField.top_toSubalgebra]

theorem ringHom_ext {α : E} (hα : IntermediateField.adjoin ℚ {α} = ⊤) {B : Type} [Field B]
    [CharZero B] (f g : E →+* B) (h : f α = g α) : f = g := by
  have h1 := AlgHom.ext_of_adjoin_eq_top (adjoin_eq_top hα) (φ₁ := f.toRatAlgHom) (φ₂ := g.toRatAlgHom)
    (by
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact h)
  ext x
  exact AlgHom.congr_fun h1 x

theorem norm_natCast_pow (c : E →+* PadicAlgCl l) (m : ℕ) :
    ‖c ((l : E) ^ m)‖ = ((l : ℝ)⁻¹) ^ m := by
  rw [map_pow, map_natCast, norm_pow]
  congr 1
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

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
    rintro _ ⟨e, rfl⟩
    have he : e ∈ Algebra.adjoin ℚ {α} := by
      rw [adjoin_eq_top hα]
      trivial
    induction he using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact IntermediateField.mem_adjoin_simple_self _ _
    | algebraMap q =>
      have e1 : c (algebraMap ℚ E q) = algebraMap ℚ_[l] (PadicAlgCl l) (q : ℚ_[l]) := by
        rw [eq_ratCast, map_ratCast, map_ratCast]
      rw [e1]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin _ _ ⟨α, rfl⟩

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

end GlobalTheory.LocStab
