import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.SplitPrime

open Polynomial

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in

theorem _root_.GlobalTheory.SW.SplitPrime.exists_prim_den (E : Type) [Field E] [NumberField E] :
    ∃ (θ : 𝓞 E) (d : ℤ), d ≠ 0 ∧ Algebra.adjoin ℚ {(θ : E)} = ⊤ ∧
      ∀ a : 𝓞 E, ∃ g : ℤ[X], (d : 𝓞 E) * a = aeval θ g := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨y, hy0, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
    (Algebra.IsAlgebraic.isAlgebraic α)).exists_integral_multiple
  set θ : E := y • α with hθdef
  clear_value θ
  have hθ : IntermediateField.adjoin ℚ {θ} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have hy : ((y : ℚ) : E) ≠ 0 := by exact_mod_cast hy0
    have : α = ((y : ℚ) : E)⁻¹ * θ := by
      rw [hθdef, zsmul_eq_mul]; push_cast; field_simp
    rw [this]
    exact mul_mem (inv_mem (IntermediateField.algebraMap_mem _ _))
      (IntermediateField.mem_adjoin_simple_self ℚ θ)
  have hθℚ : IsIntegral ℚ θ := hyi.tower_top
  let B : PowerBasis ℚ E := (IntermediateField.adjoin.powerBasis hθℚ).map
    ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv)
  have hBgen : B.gen = θ := by simp [B]
  have hD := Algebra.discr_isIntegral ℚ (R := ℤ) (b := B.basis) (fun i => by
    rw [B.basis_eq_pow, hBgen]; exact hyi.pow _)
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hD
  refine ⟨⟨θ, hyi⟩, d, ?_, ?_, fun a => ?_⟩
  · rintro rfl
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa using hd.symm)
  · show Algebra.adjoin ℚ {θ} = ⊤
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθℚ.isAlgebraic, hθ]; rfl
  · have hm := Algebra.discr_mul_isIntegral_mem_adjoin ℚ (R := ℤ) (B := B)
      (by rw [hBgen]; exact hyi) a.2
    rw [hBgen, ← hd, Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨g, hg⟩ := hm
    refine ⟨g, Subtype.ext ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hg
    have h1 : ((aeval (⟨θ, hyi⟩ : 𝓞 E) g : 𝓞 E) : E) = aeval θ g :=
      (aeval_algebraMap_apply E (⟨θ, hyi⟩ : 𝓞 E) g).symm
    refine Eq.trans ?_ h1.symm
    rw [hg, algebraMap_smul, zsmul_eq_mul]
    push_cast; rfl

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in
private theorem exists_prime_dvd_eval_not_dvd_of_natDegree_pos (h : ℤ[X]) (hh : 0 < h.natDegree) (M : ℤ)
    (hM : M ≠ 0) : ∃ (n : ℤ) (p : ℕ), p.Prime ∧ (p : ℤ) ∣ h.eval n ∧ ¬ (p : ℤ) ∣ M := by
  set c := h.coeff 0 with hcdef
  by_cases hc : c = 0
  · obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (M.natAbs + 1)
    refine ⟨0, p, hp, ?_, fun hd => ?_⟩
    · rw [← coeff_zero_eq_eval_zero, ← hcdef, hc]; exact dvd_zero _
    · have := Int.natAbs_dvd_natAbs.mpr hd
      simp only [Int.natAbs_natCast] at this
      exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hM) this) (by omega)
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := h)
  rw [← hcdef] at hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero, sub_eq_zero] at hq
    rw [hq, natDegree_C] at hh; exact lt_irrefl _ hh
  set r : ℤ[X] := q.comp (C (c * M) * X) with hr
  set G : ℤ[X] := 1 + C M * X * r with hG
  have hev : ∀ t : ℤ, h.eval (c * M * t) = c * G.eval t := by
    intro t
    have := congrArg (eval (c * M * t)) hq
    simp only [eval_sub, eval_C, eval_mul, eval_X] at this
    simp only [hG, hr, eval_add, eval_one, eval_mul, eval_C, eval_X, eval_comp]
    linear_combination this
  have hr0 : r ≠ 0 := by
    rw [hr, Ne, comp_eq_zero_iff]
    rintro (h0 | ⟨-, h1⟩)
    · exact hq0 h0
    · have := congrArg (coeff · 1) h1
      simp only [coeff_C_mul_X, coeff_C] at this
      simp at this
      exact this.elim hc hM
  have hG1 : G ≠ C 1 := by
    intro h1
    rw [hG, ← C_1, add_eq_left] at h1
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hM) X_ne_zero) hr0 h1
  have hG2 : G ≠ C (-1) := by
    intro h1
    have := congrArg (eval 0) h1
    simp [hG] at this
  have hfin : ({t : ℤ | G.eval t = 1} ∪ {t | G.eval t = -1}).Finite := by
    refine Set.Finite.union ?_ ?_ <;> by_contra hinf
    · exact hG1 (eq_of_infinite_eval_eq G (C 1) (by simpa using hinf))
    · exact hG2 (eq_of_infinite_eval_eq G (C (-1)) (by simpa using hinf))
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at ht
  set g := G.eval t with hg
  have hgabs : g.natAbs ≠ 1 := by
    intro h1
    rcases Int.natAbs_eq_iff.mp h1 with h2 | h2
    · exact ht.1 h2
    · exact ht.2 h2
  have hp := Nat.minFac_prime hgabs
  have hpg : (g.natAbs.minFac : ℤ) ∣ g := Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _)
  refine ⟨c * M * t, g.natAbs.minFac, hp, ?_, fun hpM => ?_⟩
  · rw [hev]; exact Dvd.dvd.mul_left hpg c
  · have hg' : g = 1 + M * (t * r.eval t) := by
      simp only [hg, hG, eval_add, eval_one, eval_mul, eval_C, eval_X]; ring
    have h4 : (1 : ℤ) = g - M * (t * r.eval t) := by rw [hg']; ring
    have : (g.natAbs.minFac : ℤ) ∣ 1 := by
      rw [h4]; exact dvd_sub hpg (Dvd.dvd.mul_right hpM _)
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in
private theorem span_prime_sup_span_proper_of_dvd_norm {E : Type} [Field E] [NumberField E] (x : 𝓞 E)
    (p : ℕ) (hp : p.Prime) (hdvd : (p : ℤ) ∣ Algebra.norm ℤ x) :
    Ideal.span {(p : 𝓞 E)} ⊔ Ideal.span {x} ≠ ⊤ := by
  intro htop
  have h1 : (1 : 𝓞 E) ∈ Ideal.span {(p : 𝓞 E)} ⊔ Ideal.span {x} := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  by_cases hx : x = 0
  · subst hx
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hb
    subst hb
    rw [add_zero] at hab
    have hu : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 E) p)) := by
      rw [map_natCast]; exact (isUnit_iff_exists_inv'.mpr ⟨y, hab⟩).map _
    rw [Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff] at hu
    have := hp.two_le
    rcases hu with h | h <;> omega
  · set I := Ideal.span {x}
    have hcard : Nat.card (𝓞 E ⧸ I) = (Algebra.norm ℤ x).natAbs := by
      rw [← Ideal.absNorm_span_singleton]; exact (Nat.add_zero _).symm
    have hne : (Algebra.norm ℤ x).natAbs ≠ 0 := by
      rw [Int.natAbs_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hx
    haveI : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
    haveI := Fact.mk hp
    have hpc : p ∣ Nat.card (𝓞 E ⧸ I) := by
      rw [hcard]; simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p hpc
    have hpz : (p : 𝓞 E ⧸ I) * z = 0 := by
      rw [← nsmul_eq_mul, ← hz]; exact addOrderOf_nsmul_eq_zero z
    have hunit : (Ideal.Quotient.mk I y) * (p : 𝓞 E ⧸ I) = 1 := by
      have := congrArg (Ideal.Quotient.mk I) hab
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, map_one, map_mul,
        map_natCast] at this
      exact this
    have hz0 : z = 0 := by
      calc z = (Ideal.Quotient.mk I y) * (p : 𝓞 E ⧸ I) * z := by rw [hunit, one_mul]
        _ = 0 := by rw [mul_assoc, hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in

theorem _root_.GlobalTheory.SW.SplitPrime.exists_degree_one {E : Type} [Field E] [NumberField E] (θ : 𝓞 E)
    (hθ : θ ≠ 0) (d : ℤ) (hd : d ≠ 0) (hden : ∀ a : 𝓞 E, ∃ g : ℤ[X], (d : 𝓞 E) * a = aeval θ g)
    (N : ℤ) (hN : N ≠ 0) :
    ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ (N : 𝓞 E) ∉ P ∧
      Function.Surjective (Int.castRingHom (𝓞 E ⧸ P)) := by
  obtain ⟨n, p, hp, hpn, hpM⟩ := exists_prime_dvd_eval_not_dvd_of_natDegree_pos
    (LinearMap.charpoly (Algebra.lmul ℤ (𝓞 E) θ)) (by
      rw [LinearMap.charpoly_natDegree]; exact Module.finrank_pos) (N * d) (mul_ne_zero hN hd)
  have hnorm : (LinearMap.charpoly (Algebra.lmul ℤ (𝓞 E) θ)).eval n =
      Algebra.norm ℤ ((n : 𝓞 E) - θ) := by
    rw [LinearMap.eval_charpoly, Algebra.norm_apply]
    congr 1
    ext x
    simp [Algebra.smul_def, sub_mul]
  rw [hnorm] at hpn
  obtain ⟨P, hP, hJ⟩ := Ideal.exists_le_maximal _ (span_prime_sup_span_proper_of_dvd_norm _ p hp hpn)
  have hpP : (p : 𝓞 E) ∈ P := hJ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hxP : (n : 𝓞 E) - θ ∈ P := hJ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hcop : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → ∃ v : ℤ, (v : 𝓞 E) * k - 1 ∈ P := by
    intro k hk
    obtain ⟨u, v, huv⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hk
    refine ⟨v, ?_⟩
    have : (v : 𝓞 E) * k - 1 = -((u : 𝓞 E) * (p : 𝓞 E)) := by
      have h2 := congrArg (Int.cast : ℤ → 𝓞 E) huv
      push_cast at h2
      linear_combination h2
    rw [this]
    exact P.neg_mem_iff.mpr (P.mul_mem_left _ hpP)
  have hnot : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → (k : 𝓞 E) ∉ P := by
    intro k hk hkP
    obtain ⟨v, hv⟩ := hcop k hk
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := P.sub_mem (P.mul_mem_left (v : 𝓞 E) hkP) hv
      simpa using this))
  refine ⟨P, hP, hnot N (fun h => hpM (Dvd.dvd.mul_right h d)), fun y => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨g, hg⟩ := hden a
  obtain ⟨v, hv⟩ := hcop d (fun h => hpM (Dvd.dvd.mul_left h N))
  refine ⟨v * g.eval n, ?_⟩
  have hθn : Ideal.Quotient.mk P θ = ((n : ℤ) : 𝓞 E ⧸ P) := by
    rw [← map_intCast (Ideal.Quotient.mk P)]
    exact (Ideal.Quotient.eq.mpr (by rw [← P.neg_mem_iff, neg_sub]; exact hxP))
  have hga : Ideal.Quotient.mk P ((d : 𝓞 E) * a) = ((g.eval n : ℤ) : 𝓞 E ⧸ P) := by
    have h3 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ P) θ g
    rw [Ideal.Quotient.mkₐ_eq_mk] at h3
    rw [hg, ← h3, hθn, ← eq_intCast (algebraMap ℤ (𝓞 E ⧸ P)),
      aeval_algebraMap_apply_eq_algebraMap_eval, eq_intCast]
  have hv' : Ideal.Quotient.mk P ((v : 𝓞 E) * d) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk P), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hv
  simp only [eq_intCast, Int.cast_mul]
  rw [← hga, ← map_intCast (Ideal.Quotient.mk P) v, ← map_mul, ← mul_assoc, map_mul, hv', one_mul]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in

theorem _root_.GlobalTheory.SW.SplitPrime.absNorm_prime {E : Type} [Field E] [NumberField E]
    (P : Ideal (𝓞 E)) (hP : P.IsMaximal)
    (hs : Function.Surjective (Int.castRingHom (𝓞 E ⧸ P))) : (Ideal.absNorm P).Prime := by
  letI := Ideal.Quotient.field P
  have hN : Ideal.absNorm P = Nat.card (𝓞 E ⧸ P) := Nat.add_zero _
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ P)
  haveI := hp
  have hp' : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right (by
    rintro rfl
    haveI : CharZero (𝓞 E ⧸ P) := CharP.charP_to_charZero _
    haveI : Infinite (𝓞 E ⧸ P) := Infinite.of_injective _ Nat.cast_injective
    exact not_finite (𝓞 E ⧸ P))
  haveI := Fact.mk hp'
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 E ⧸ P)) := by
    refine ⟨(ZMod.castHom (dvd_refl p) (𝓞 E ⧸ P)).injective, fun y => ?_⟩
    obtain ⟨n, rfl⟩ := hs y
    exact ⟨n, by simp⟩
  rw [hN, ← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_zmod]
  exact hp'

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open Polynomial in

theorem _root_.GlobalTheory.SW.SplitPrime.exists_goodPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (m : ℕ), 0 < m → ∃ (q : ℕ) (P : Ideal (𝓞 E)), _root_.GlobalTheory.SW.GoodPrime m q P := by
  intro E _ _ _ m hm
  obtain ⟨θ, d, hd, hadj, hden⟩ := _root_.GlobalTheory.SW.SplitPrime.exists_prim_den E
  have hcc : ∀ x : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x = IsCMField.complexConj E x := fun x => rfl
  let θc : 𝓞 E := ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E), _root_.GlobalTheory.SW.Base.isIntegral_cc θ.2⟩
  have hβ : θ - θc ≠ 0 := by
    intro h
    have h' : IsCMField.complexConj E (θ : E) = θ := by
      rw [← hcc]; exact (congrArg Subtype.val (sub_eq_zero.mp h)).symm
    have : (((IsCMField.complexConj E).toAlgHom).restrictScalars ℚ) = AlgHom.id ℚ E :=
      AlgHom.ext_of_adjoin_eq_top hadj (by
        intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact h')
    apply IsCMField.complexConj_ne_one E
    ext x
    exact DFunLike.congr_fun this x
  have hθ : θ ≠ 0 := by
    rintro rfl
    apply hβ
    rw [sub_eq_zero]
    apply Subtype.ext
    show (0 : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (0 : E)
    rw [hcc, map_zero]
  set Nv : ℤ := m * (2 * discr E) * Algebra.norm ℤ (θ - θc) with hNv
  have hNv0 : Nv ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hm.ne')
      (mul_ne_zero two_ne_zero (discr_ne_zero E))) ?_
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hβ
  obtain ⟨P, hP, hNP, hs⟩ := _root_.GlobalTheory.SW.SplitPrime.exists_degree_one θ hθ d hd hden Nv hNv0
  have hq := _root_.GlobalTheory.SW.SplitPrime.absNorm_prime P hP hs
  have hqN : ¬ ((Ideal.absNorm P : ℕ) : ℤ) ∣ Nv := by
    rintro ⟨k, hk⟩
    apply hNP
    rw [hk, Int.cast_mul, Int.cast_natCast]
    exact P.mul_mem_right _ (Ideal.absNorm_mem P)
  refine ⟨Ideal.absNorm P, P, ?_⟩
  unfold _root_.GlobalTheory.SW.GoodPrime
  refine ⟨hq, ?_, rfl, ?_, fun h => hqN ?_⟩
  · refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => hqN ?_)).symm
    rw [hNv, mul_assoc]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr h) _
  · rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have hle : _root_.GlobalTheory.SW.conjI P ≤ P := by
      have := hP.eq_of_le hne le_sup_left
      exact le_sup_right.trans this.symm.le
    obtain ⟨n0, hn0⟩ := hs (Ideal.Quotient.mk P θ)
    have h1 : θ - (n0 : 𝓞 E) ∈ P := by
      rw [← Ideal.Quotient.eq, ← hn0, eq_intCast, map_intCast]
    have h2 : θc - (n0 : 𝓞 E) ∈ P := by
      apply hle
      unfold _root_.GlobalTheory.SW.conjI
      apply Ideal.subset_span
      refine ⟨θ - (n0 : 𝓞 E), h1, ?_⟩
      change ((θc : E) - ((n0 : 𝓞 E) : E)) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((θ : E) - ((n0 : 𝓞 E) : E))
      have hn : ((n0 : 𝓞 E) : E) = (n0 : E) := by push_cast; rfl
      rw [hn, hcc, map_sub, map_intCast]
      rfl
    have h3 : θ - θc ∈ P := by
      have := P.sub_mem h1 h2
      rwa [sub_sub_sub_cancel_right] at this
    have h4 : ((Algebra.norm ℤ (θ - θc) : ℤ) : 𝓞 E) ∈ P := by
      have h5 : (((Algebra.norm ℤ (θ - θc)).natAbs : ℕ) : 𝓞 E) ∈ P := by
        have := Ideal.absNorm_mem (Ideal.span {θ - θc})
        rw [Ideal.absNorm_span_singleton] at this
        exact (Ideal.span_singleton_le_iff_mem P).mpr h3 this
      rcases Int.natAbs_eq (Algebra.norm ℤ (θ - θc)) with h6 | h6
      · rw [h6, Int.cast_natCast]; exact h5
      · rw [h6, Int.cast_neg, Int.cast_natCast]; exact P.neg_mem h5
    apply hNP
    rw [hNv, Int.cast_mul]
    exact P.mul_mem_left _ h4
  · rw [hNv, mul_comm (m : ℤ), mul_assoc]
    exact Dvd.dvd.mul_right h _

end GlobalTheory.SW.SplitPrime
