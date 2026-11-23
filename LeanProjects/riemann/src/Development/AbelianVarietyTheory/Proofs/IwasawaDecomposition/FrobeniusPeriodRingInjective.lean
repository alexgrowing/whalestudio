import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientCompleteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIffStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanPairPowSucc

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.FrobInj

section Pair
variable {R : Type} [CommRing R] (p w : R)

theorem mem_pow_succ (k : ℕ) (x : R) (hx : x ∈ Ideal.span {p, w} ^ (k + 1)) :
    ∃ c G, G ∈ Ideal.span {p, w} ^ k ∧ x = w ^ (k + 1) * c + p * G := by
  first
  | exact @_root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ
  | exact _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ
  | (apply _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ ..)

theorem pow_mem (k : ℕ) : w ^ k ∈ Ideal.span {p, w} ^ k :=
  Ideal.pow_mem_pow (Ideal.subset_span (by simp)) k

theorem pow_mem' (k : ℕ) : p ^ k ∈ Ideal.span {p, w} ^ k :=
  Ideal.pow_mem_pow (Ideal.subset_span (by simp)) k

variable {p w} (hp : ∀ x : R, p * x = 0 → x = 0) (hw : ∀ b : R, p ∣ w * b → p ∣ b)

include hw in
theorem dvd_of_pow (k : ℕ) (b : R) (h : p ∣ w ^ k * b) : p ∣ b := by
  induction k with
  | zero => simpa using h
  | succ k ih => exact ih (hw _ (by rwa [← mul_assoc, ← pow_succ']))

include hp hw in
theorem sat (k : ℕ) (x : R) (hx : p * x ∈ Ideal.span {p, w} ^ (k + 1)) : x ∈ Ideal.span {p, w} ^ k := by
  obtain ⟨c, G, hG, e⟩ := mem_pow_succ p w k _ hx
  obtain ⟨d, rfl⟩ := dvd_of_pow hw (k + 1) c ⟨x - G, by linear_combination -e⟩
  have : x = w ^ k * (w * d) + G := sub_eq_zero.1 (hp _ (by linear_combination e))
  rw [this]
  exact add_mem (Ideal.mul_mem_right _ _ (pow_mem p w k)) hG

include hp hw in

theorem coeff_mem (l r : ℕ) (a F : ℕ → R) (hF : ∀ N, F (N + 1) = a N * w ^ (l * N) + p * F N)
    (N : ℕ) (b : R) (h : b * w ^ (l * N) + F N ∈ Ideal.span {p, w} ^ (N + r)) :
    ∀ i < N, l * (i + 1) ≤ i + r + 1 → a i ∈ Ideal.span {p, w ^ l} := by
  induction N generalizing b with
  | zero => intro i hi; omega
  | succ N ih =>
    have e0 : b * w ^ (l * (N + 1)) + F (N + 1) = (b * w ^ l + a N) * w ^ (l * N) + p * F N := by
      rw [hF]; ring
    rw [e0, show N + 1 + r = N + r + 1 by ring] at h
    by_cases hc : N + r + 1 ≤ l * N
    · have h1 : (b * w ^ l + a N) * w ^ (l * N) ∈ Ideal.span {p, w} ^ (N + r + 1) :=
        Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hc (pow_mem p w _))
      have h2 := sat hp hw _ _ ((Ideal.add_mem_iff_right _ h1).1 h)
      intro i hi hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih 0 (by simpa using h2) i hi hl
      · have : l = 0 := by
          rw [Nat.mul_succ] at hl
          omega
        subst this
        omega
    · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (not_le.1 hc).le
      obtain ⟨c, G, hG, e1⟩ := mem_pow_succ p w _ _ h
      rw [he, pow_add] at e1
      obtain ⟨d, hd⟩ := dvd_of_pow hw (l * N) (b * w ^ l + a N - w ^ e * c)
        ⟨G - F N, by linear_combination e1⟩
      have h2 : d * w ^ (l * N) + F N = G :=
        sub_eq_zero.1 (hp _ (by linear_combination e1 - w ^ (l * N) * hd))
      intro i hi hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih d (h2 ▸ hG) i hi hl
      · obtain ⟨e', rfl⟩ : ∃ e', e = l + e' := Nat.exists_eq_add_of_le (by
          rw [Nat.mul_succ] at hl
          omega)
        exact Ideal.mem_span_pair.2 ⟨d, w ^ e' * c - b, by linear_combination -hd⟩

end Pair

section Loc
variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {p w : R} {q : K}
  (hq : algebraMap R K p * q = 1)

include hq in
theorem clear_den (v : K) (hv : v ∈ Algebra.adjoin R {algebraMap R K w * q}) :
    ∃ N : ℕ, ∃ c ∈ Ideal.span {p, w} ^ N, algebraMap R K p ^ N * v = algebraMap R K c := by
  induction hv using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨1, w, by simpa using pow_mem p w 1, by linear_combination (algebraMap R K w) * hq⟩
  | algebraMap r => exact ⟨0, r, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, c, hc, e⟩ := hx
    obtain ⟨N', c', hc', e'⟩ := hy
    refine ⟨N + N', c * p ^ N' + p ^ N * c', ?_, ?_⟩
    · rw [pow_add]
      exact add_mem (Ideal.mul_mem_mul hc (pow_mem' p w N')) (Ideal.mul_mem_mul (pow_mem' p w N) hc')
    · simp only [map_add, map_mul, map_pow, ← e, ← e']; ring
  | mul x y _ _ hx hy =>
    obtain ⟨N, c, hc, e⟩ := hx
    obtain ⟨N', c', hc', e'⟩ := hy
    refine ⟨N + N', c * c', ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul hc hc'
    · simp only [map_mul, ← e, ← e']; ring

variable (hp : ∀ x : R, p * x = 0 → x = 0) (hw : ∀ b : R, p ∣ w * b → p ∣ b)
  (hinj : Function.Injective (algebraMap R K)) (l : ℕ) (φ : R →+* R) (hφ : Function.Bijective φ)
  (hφp : φ p = p) (hφw : φ w = w ^ l) (ψ : K →+* K) (hψ : ∀ a, ψ (algebraMap R K a) = algebraMap R K (φ a))

include hq hp hw hinj hφ hφp hφw hψ in
theorem coeff_mem_of_frob (h : Polynomial R) (i : ℕ) (v : K) (hv : v ∈ Algebra.adjoin R {algebraMap R K w * q})
    (e : ψ (Polynomial.aeval (algebraMap R K w * q) h) = algebraMap R K p ^ (l * (i + 1) + 1) * v) :
    h.coeff i ∈ Ideal.span {p, w} := by
  set P := algebraMap R K p with hP
  have hψq : ψ q = q := by
    have := congrArg ψ hq
    rw [map_mul, hP, hψ, hφp, map_one, ← hP] at this
    linear_combination q * this - ψ q * hq
  let F : ℕ → R := fun N => Nat.rec 0 (fun N x => φ (h.coeff N) * w ^ (l * N) + p * x) N
  have hF : ∀ N, F (N + 1) = φ (h.coeff N) * w ^ (l * N) + p * F N := fun N => rfl
  have hFK : ∀ N, algebraMap R K (F N) * P =
      P ^ N * ψ (∑ j ∈ Finset.range N, h.coeff j • (algebraMap R K w * q) ^ j) := by
    intro N
    induction N with
    | zero => simp [F]
    | succ N ih =>
      have : P ^ N * q ^ N = 1 := by rw [← mul_pow, hq, one_pow]
      rw [hF, Finset.sum_range_succ, map_add ψ, Algebra.smul_def, map_mul ψ, map_pow ψ, map_mul ψ, hψ, hψ, hψq,
        hφw, map_add, map_mul, map_mul, map_pow, map_pow, ← hP, mul_pow, ← pow_mul]
      linear_combination P * ih - P * algebraMap R K (φ (h.coeff N)) * algebraMap R K w ^ (l * N) * this
  obtain ⟨N0, c, hc, ec⟩ := clear_den hq v hv
  have h1 := hFK (N0 + (h.natDegree + i + 1))
  rw [← Polynomial.aeval_eq_sum_range' (by omega), e] at h1
  have h2 : F (N0 + (h.natDegree + i + 1)) = c * p ^ (h.natDegree + i + 1 + l * (i + 1)) := by
    apply hinj
    rw [map_mul, map_pow, ← ec, ← hP]
    linear_combination q * h1 - (algebraMap R K (F (N0 + (h.natDegree + i + 1))) -
      P ^ N0 * v * P ^ (h.natDegree + i + 1 + l * (i + 1))) * hq
  have h3 := coeff_mem hp hw l (l * (i + 1)) (fun j => φ (h.coeff j)) F hF (N0 + (h.natDegree + i + 1)) 0
    (by
      rw [zero_mul, zero_add, h2, add_assoc, pow_add _ N0]
      exact Ideal.mul_mem_mul hc (pow_mem' p w _)) i (by omega) (by omega)
  obtain ⟨α, β, h4⟩ := Ideal.mem_span_pair.1 h3
  obtain ⟨α, rfl⟩ := hφ.2 α
  obtain ⟨β, rfl⟩ := hφ.2 β
  exact Ideal.mem_span_pair.2 ⟨α, β, hφ.1 (by rw [map_add, map_mul, map_mul, hφp, hφw, h4])⟩

include hq hp hw hinj hφ hφp hφw hψ in
theorem dvd_of_frob (t : K) (ht : t ∈ Algebra.adjoin R {algebraMap R K w * q})
    (H : ∀ r : ℕ, ∃ u ∈ Algebra.adjoin R {algebraMap R K w * q}, ∃ v ∈ Algebra.adjoin R {algebraMap R K w * q},
      ψ (t + algebraMap R K p * u) = algebraMap R K p ^ r * v) :
    ∃ m ∈ Algebra.adjoin R {algebraMap R K w * q}, t = algebraMap R K p * m := by
  have hZ : algebraMap R K w * q ∈ Algebra.adjoin R {algebraMap R K w * q} := Algebra.subset_adjoin rfl
  have ht' := ht
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ht'
  obtain ⟨f, rfl⟩ := ht'
  have hf : ∀ i, f.coeff i ∈ Ideal.span {p, w} := by
    intro i
    obtain ⟨u, hu, v, hv, e⟩ := H (l * (i + 1) + 1)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hu
    obtain ⟨g, rfl⟩ := hu
    have := coeff_mem_of_frob hq hp hw hinj l φ hφ hφp hφw ψ hψ (f + Polynomial.C p * g) i v hv
      (by rw [← e]; simp)
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul] at this
    exact (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))).1 this
  change ∃ m ∈ _, Polynomial.aeval _ f = _
  rw [Polynomial.aeval_eq_sum_range]
  refine Finset.sum_induction _ (fun t => ∃ m ∈ Algebra.adjoin R {algebraMap R K w * q},
    t = algebraMap R K p * m) ?_ ⟨0, zero_mem _, by simp⟩ ?_
  · rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', add_mem hm hm', by ring⟩
  · intro i _
    obtain ⟨α, β, h4⟩ := Ideal.mem_span_pair.1 (hf i)
    refine ⟨(algebraMap R K α + algebraMap R K β * (algebraMap R K w * q)) * (algebraMap R K w * q) ^ i,
      mul_mem (add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) hZ))
        (_root_.pow_mem hZ i), ?_⟩
    rw [Algebra.smul_def, ← h4, map_add, map_mul, map_mul]
    linear_combination -(algebraMap R K β * algebraMap R K w * (algebraMap R K w * q) ^ i) * hq

include hq hp hw hinj hφ hφp hφw hψ in
theorem pow_dvd_of_frob (k : ℕ) (t : K) (ht : t ∈ Algebra.adjoin R {algebraMap R K w * q})
    (H : ∀ r : ℕ, ∃ u ∈ Algebra.adjoin R {algebraMap R K w * q}, ∃ v ∈ Algebra.adjoin R {algebraMap R K w * q},
      ψ (t + algebraMap R K p ^ k * u) = algebraMap R K p ^ r * v) :
    ∃ m ∈ Algebra.adjoin R {algebraMap R K w * q}, t = algebraMap R K p ^ k * m := by
  induction k with
  | zero => exact ⟨t, ht, by simp⟩
  | succ k ih =>
    obtain ⟨t', ht', rfl⟩ := ih fun r => by
      obtain ⟨u, hu, v, hv, e⟩ := H r
      exact ⟨algebraMap R K p * u, mul_mem (Subalgebra.algebraMap_mem _ _) hu, v, hv,
        by rw [← e, pow_succ, mul_assoc]⟩
    obtain ⟨m, hm, rfl⟩ := dvd_of_frob hq hp hw hinj l φ hφ hφp hφw ψ hψ t' ht' fun r => by
      obtain ⟨u, hu, v, hv, e⟩ := H (k + r)
      refine ⟨u, hu, v, hv, ?_⟩
      have : algebraMap R K p ^ k * q ^ k = 1 := by rw [← mul_pow, hq, one_pow]
      simp only [map_add, map_mul, map_pow, hψ, hφp] at e ⊢
      linear_combination q ^ k * e - (ψ t' + algebraMap R K p * ψ u - algebraMap R K p ^ r * v) * this
    exact ⟨m, hm, by ring⟩

include hq in

theorem bounded_mod (x : R) (n : ℕ) (m : K) (hm : m ∈ Algebra.adjoin R {algebraMap R K x * q}) :
    ∃ (a : R) (z : K), algebraMap R K p ^ n * m = algebraMap R K a + algebraMap R K x ^ n * z := by
  induction n generalizing m with
  | zero => exact ⟨0, m, by simp⟩
  | succ n ih =>
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨f, rfl⟩ := hm
    obtain ⟨a, z, e⟩ := ih (Polynomial.aeval (algebraMap R K x * q) f.divX)
      (Polynomial.aeval_mem_adjoin_singleton _ _)
    refine ⟨p ^ (n + 1) * f.coeff 0 + x * a, z, ?_⟩
    have h := congrArg (Polynomial.aeval (algebraMap R K x * q)) (Polynomial.divX_mul_X_add f)
    change _ * Polynomial.aeval _ f = _
    rw [← h]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination algebraMap R K x * e + algebraMap R K x * algebraMap R K p ^ n *
      Polynomial.aeval (algebraMap R K x * q) f.divX * hq

theorem dividedPower_mem {P f y : K} (hP : P * q = 1) (x a c : R) (n : ℕ) (hf : IsUnit f)
    (hc : f * algebraMap R K c = P ^ n) (hy : f * y = algebraMap R K (x * a) ^ n) :
    y ∈ Algebra.adjoin R {algebraMap R K x * q} := by
  have h1 : P ^ n * q ^ n = 1 := by rw [← mul_pow, hP, one_pow]
  have key : y = algebraMap R K c * (algebraMap R K a * (algebraMap R K x * q)) ^ n := by
    apply hf.mul_left_cancel
    rw [← mul_assoc, hc, hy, map_mul, mul_pow, mul_pow, mul_pow]
    linear_combination -(algebraMap R K x ^ n * algebraMap R K a ^ n) * h1
  rw [key]
  have hZ : algebraMap R K x * q ∈ Algebra.adjoin R {algebraMap R K x * q} := Algebra.subset_adjoin rfl
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) (Subalgebra.pow_mem _ ?_ n)
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) hZ

end Loc

end GlobalTheory.FrobInj

namespace GlobalTheory.MemLoc.PhiInj

variable (l : ℕ) [Fact l.Prime]

theorem exists_eps : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem φA_bijective : Function.Bijective (Per.φA l) := by
  have h : (Per.φA l : Per.Ainf l → Per.Ainf l) = WittVector.map (frobenius (Per.Fl l) l) := by
    funext w
    apply WittVector.ext
    intro n
    rw [GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff, frobenius_def]
  rw [h]
  exact ⟨WittVector.map_injective _ (frobeniusEquiv (Per.Fl l) l).injective,
    WittVector.map_surjective _ (frobeniusEquiv (Per.Fl l) l).surjective⟩

theorem exists_teich (x : Per.Ainf l) : ∃ w u : Per.Ainf l, x = w + (l : Per.Ainf l) * u ∧ Per.φA l w = w ^ l := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by
    ext i
    simp
  rw [hI, Finset.sum_singleton] at h0
  obtain ⟨u, hu⟩ : (l : Per.Ainf l) ∣ x - Per.tm (x.coeff 0) := by simpa using h0
  refine ⟨Per.tm (x.coeff 0), u, by rw [← hu]; ring, ?_⟩
  rw [GlobalTheory.RingIface.phiA_teich, map_pow]

theorem acris0_le {e : Per.Fl l} (he : IsEps e) {q : Per.AinfP l} (hq : (l : Per.AinfP l) * q = 1)
    (s : Per.Acris0 l) :
    (s : Per.AinfP l) ∈ Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q} := by
  have H : Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
        ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} ≤
      Subalgebra.toSubmodule
        (Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q}) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨n, hn⟩
    obtain ⟨c, hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
    have h := congrArg (fun z => algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l z)) hc
    simp only [map_mul, map_natCast, map_pow] at h
    have h' : ((n.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c) =
        (l : Per.AinfP l) ^ n := h
    exact GlobalTheory.FrobInj.dividedPower_mem hq (xi e) 1 (Per.zA l c) n
      (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero) h' (by rw [mul_one]; exact hn)
  exact H ((GlobalTheory.T.acris_membership_span_iff l e he s).1 s.2)

noncomputable def phi0 : Per.Acris0 l →+* Per.Acris0 l :=
  (Per.extP (Per.φA l)).restrict _ _ (GlobalTheory.CrisMaps.frob_extends l).mem

theorem coe_phi0 (s : Per.Acris0 l) : (phi0 l s : Per.AinfP l) = Per.extP (Per.φA l) s := rfl

theorem phiA_of (s : Per.Acris0 l) : phiA l (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
    algebraMap (Per.Acris0 l) (Per.Acris l) (phi0 l s) :=
  (GlobalTheory.CrisMaps.phiA_extends l).env s

theorem ev_alg (n : ℕ) (x : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
  GlobalTheory.RingIface.ev_alg l n x

theorem eq_zero_of_ev (y : Per.BdRp l) (h : ∀ n, Per.ev l n y = Per.ev l n 0) : y = 0 :=
  GlobalTheory.RingIface.ev_ext l y 0 h

theorem mem_kerP (x : Per.Ainf l) (hx : Per.θ l x = 0) :
    algebraMap (Per.Ainf l) (Per.AinfP l) x ∈ Per.kerP l :=
  GlobalTheory.RingIface.alg_mem_kerP l hx

theorem φB_alg (x : Per.Acris l) : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) =
    algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  GlobalTheory.CrisMaps.φB_phiA l x

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem approx_mem {e : Per.Fl l} (he : IsEps e) {q : Per.AinfP l} (hq : (l : Per.AinfP l) * q = 1)
    (x : Per.Acris l) (hx : phiA l x = 0) (k : ℕ) (s : Per.Acris0 l) (z : Per.Acris l)
    (hs : x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ k * z) :
    ∃ m ∈ Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q},
      (s : Per.AinfP l) = (l : Per.AinfP l) ^ k * m := by
  obtain ⟨hd, -, hinj⟩ := ainf_isDomain_and_injective l
  obtain ⟨-, -, hdense, hdvd⟩ := acris_basic l
  obtain ⟨w, u, hw, hφw⟩ := exists_teich l (xi e)
  have hq' : algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l) * q = 1 := by rwa [map_natCast]
  have hp : ∀ a : Per.Ainf l, (l : Per.Ainf l) * a = 0 → a = 0 := by
    intro a ha
    apply hinj
    have := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) ha
    rw [map_mul, map_zero] at this
    rw [map_zero]
    linear_combination q * this - algebraMap (Per.Ainf l) (Per.AinfP l) a * hq'
  have hsat : ∀ a : Per.Ainf l, xi e ∣ (l : Per.Ainf l) * a → xi e ∣ a := by
    simpa using (GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he 1).1
  have hx0 : xi e ≠ 0 := by
    intro h
    have h1 := (theta_eq_zero_iff_xi_dvd l e he (mu e)).1 (by
      rw [mu, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self])
    rw [h, zero_dvd_iff, mu, sub_eq_zero] at h1
    have h2 : e = 1 := by simpa using congrArg (fun y : Per.Ainf l => y.coeff 0) h1
    apply he.2
    rw [h2, map_one, map_one]
  have hreg : ∀ b : Per.Ainf l, (l : Per.Ainf l) ∣ w * b → (l : Per.Ainf l) ∣ b := by
    rintro b ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hsat (c + u * b) ⟨b, by linear_combination -hc - b * hw⟩
    exact ⟨d, mul_left_cancel₀ hx0 (by linear_combination hc + b * hw + (l : Per.Ainf l) * hd)⟩
  have hZ : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q =
      algebraMap (Per.Ainf l) (Per.AinfP l) w * q + algebraMap (Per.Ainf l) (Per.AinfP l) u := by
    rw [hw, map_add, map_mul]
    linear_combination algebraMap (Per.Ainf l) (Per.AinfP l) u * hq'
  have hM : Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) * q} =
      Algebra.adjoin (Per.Ainf l) {algebraMap (Per.Ainf l) (Per.AinfP l) w * q} := by
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
    · rintro _ rfl
      rw [hZ]
      exact add_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)
    · rintro _ rfl
      rw [← sub_eq_iff_eq_add.2 hZ]
      exact sub_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)
  have hle := acris0_le l he hq
  rw [hM] at hle ⊢
  have := GlobalTheory.FrobInj.pow_dvd_of_frob hq' hp hreg hinj l (Per.φA l) (φA_bijective l) (map_natCast _ _) hφw
    (Per.extP (Per.φA l)) (GlobalTheory.RingBasics.awayMap_algebraMap₂ _) k s (hle s) (fun r => by
      obtain ⟨s', z', rfl⟩ := hdense z r
      have h1 : (l : Per.Acris l) ^ r ∣
          algebraMap (Per.Acris0 l) (Per.Acris l) (phi0 l (s + (l : Per.Acris0 l) ^ k * s')) := by
        refine ⟨-((l : Per.Acris l) ^ k * phiA l z'), ?_⟩
        rw [hs] at hx
        rw [← phiA_of]
        simp only [map_add, map_mul, map_pow, map_natCast] at hx ⊢
        linear_combination hx
      obtain ⟨v, hv⟩ := (hdvd _ _).1 h1
      refine ⟨s', hle s', v, hle v, ?_⟩
      have h2 := congrArg Subtype.val hv
      rw [coe_phi0] at h2
      rw [map_natCast]
      simpa using h2)
  rwa [map_natCast] at this

theorem phiA_injective : Function.Injective (phiA l) := by
  obtain ⟨e, he⟩ := exists_eps l
  obtain ⟨q, hq⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  have hq' : algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l) * q = 1 := by rwa [map_natCast]
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_canonical_acris_to_bdRPlus l
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply GlobalTheory.T.acrisToBdRPlus_injective l j hj
  rw [map_zero]
  refine eq_zero_of_ev l _ fun n => (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n x 0 fun r => ?_
  obtain ⟨s, z, hs⟩ := (acris_basic l).2.2.1 x (r + n)
  obtain ⟨m, hm, e1⟩ := approx_mem l he hq x hx (r + n) s z hs
  obtain ⟨a, y, e2⟩ := GlobalTheory.FrobInj.bounded_mod hq' (xi e) n m hm
  refine ⟨s, (l : Per.Acris l) ^ n * z, -a, by rw [hs]; ring, ?_⟩
  have e3 : ((l : Per.BdRp l) ^ r * aDp l (-a)) = algebraMap (Per.AinfP l) (Per.BdRp l)
      ((l : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) (-a)) := by
    rw [map_mul, map_pow, map_natCast]
    rfl
  rw [e3, zero_sub, ← map_neg, ev_alg, ev_alg, Ideal.Quotient.eq]
  have e4 : -(s : Per.AinfP l) - (l : Per.AinfP l) ^ r * algebraMap (Per.Ainf l) (Per.AinfP l) (-a) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n * (-((l : Per.AinfP l) ^ r * y)) := by
    rw [map_natCast] at e2
    rw [e1, map_neg]
    linear_combination -(l : Per.AinfP l) ^ r * e2
  rw [e4]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow
    (mem_kerP l _ ((theta_eq_zero_iff_xi_dvd l e he _).2 dvd_rfl)) n)

theorem algebraMap_acris_bcris_injective : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_canonical_acris_to_bdRPlus l
  obtain ⟨ι, hι, -⟩ := GlobalTheory.T.exists_injective_bcris_to_bdR l j hj
  intro x y h
  apply GlobalTheory.T.acrisToBdRPlus_injective l j hj
  apply (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1
  rw [← hι, ← hι, h]

theorem φB_inj : Function.Injective (Per.φB l) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, x, h⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne b
  have h1 := congrArg (Per.φB l) h
  rw [map_mul, hb, zero_mul, φB_alg, ← map_zero (algebraMap (Per.Acris l) (Per.Bcris l)),
    ← map_zero (phiA l)] at h1
  have h2 := phiA_injective l (algebraMap_acris_bcris_injective l h1)
  rw [← h2, map_zero] at h
  exact ((GlobalTheory.CrisLoc.unit_of_root l e he hne).pow n).mul_left_eq_zero.1 h

end

end GlobalTheory.MemLoc.PhiInj

theorem GlobalTheory.MemLoc.phiB_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (Per.φB l) :=
  fun l _ => GlobalTheory.MemLoc.PhiInj.φB_inj l
