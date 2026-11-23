import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcSp

section Witt

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]

theorem coeff_iterate_verschiebung (m : ℕ) (y : WittVector p R) (i : ℕ) (h : i < m) :
    (WittVector.verschiebung^[m] y).coeff i = 0 := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ i =>
      rw [WittVector.verschiebung_coeff_succ]
      exact ih i (by omega)

theorem idem_eq_zero (u : WittVector p R) (hu : u * u = u) (h0 : u.coeff 0 = 0) : u = 0 := by
  have key : ∀ n, ∀ i < n + 1, u.coeff i = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0
    | succ n ih =>
      intro i hi
      by_cases h : i < n + 1
      · exact ih i h
      obtain rfl : i = n + 1 := by omega
      obtain ⟨y, e⟩ : ∃ y, u = WittVector.verschiebung^[n + 1] y := ⟨_, WittVector.eq_iterate_verschiebung ih⟩
      have e2 : u = WittVector.verschiebung^[(n + 1) + (n + 1)]
          (WittVector.frobenius^[n + 1] y * WittVector.frobenius^[n + 1] y) := by
        rw [← WittVector.iterate_verschiebung_mul, ← e, hu]
      rw [e2]
      exact coeff_iterate_verschiebung _ _ _ (by omega)
  ext i
  rw [key i i (by omega)]
  simp

theorem sum_teichmuller {ι : Type} [Fintype ι] (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller p (e i) = (1 : WittVector p R) := by
  have ho : OrthogonalIdempotents fun i => WittVector.teichmuller p (e i) :=
    { idem := fun i => by
        change _ * _ = _
        rw [← map_mul, (he.idem i).eq]
      ortho := fun i j hij => by
        change _ * _ = _
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hs : IsIdempotentElem (∑ i, WittVector.teichmuller p (e i)) := ho.isIdempotentElem_sum
  have h1 : (1 : WittVector p R) - ∑ i, WittVector.teichmuller p (e i) = 0 := by
    refine idem_eq_zero _ hs.one_sub.eq ?_
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  exact (sub_eq_zero.1 h1).symm

end Witt

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem sum_teich {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller l (e i) = (1 : A.W) := by
  rcases subsingleton_or_nontrivial A.A with h | h
  · exact WittVector.ext fun _ => Subsingleton.elim _ _
  · haveI : CharP A.A l := (CharP.charP_iff_prime_eq_zero Fact.out).2 A.natCast_l
    exact sum_teichmuller e he

theorem acr_ext {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) {x y : A.Acr n}
    (h : ∀ i, A.toAcr n (WittVector.teichmuller l (e i)) * x = A.toAcr n (WittVector.teichmuller l (e i)) * y) :
    x = y := by
  have hs : ∑ i, A.toAcr n (WittVector.teichmuller l (e i)) = 1 := by
    rw [← map_sum, sum_teich A e he, map_one]
  calc x = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * x := by rw [hs, one_mul]
    _ = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * y := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => h i
    _ = y := by rw [hs, one_mul]

theorem exists_cast : ∃ c : ZMod (l ^ n) →+* A.Acr n, ∀ a, c a = (a.val : A.Acr n) := by
  haveI : CharP (A.Acr n) (ringChar (A.Acr n)) := ringChar.charP _
  have hd : ringChar (A.Acr n) ∣ l ^ n :=
    (CharP.cast_eq_zero_iff (A.Acr n) (ringChar (A.Acr n)) (l ^ n)).1 (by
      rw [Nat.cast_pow]
      exact A.pow_l_acr n)
  refine ⟨ZMod.castHom hd _, fun a => ?_⟩
  rw [ZMod.castHom_apply, ZMod.natCast_val]

variable {A n}

section Main

variable (hI : LcIdem) (H : RIn l) (hA : A.IsTest)
include hI H hA

theorem exists_isLcA (f : LocallyConstant (SU A) (ZMod (l ^ n))) : ∃ x, IsLcA A n f x := by
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine ⟨∑ a, A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n), fun e' a he' hf => ?_⟩
  have h3 : e' * e a = e' := h2 e' a he' hf
  rw [Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, h3]
  · intro b _ hb
    have h4 : e' * e b = 0 := by
      calc e' * e b = e' * e a * e b := by rw [h3]
        _ = 0 := by rw [mul_assoc, he.ortho hb.symm, mul_zero]
    rw [← mul_assoc, ← map_mul, ← map_mul, h4, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isLcA_unique {f : LocallyConstant (SU A) (ZMod (l ^ n))} {x y : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n f y) : x = y := by
  obtain ⟨e, he, h1, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine acr_ext A n e he fun a => ?_
  have hf : ∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal → f p = a :=
    fun p hp => (h1 a p).1 hp
  rw [hx (e a) a (he.idem a) hf, hy (e a) a (he.idem a) hf]

theorem isLcA_one : IsLcA A n 1 1 := by
  obtain ⟨c, hc⟩ := exists_cast A n
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) 1
  intro e' a he' hf
  by_cases ha : a = 1
  · subst ha
    rw [← hc, map_one]
  · have h3 : e' * e a = e' := h2 e' a he' hf
    have h4 : e' * e 1 = e' := h2 e' 1 he' fun _ _ => rfl
    have h5 : e' = 0 := by
      calc e' = e' * e 1 * e a := by rw [h4, h3]
        _ = 0 := by rw [mul_assoc, he.ortho (Ne.symm ha), mul_zero]
    rw [h5, WittVector.teichmuller_zero, map_zero, zero_mul, zero_mul]

theorem exists_pair (f g : LocallyConstant (SU A) (ZMod (l ^ n))) :
    ∃ e : ZMod (l ^ n) × ZMod (l ^ n) → A.A, CompleteOrthogonalIdempotents e ∧
      ∀ (ab : ZMod (l ^ n) × ZMod (l ^ n)) (p : PrimeSpectrum A.Ug),
        algebraMap A.U A.Ug (A.sharp (e ab)) ∉ p.asIdeal → f p = ab.1 ∧ g p = ab.2 := by
  let h : LocallyConstant (SU A) (ZMod (l ^ n) × ZMod (l ^ n)) :=
    ⟨fun p => (f p, g p), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨e, he, h1, -⟩ := hI l H A hA _ h
  refine ⟨e, he, fun ab p hp => ?_⟩
  have h2 : (f p, g p) = ab := (h1 ab p).1 hp
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem isLcA_add {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f + g) z) : z = x + y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 + ab.2) (he.idem ab) fun p hp => by
    change f p + g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  rw [h3, mul_add, h1, h2, ← hc, ← hc, ← hc, map_add, mul_add]

theorem isLcA_mul {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f * g) z) : z = x * y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 * ab.2) (he.idem ab) fun p hp => by
    change f p * g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  have ht : A.toAcr n (WittVector.teichmuller l (e ab)) * A.toAcr n (WittVector.teichmuller l (e ab)) =
      A.toAcr n (WittVector.teichmuller l (e ab)) := by
    rw [← map_mul, ← map_mul, (he.idem ab).eq]
  rw [← hc] at h1 h2 h3
  calc _ = A.toAcr n (WittVector.teichmuller l (e ab)) * (c ab.1 * c ab.2) := by rw [h3, map_mul]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.1) * (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.2) := by
      rw [mul_mul_mul_comm, ht]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * x) * (A.toAcr n (WittVector.teichmuller l (e ab)) * y) := by
      rw [h1, h2]
    _ = _ := by rw [mul_mul_mul_comm, ht]

end Main

theorem lcSpec_of_lcIdem : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec := by
  intro hI l _ H A hA n
  have P : ∃ κ : LocallyConstant (SU A) (ZMod (l ^ n)) →+ A.Acr n, ∀ f, IsLcA A n f (κ f) := by
    choose k hk using exists_isLcA (n := n) hI H hA
    exact ⟨AddMonoidHom.mk' k fun f g => isLcA_add hI H hA (hk f) (hk g) (hk (f + g)), hk⟩
  have S : ∀ f, IsLcA A n f (lcA A n f) := pick_spec P
  refine ⟨S, isLcA_unique hI H hA (S 1) (isLcA_one hI H hA),
    fun f g => isLcA_mul hI H hA (S f) (S g) (S (f * g)), fun f e he h => ?_⟩
  refine acr_ext A n e he fun a => ?_
  rw [S f (e a) a (he.idem a) (h a), Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, (he.idem a).eq]
  · intro b _ hb
    rw [← mul_assoc, ← map_mul, ← map_mul, he.ortho hb.symm, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

end GlobalTheory.CompanionTheory.LcSp
