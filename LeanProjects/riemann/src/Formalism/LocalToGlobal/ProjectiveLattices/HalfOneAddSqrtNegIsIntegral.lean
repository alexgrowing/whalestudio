import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions
open scoped Pointwise

instance instCMFieldHost (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

theorem sqrtMinusD_isIntegral (D : D7) : IsIntegral ℤ D.host.sqrtMinusD :=
  ⟨Polynomial.X ^ 2 + Polynomial.C (D.host.d : ℤ), by monicity!, by
    simp [Polynomial.eval₂_add, D.host.sqrtMinusD_sq]⟩

def rtE (D : D7) : 𝓞 D.host.E := ⟨D.host.sqrtMinusD, sqrtMinusD_isIntegral D⟩

theorem rtE_sq (D : D7) : rtE D ^ 2 = -(D.host.d : 𝓞 D.host.E) := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  rw [map_pow, map_neg, map_natCast]
  exact D.host.sqrtMinusD_sq

theorem half_one_add_sqrt_neg_isIntegral (D : D7) : IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d + 1 = 4 * m :=
    ⟨(D.host.d + 1) / 4, by have := D.host.hyp.2.2.2.1; omega⟩
  set c : D.host.E := (1 + D.host.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : D.host.E) = 0 := by
    have e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
    have hs := D.host.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * e
  exact ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩

def w0E (D : D7) : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2, half_one_add_sqrt_neg_isIntegral D⟩

theorem two_w0E (D : D7) : 2 * w0E D = 1 + rtE D := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  rw [map_mul, map_add, map_one, map_ofNat]
  show 2 * ((1 + D.host.sqrtMinusD) / 2) = 1 + D.host.sqrtMinusD
  field_simp

def barE (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E)

def UnramBridge : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K)

def hostOf (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E where
  d := D.host.d
  d_mod := D.host.hyp.2.2.2.1
  d_prime := D.host.hyp.2.1
  rt := rtE D
  rt_sq := rtE_sq D
  w0 := w0E D
  two_weight_eq_one_add_root := two_w0E D
  bar := barE D
  bar_eq _ := rfl
  unram := hU
  rt0 := D.host.φ₀ D.host.sqrtMinusD
  sqrt_neg_disc_sq := by rw [← map_pow, D.host.sqrtMinusD_sq]; simp

theorem barE_eq_conj (D : D7) (a : 𝓞 D.host.E) : ((barE D a : 𝓞 D.host.E) : D.host.E) = D.host.conj (a : D.host.E) := by
  apply D.host.φ₀.injective
  show D.host.φ₀ (IsCMField.complexConj D.host.E (a : D.host.E)) = _
  rw [IsCMField.complexEmbedding_complexConj]
  exact (D.host.toHostAx.conjE_apply _ _).symm

theorem barE_eq_star (D : D7) (a : 𝓞 D.host.E) :
    ((barE D a : 𝓞 D.host.E) : D.host.E) = (letI := D.host.cmStar; star (a : D.host.E)) := rfl

theorem cc_sqrtMinusD (D : D7) : IsCMField.complexConj D.host.E D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  have h := barE_eq_conj D (rtE D)
  have h2 := D.host.conj_sqrtMinusD
  exact h.trans h2

theorem conj_w0E (D : D7) : barE D (w0E D) = 1 - w0E D := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  rw [map_sub, map_one]
  show IsCMField.complexConj D.host.E ((1 + D.host.sqrtMinusD) / 2) = 1 - (1 + D.host.sqrtMinusD) / 2
  rw [map_div₀, map_add, map_one, cc_sqrtMinusD, map_ofNat]
  ring

def mE (D : D7) : ℕ := (D.host.d + 1) / 4

theorem mE_spec (D : D7) : 4 * mE D = D.host.d + 1 := by
  have := D.host.hyp.2.2.2.1; unfold mE; omega

theorem w0E_sq (D : D7) : w0E D ^ 2 = w0E D - (mE D : 𝓞 D.host.E) := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  rw [map_pow, map_sub, map_natCast]
  show ((1 + D.host.sqrtMinusD) / 2) ^ 2 = (1 + D.host.sqrtMinusD) / 2 - (mE D : D.host.E)
  have e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (mE D : D.host.E) := by exact_mod_cast (mE_spec D).symm
  have hs := D.host.sqrtMinusD_sq
  linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * e

theorem cmUnram_conj (D : D7) : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ θ : 𝓞 D.host.E,
    θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ ∉ P := by
  intro P hP
  obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
  refine ⟨θ, ?_⟩
  have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t := by
    apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
    exact ht.symm
  rwa [this]

def hostOfB (D : D7) (hB : UnramBridge) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E :=
  hostOf D (hB D.host.E (cmUnram_conj D))

theorem unramBridge : UnramBridge := fun K _ _ _ h => unramBridge_holds K h

def hostOfRecord (D : D7) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E := hostOfB D unramBridge

open Classical in

def cRoot (D : D7) (p : ℕ) : ℤ :=
  if h : ∃ c : ℤ, (p : ℤ) ∣ c ^ 2 - c + mE D then Classical.choose h else 0

def pIdeal (D : D7) (p : ℕ) : Ideal (𝓞 D.host.E) :=
  Ideal.span {(p : 𝓞 D.host.E), w0E D - (cRoot D p : 𝓞 D.host.E)}

def MbOf (D : D7) (ps : List ℕ) : Ideal (𝓞 D.host.E) := (ps.map (pIdeal D)).prod

theorem fromK_of_gen {R : Type} [CommRing R] {I : Ideal R} {A : Subalgebra ℤ R}
    (h : ∃ G : Set R, I = Ideal.span G ∧ G ⊆ A) : I = Ideal.span {a | a ∈ I ∧ a ∈ A} := by
  obtain ⟨G, rfl, hG⟩ := h
  apply le_antisymm
  · exact Ideal.span_mono (fun x hx => ⟨Ideal.subset_span hx, hG hx⟩)
  · exact Ideal.span_le.2 (fun x hx => hx.1)

theorem MbOf_gen (D : D7) : ∀ ps : List ℕ, ∃ G : Set (𝓞 D.host.E),
    MbOf D ps = Ideal.span G ∧ G ⊆ Algebra.adjoin ℤ {w0E D}
  | [] => ⟨{1}, by simp [MbOf], by
      intro x hx; rw [Set.mem_singleton_iff.1 hx]; exact Subalgebra.one_mem _⟩
  | p :: t => by
      obtain ⟨G, hG, hGA⟩ := MbOf_gen D t
      refine ⟨{(p : 𝓞 D.host.E), w0E D - (cRoot D p : 𝓞 D.host.E)} * G, ?_, ?_⟩
      · rw [MbOf, List.map_cons, List.prod_cons, ← MbOf, hG, pIdeal, Ideal.span_mul_span']
      · intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
        refine Subalgebra.mul_mem _ ?_ (hGA hb)
        rcases ha with rfl | rfl
        · exact Subalgebra.natCast_mem _ _
        · exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _))
            (Subalgebra.intCast_mem _ _)

theorem MbOf_fromK (D : D7) (ps : List ℕ) :
    MbOf D ps = Ideal.span {a | a ∈ MbOf D ps ∧ a ∈ Algebra.adjoin ℤ {w0E D}} :=
  fromK_of_gen (MbOf_gen D ps)

abbrev bH (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := ((barE D : 𝓞 D.host.E ≃+* 𝓞 D.host.E) : 𝓞 D.host.E →+* 𝓞 D.host.E)

def SplitPrimes (D : D7) : Prop :=
  (∀ i, D.host.g i ≠ 2) ∧
    ∀ p ∈ [D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'], jacobiSym (-(D.host.d : ℤ)) p = 1

def MbProdLaw (D : D7) (ps : List ℕ) : Prop :=
  MbOf D ps * (MbOf D ps).map (bH D) = Ideal.span {((ps.prod : ℕ) : 𝓞 D.host.E)}

def MbCopLaw (D : D7) (ps : List ℕ) : Prop := MbOf D ps ⊔ (MbOf D ps).map (bH D) = ⊤

def SplitOK (D : D7) (p : ℕ) : Prop := p.Prime ∧ p ≠ 2 ∧ jacobiSym (-(D.host.d : ℤ)) p = 1

theorem exists_cRoot (D : D7) {p : ℕ} (hp : SplitOK D p) : ∃ c : ℤ, (p : ℤ) ∣ c ^ 2 - c + mE D := by
  have := Fact.mk hp.1
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hp.2.2
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp.2.1 ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).1 h')
  set h := (2 : ZMod p)⁻¹
  have hh : 2 * h = 1 := mul_inv_cancel₀ h2
  have e4 : (4 : ZMod p) * (mE D : ZMod p) = (D.host.d : ZMod p) + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) (mE_spec D)
  push_cast at hr
  obtain ⟨c, hc⟩ := ZMod.intCast_surjective ((1 + r) * h)
  refine ⟨c, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_⟩
  push_cast [hc]
  linear_combination (-h ^ 2) * hr + h ^ 2 * e4 + ((1 + r) * h - (mE D : ZMod p) * (2 * h + 1)) * hh

theorem cRoot_spec (D : D7) {p : ℕ} (hp : SplitOK D p) : (p : ℤ) ∣ cRoot D p ^ 2 - cRoot D p + mE D := by
  rw [cRoot, dif_pos (exists_cRoot D hp)]; exact Classical.choose_spec (exists_cRoot D hp)

theorem cRoot_coprime (D : D7) {p : ℕ} (hp : SplitOK D p) : IsCoprime (1 - 2 * cRoot D p) (p : ℤ) := by
  apply IsCoprime.symm
  rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.1)]
  intro hdiv
  obtain ⟨t, ht⟩ := cRoot_spec D hp
  have e : (4 : ℤ) * (mE D : ℤ) = (D.host.d : ℤ) + 1 := by exact_mod_cast mE_spec D
  have hd : (D.host.d : ℤ) = 4 * (cRoot D p ^ 2 - cRoot D p + mE D) - (1 - 2 * cRoot D p) ^ 2 := by
    linear_combination (-1 : ℤ) * e
  have hpd : (p : ℤ) ∣ D.host.d := by
    rw [hd]; exact dvd_sub (Dvd.dvd.mul_left ⟨t, ht⟩ 4) (dvd_pow hdiv two_ne_zero)
  have hpeq : p = D.host.d := (Nat.prime_dvd_prime_iff_eq hp.1 D.host.hyp.2.1).1 (Int.natCast_dvd_natCast.1 hpd)
  have hj := hp.2.2
  rw [hpeq] at hj
  have : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have h0 : jacobiSym (-(D.host.d : ℤ)) D.host.d = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime]
    show Nat.gcd (-(D.host.d : ℤ)).natAbs (D.host.d : ℤ).natAbs ≠ 1
    simp [D.host.hyp.2.1.ne_one]
  rw [h0] at hj; exact absurd hj (by decide)

theorem map_pIdeal (D : D7) (p : ℕ) : (pIdeal D p).map (bH D) =
    Ideal.span {(p : 𝓞 D.host.E), 1 - w0E D - (cRoot D p : 𝓞 D.host.E)} := by
  rw [pIdeal, Ideal.map_span, Set.image_pair]
  simp [conj_w0E]

theorem pIdeal_mul_bar (D : D7) {p : ℕ} (hp : SplitOK D p) :
    pIdeal D p * (pIdeal D p).map (bH D) = Ideal.span {(p : 𝓞 D.host.E)} := by
  rw [map_pIdeal, pIdeal, Ideal.span_pair_mul_span_pair]
  obtain ⟨t, ht⟩ := cRoot_spec D hp
  obtain ⟨u, v, huv⟩ := cRoot_coprime D hp
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hz with rfl | rfl | rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
    · refine ⟨(t : 𝓞 D.host.E), ?_⟩
      have hw := w0E_sq D
      have ht' : ((cRoot D p ^ 2 - cRoot D p + mE D : ℤ) : 𝓞 D.host.E) = ((p * t : ℤ) : 𝓞 D.host.E) := by rw [ht]
      push_cast at ht'
      linear_combination (-1 : 𝓞 D.host.E) * hw + ht'
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have huv' : ((u * (1 - 2 * cRoot D p) + v * p : ℤ) : 𝓞 D.host.E) = ((1 : ℤ) : 𝓞 D.host.E) := by rw [huv]
    push_cast at huv'
    have e : (p : 𝓞 D.host.E) = (u : 𝓞 D.host.E) * ((p : 𝓞 D.host.E) * (1 - w0E D - (cRoot D p : 𝓞 D.host.E))) +
        (u : 𝓞 D.host.E) * ((w0E D - (cRoot D p : 𝓞 D.host.E)) * (p : 𝓞 D.host.E)) +
        (v : 𝓞 D.host.E) * ((p : 𝓞 D.host.E) * (p : 𝓞 D.host.E)) := by
      linear_combination (-(p : 𝓞 D.host.E)) * huv'
    have key := Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left (Ideal.span {(p : 𝓞 D.host.E) * (p : 𝓞 D.host.E), (p : 𝓞 D.host.E) * (1 - w0E D - (cRoot D p : 𝓞 D.host.E)),
        (w0E D - (cRoot D p : 𝓞 D.host.E)) * (p : 𝓞 D.host.E),
        (w0E D - (cRoot D p : 𝓞 D.host.E)) * (1 - w0E D - (cRoot D p : 𝓞 D.host.E))}) (u : 𝓞 D.host.E)
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      (Ideal.mul_mem_left _ (u : 𝓞 D.host.E) (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))
      (Ideal.mul_mem_left _ (v : 𝓞 D.host.E) (Ideal.subset_span (Set.mem_insert _ _)))
    rwa [← e] at key

theorem isCoprime_pq (D : D7) {p q : ℕ} (hp : SplitOK D p) (hq : SplitOK D q) :
    IsCoprime (pIdeal D p) ((pIdeal D q).map (bH D)) := by
  rw [Ideal.isCoprime_iff_sup_eq, map_pIdeal, pIdeal, Ideal.eq_top_iff_one]
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨u, v, huv⟩ := cRoot_coprime D hp
    have huv' : ((u * (1 - 2 * cRoot D p) + v * p : ℤ) : 𝓞 D.host.E) = ((1 : ℤ) : 𝓞 D.host.E) := by rw [huv]
    push_cast at huv'
    have e : (1 : 𝓞 D.host.E) = (u : 𝓞 D.host.E) * (w0E D - (cRoot D p : 𝓞 D.host.E)) +
        (u : 𝓞 D.host.E) * (1 - w0E D - (cRoot D p : 𝓞 D.host.E)) + (v : 𝓞 D.host.E) * (p : 𝓞 D.host.E) := by
      linear_combination (-1 : 𝓞 D.host.E) * huv'
    have key := Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ (u : 𝓞 D.host.E) (Ideal.mem_sup_left (S := Ideal.span {(p : 𝓞 D.host.E), w0E D - (cRoot D p : 𝓞 D.host.E)})
        (T := Ideal.span {(p : 𝓞 D.host.E), 1 - w0E D - (cRoot D p : 𝓞 D.host.E)})
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
      (Ideal.mul_mem_left _ (u : 𝓞 D.host.E) (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))))
      (Ideal.mul_mem_left _ (v : 𝓞 D.host.E) (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))))
    rwa [← e] at key
  · obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp.1 hq.1).2 hpq)
    have huv' : ((u * p + v * q : ℤ) : 𝓞 D.host.E) = ((1 : ℤ) : 𝓞 D.host.E) := by rw [huv]
    push_cast at huv'
    have key := Ideal.add_mem _
      (Ideal.mul_mem_left _ (u : 𝓞 D.host.E) (Ideal.mem_sup_left (S := Ideal.span {(p : 𝓞 D.host.E), w0E D - (cRoot D p : 𝓞 D.host.E)})
        (T := Ideal.span {(q : 𝓞 D.host.E), 1 - w0E D - (cRoot D q : 𝓞 D.host.E)}) (Ideal.subset_span (Set.mem_insert _ _))))
      (Ideal.mul_mem_left _ (v : 𝓞 D.host.E) (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert _ _))))
    rwa [huv'] at key

theorem isCoprime_list_right {R : Type} [CommSemiring R] (a : R) (B : ℕ → R) :
    ∀ qs : List ℕ, (∀ q ∈ qs, IsCoprime a (B q)) → IsCoprime a (qs.map B).prod
  | [], _ => by simp [isCoprime_one_right]
  | q :: t, h => by
      rw [List.map_cons, List.prod_cons]
      exact IsCoprime.mul_right (h q (by simp)) (isCoprime_list_right a B t (fun r hr => h r (by simp [hr])))

theorem isCoprime_list {R : Type} [CommSemiring R] (A B : ℕ → R) :
    ∀ ps qs : List ℕ, (∀ p ∈ ps, ∀ q ∈ qs, IsCoprime (A p) (B q)) → IsCoprime (ps.map A).prod (qs.map B).prod
  | [], _, _ => by simp [isCoprime_one_left]
  | p :: t, qs, h => by
      rw [List.map_cons, List.prod_cons]
      exact IsCoprime.mul_left (isCoprime_list_right _ B qs (h p (by simp)))
        (isCoprime_list A B t qs (fun r hr => h r (by simp [hr])))

theorem map_MbOf (D : D7) : ∀ ps : List ℕ,
    (MbOf D ps).map (bH D) = (ps.map (fun p => (pIdeal D p).map (bH D))).prod
  | [] => by simp [MbOf, Ideal.map_top]
  | p :: t => by
      rw [MbOf, List.map_cons, List.prod_cons, Ideal.map_mul, ← MbOf, map_MbOf D t, List.map_cons, List.prod_cons]

theorem MbProd_of (D : D7) : ∀ ps : List ℕ, (∀ p ∈ ps, SplitOK D p) → MbProdLaw D ps
  | [], _ => by simp [MbProdLaw, MbOf, Ideal.map_top]
  | p :: t, h => by
      have ih := MbProd_of D t (fun q hq => h q (by simp [hq]))
      unfold MbProdLaw at ih ⊢
      rw [MbOf, List.map_cons, List.prod_cons, Ideal.map_mul, ← MbOf, mul_mul_mul_comm, pIdeal_mul_bar D (h p (by simp)),
        ih, Ideal.span_singleton_mul_span_singleton, List.prod_cons, Nat.cast_mul]

theorem MbCop_of (D : D7) (ps : List ℕ) (h : ∀ p ∈ ps, SplitOK D p) : MbCopLaw D ps := by
  rw [MbCopLaw, ← Ideal.isCoprime_iff_sup_eq, map_MbOf]
  exact isCoprime_list (pIdeal D) (fun p => (pIdeal D p).map (bH D)) ps ps
    (fun p hp q hq => isCoprime_pq D (h p hp) (h q hq))

theorem three_le_prod : ∀ ps : List ℕ, (∀ p ∈ ps, 3 ≤ p) → ps ≠ [] → 3 ≤ ps.prod
  | [], _, h => (h rfl).elim
  | p :: t, hp, _ => by
      rw [List.prod_cons]
      have h1 : 1 ≤ t.prod := by
        rw [Nat.one_le_iff_ne_zero, Ne, List.prod_eq_zero_iff]
        intro h0
        have := hp 0 (by simp [h0])
        omega
      have := hp p (by simp)
      nlinarith

theorem odd_prod_of : ∀ ps : List ℕ, (∀ p ∈ ps, Odd p) → Odd ps.prod
  | [], _ => by simp
  | p :: t, h => by
      rw [List.prod_cons]
      exact (h p (by simp)).mul (odd_prod_of t (fun q hq => h q (by simp [hq])))

def levelOfPs (D : D7) {hU} (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime ∧ p ≠ 2) (hne : ps ≠ [])
    (hP : MbProdLaw D ps) (hC : MbCopLaw D ps) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level (hostOf D hU) where
  M := ps.prod
  three_le := three_le_prod ps (fun p h => by
    have := (hp p h).1.two_le; have := (hp p h).2; omega) hne
  odd := odd_prod_of ps (fun p h => (hp p h).1.odd_of_ne_two (hp p h).2)
  Mb := MbOf D ps
  fromK := MbOf_fromK D ps
  prod := hP
  coprime := hC
  A := 1
  A_pos := Nat.one_pos

theorem splitOK_of (D : D7) (hS : SplitPrimes D) :
    ∀ p ∈ [D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'], SplitOK D p := by
  intro p hp
  have hj := hS.2 p hp
  simp at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨D.host.g_prime 0, hS.1 0, hj⟩
  · exact ⟨D.host.g_prime 1, hS.1 1, hj⟩
  · exact ⟨D.host.pde_prime, by have := D.host.pde_mod.1; omega, hj⟩
  · exact ⟨D.host.pde'_prime, by have := D.host.pde_mod.2; omega, hj⟩

def levelOf (D : D7) {hU} (hS : SplitPrimes D) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level (hostOf D hU) :=
  have h : ∀ p ∈ [D.host.g 0, D.host.g 1], SplitOK D p := fun p hp =>
    splitOK_of D hS p (by simp at hp ⊢; tauto)
  levelOfPs D _ (fun p hp => ⟨(h p hp).1, (h p hp).2.1⟩) (by simp) (MbProd_of D _ h) (MbCop_of D _ h)

def levelDeep (D : D7) {hU} (hS : SplitPrimes D) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level (hostOf D hU) :=
  have h := splitOK_of D hS
  levelOfPs D _ (fun p hp => ⟨(h p hp).1, (h p hp).2.1⟩) (by simp) (MbProd_of D _ h) (MbCop_of D _ h)

theorem levelOf_M (D : D7) (hU) (hS : SplitPrimes D) :
    (levelOf D (hU := hU) hS).M = D.host.g 0 * D.host.g 1 ∧ (levelOf D (hU := hU) hS).A = 1 := by
  simp [levelOf, levelOfPs]

theorem levelDeep_M (D : D7) (hU) (hS : SplitPrimes D) :
    (levelDeep D (hU := hU) hS).M = D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' := by
  simp [levelDeep, levelOfPs, mul_assoc]

theorem hostOf_bar (D : D7) (hU) (a : 𝓞 D.host.E) :
    (((hostOf D hU).bar a : 𝓞 D.host.E) : D.host.E) = D.host.conj (a : D.host.E) := barE_eq_conj D a

section Dat

open scoped TensorProduct

local instance instStarRingHost (D : D7) : StarRing D.host.E := D.host.cmStar

def latW (D : D7) (j : ℕ) : Submodule (𝓞 D.host.E) (D.sp.W j).V :=
  Submodule.span (𝓞 D.host.E) {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ (D.sp.W j).L0, v = a • x}

def efQ (D : D7) (j : ℕ) : latW D j →ₗ[ℤ] latW D j →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT x y))
    (fun x x' y => by simp [map_add, mul_add])
    (fun c x y => by simp [map_zsmul]; rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul])
    (fun x y y' => by simp [map_add, mul_add])
    (fun c x y => by simp [map_zsmul]; rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul])

theorem choose_cast {M : Type} [AddCommGroup M] (B : M →ₗ[ℤ] M →ₗ[ℤ] ℚ) (h : ∀ x y, ∃ n : ℤ, B x y = n)
    (x y : M) : (((h x y).choose : ℤ) : ℚ) = B x y := (h x y).choose_spec.symm

def intForm {M : Type} [AddCommGroup M] (B : M →ₗ[ℤ] M →ₗ[ℤ] ℚ) (h : ∀ x y, ∃ n : ℤ, B x y = n) :
    LinearMap.BilinForm ℤ M :=
  LinearMap.mk₂ ℤ (fun x y => (h x y).choose)
    (fun x x' y => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, choose_cast, choose_cast, choose_cast, map_add, LinearMap.add_apply]))
    (fun c x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, choose_cast, choose_cast, LinearMap.map_smul₂, zsmul_eq_mul]))
    (fun x y y' => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, choose_cast, choose_cast, choose_cast, map_add]))
    (fun c x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, choose_cast, choose_cast, map_zsmul, zsmul_eq_mul]))

theorem intForm_cast {M : Type} [AddCommGroup M] (B : M →ₗ[ℤ] M →ₗ[ℤ] ℚ) (h : ∀ x y, ∃ n : ℤ, B x y = n)
    (x y : M) : ((intForm B h x y : ℤ) : ℚ) = B x y := choose_cast B h x y

def DatInt (D : D7) (j : ℕ) : Prop := ∀ x y : latW D j, ∃ n : ℤ, efQ D j x y = n

def DomFor (D : D7) (j : ℕ) (EF : LinearMap.BilinForm ℤ (latW D j)) : Prop :=
  ∃ J : ℝ ⊗[ℤ] latW D j →ₗ[ℝ] ℝ ⊗[ℤ] latW D j, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 D.host.E) (A : ℝ ⊗[ℤ] latW D j →ₗ[ℝ] ℝ ⊗[ℤ] latW D j) (t : ℂ),
      (∀ x : latW D j, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : D.host.E →+* ℂ => τ (rtE D : D.host.E) = D.host.φ₀ D.host.sqrtMinusD),
        (((D.R.sigW j).1 : ℂ) * τ (a : D.host.E) + ((D.R.sigW j).2 : ℂ) * starRingEnd ℂ (τ (a : D.host.E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im

open Classical in

def sgnW (D : D7) (j : ℕ) : ℤ := if ∃ hI : DatInt D j, DomFor D j (intForm (efQ D j) hI) then 1 else -1

def efW (D : D7) (j : ℕ) (hI : DatInt D j) : LinearMap.BilinForm ℤ (latW D j) := sgnW D j • intForm (efQ D j) hI

theorem efQ_adj (D : D7) (j : ℕ) (a : 𝓞 D.host.E) (x y : latW D j) :
    efQ D j (a • x) y = efQ D j x (barE D a • y) := by
  simp only [efQ, LinearMap.mk₂_apply, Submodule.coe_smul]
  rw [← algebraMap_smul D.host.E a (x : (D.sp.W j).V), ← algebraMap_smul D.host.E (barE D a) (y : (D.sp.W j).V),
    LinearMap.map_smulₛₗ₂, map_smul]
  rfl

theorem efW_adj (D : D7) (j : ℕ) (hI : DatInt D j) (a : 𝓞 D.host.E) (x y : latW D j) :
    efW D j hI (a • x) y = efW D j hI x (barE D a • y) := by
  simp only [efW, LinearMap.smul_apply]
  congr 1
  exact Int.cast_injective (α := ℚ) ((intForm_cast _ hI _ _).trans ((efQ_adj D j a x y).trans (intForm_cast _ hI _ _).symm))

theorem conj_xi0_alt (D : D7) : IsCMField.complexConj D.host.E D.host.xi0 = -D.host.xi0 := by
  simp only [Host.xi0, map_neg, map_div₀, map_one, map_mul, map_natCast, cc_sqrtMinusD]
  rw [mul_neg, div_neg]

theorem trace_cc (D : D7) (z : D.host.E) :
    Algebra.trace ℚ D.host.E (IsCMField.complexConj D.host.E z) = Algebra.trace ℚ D.host.E z := by
  rw [Algebra.trace_eq_of_equiv_equiv (RingEquiv.refl ℚ) (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E)
    (RingHom.ext_rat _ _) z]
  rfl

theorem efQ_alt (D : D7) (j : ℕ) (x : latW D j) : efQ D j x x = 0 := by
  simp only [efQ, LinearMap.mk₂_apply]
  have hh : IsCMField.complexConj D.host.E ((D.sp.W j).hT x x) = (D.sp.W j).hT x x :=
    LinearMap.isSymm_def.1 (D.sp.W j).herm x x
  have hz : IsCMField.complexConj D.host.E (D.host.xi0 * (D.sp.W j).hT x x) =
      -(D.host.xi0 * (D.sp.W j).hT x x) := by
    rw [map_mul, conj_xi0_alt, hh, neg_mul]
  have ht := trace_cc D (D.host.xi0 * (D.sp.W j).hT x x)
  rw [hz, map_neg] at ht
  linarith

theorem efW_alt (D : D7) (j : ℕ) (hI : DatInt D j) (x : latW D j) : efW D j hI x x = 0 := by
  simp only [efW, LinearMap.smul_apply]
  rw [Int.cast_injective (α := ℚ) ((intForm_cast _ hI x x).trans ((efQ_alt D j x).trans Int.cast_zero.symm)), smul_zero]

theorem latW_fin (D : D7) (j : ℕ) : Module.Finite (𝓞 D.host.E) (latW D j) := by
  obtain ⟨a, ha, hAA⟩ := D.host.AA.isFractional
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero ha (IsFractionRing.injective _ D.host.E (h0.trans (map_zero _).symm))
  let f : (D.sp.W j).V →ₗ[𝓞 D.host.E] (D.sp.W j).V :=
    (LinearMap.lsmul D.host.E (D.sp.W j).V (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹).restrictScalars (𝓞 D.host.E)
  have hN : ((D.sp.W j).L0.map f).FG := (D.sp.W j).standardTuple_isLattice.fg.map f
  have hle : latW D j ≤ (D.sp.W j).L0.map f := by
    rw [latW, Submodule.span_le]
    rintro v ⟨b, hb, x, hx, rfl⟩
    obtain ⟨d, hd⟩ := hAA b hb
    refine ⟨d • x, (D.sp.W j).L0.smul_mem d hx, ?_⟩
    show (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ • (d • x) = b • x
    rw [← algebraMap_smul D.host.E d x, hd, Algebra.smul_def, smul_smul, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  exact Module.Finite.iff_fg.2 (isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian _ hN) _ hle)

theorem latW_proj (D : D7) (j : ℕ) : Module.Projective (𝓞 D.host.E) (latW D j) := by
  have := latW_fin D j
  have hF : Module.Flat (𝓞 D.host.E) (latW D j) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).1 hx
    have h0 : r • x = 0 := hrx
    have h1 : r • (x : (D.sp.W j).V) = 0 := by rw [← Submodule.coe_smul, h0]; rfl
    rw [← algebraMap_smul D.host.E r (x : (D.sp.W j).V), smul_eq_zero] at h1
    rcases h1 with h | h
    · exact absurd (IsFractionRing.injective _ D.host.E (h.trans (map_zero _).symm)) (nonZeroDivisors.ne_zero hr)
    · exact (Submodule.mem_bot _).2 (Subtype.ext h)
  have := Module.finitePresentation_of_finite (𝓞 D.host.E) (latW D j)
  exact Module.Flat.projective_of_finitePresentation

structure DatLaws (D : D7) (j : ℕ) (hI : DatInt D j) : Prop where
  unimod : Function.Bijective (efW D j hI)
  rank : Module.finrank (𝓞 D.host.E) (latW D j) = (D.R.sigW j).1 + (D.R.sigW j).2
  dom : DomFor D j (efW D j hI)

def datumOf (D : D7) {hU} (j : ℕ) (hI : DatInt D j) (hL : DatLaws D j hI) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum (hostOf D hU) where
  La := latW D j
  fin := latW_fin D j
  proj := latW_proj D j
  EF := efW D j hI
  alt := efW_alt D j hI
  unimod := hL.unimod
  adj := efW_adj D j hI
  p := (D.R.sigW j).1
  q := (D.R.sigW j).2
  rank := hL.rank
  dom := hL.dom

end Dat

end Formalism.L2.Pj
