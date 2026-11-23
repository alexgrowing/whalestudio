import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsLocFrac
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace FlagRestrict

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Forms

open Classical

variable {R : Type*} [CommRing R]

def blkWt : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1

theorem weight_blkWt_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkWt (ι := ι)) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blkWt]
  · intro b _ hb
    simp [blkWt, Ne.symm hb]
  · simp

theorem isMultiHomog_iff (s : MRingOver R ι) (a : K → ℕ) :
    IsMultiHomog s a ↔ IsWeightedHomogeneous (blkWt (ι := ι)) s a := by
  constructor
  · intro h m hm
    funext k
    rw [weight_blkWt_apply]
    exact h m (mem_support_iff.mpr hm) k
  · intro h m hm k
    rw [← weight_blkWt_apply, h (mem_support_iff.mp hm)]

theorem isMultiHomog_mul {f g : MRingOver R ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) :=
  (isMultiHomog_iff _ _).2 (((isMultiHomog_iff _ _).1 hf).mul ((isMultiHomog_iff _ _).1 hg))

theorem isMultiHomog_add {f g : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a :=
  (isMultiHomog_iff _ _).2 (((isMultiHomog_iff _ _).1 hf).add ((isMultiHomog_iff _ _).1 hg))

theorem isMultiHomog_sub {f g : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f - g) a := by
  rw [isMultiHomog_iff] at *
  exact (weightedHomogeneousSubmodule R _ a).sub_mem hf hg

theorem isMultiHomog_C (c : R) : IsMultiHomog (C c : MRingOver R ι) 0 :=
  (isMultiHomog_iff _ _).2 (isWeightedHomogeneous_C _ _)

theorem isMultiHomog_one : IsMultiHomog (1 : MRingOver R ι) 0 := by
  simpa using isMultiHomog_C (R := R) (ι := ι) 1

theorem isMultiHomog_X (p : Σ k, ι k) : IsMultiHomog (X p : MRingOver R ι) (Pi.single p.1 1) :=
  (isMultiHomog_iff _ _).2 (isWeightedHomogeneous_X R _ p)

def segForm (s : ∀ k, ι k) : MRingOver R ι := ∏ k, X ⟨k, s k⟩

theorem isMultiHomog_segForm (s : ∀ k, ι k) :
    IsMultiHomog (segForm (R := R) s) (fun _ => 1) := by
  have h : IsWeightedHomogeneous (blkWt (ι := ι)) (segForm (R := R) s) (∑ k, blkWt (ι := ι) ⟨k, s k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ => isWeightedHomogeneous_X R _ _
  have e : (∑ k, blkWt (ι := ι) ⟨k, s k⟩) = fun _ => 1 := by
    funext k
    simp only [blkWt, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact (isMultiHomog_iff _ _).2 h

theorem aeval_segForm {S : Type*} [CommRing S] [Algebra R S] (y : (Σ k, ι k) → S) (s : ∀ k, ι k) :
    aeval y (segForm (R := R) s) = mseg y s := by
  simp [segForm, mseg, map_prod]

theorem map_segForm {S : Type*} [CommRing S] (f : R →+* S) (s : ∀ k, ι k) :
    MvPolynomial.map f (segForm (R := R) s) = segForm s := by
  simp [segForm, map_prod]

theorem mcMap_of_isMultiHomog {Ω : Type*} [CommRing Ω] [Algebra R Ω] (x : (Σ k, ι k) → Ω)
    {H : MRingOver R ι} {α : K → ℕ} (hH : IsMultiHomog H α) :
    mcMap R x H = MvPolynomial.C (aeval x H) * ∏ k, X k ^ α k := by
  classical
  conv_lhs => rw [H.as_sum]
  conv_rhs => rw [H.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [mcMap, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  rw [mul_assoc]
  congr 2
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← hH m hm k, ← Finset.prod_pow_eq_pow_sum]

theorem mem_mcIdeal_iff {Ω : Type*} [Field Ω] [Algebra R Ω] (x : (Σ k, ι k) → Ω)
    {H : MRingOver R ι} {α : K → ℕ} (hH : IsMultiHomog H α) :
    H ∈ mcIdeal R x ↔ aeval x H = 0 := by
  rw [mcIdeal, RingHom.mem_ker, mcMap_of_isMultiHomog x hH, mul_eq_zero, MvPolynomial.C_eq_zero]
  have : (∏ k, X k ^ α k : MvPolynomial K Ω) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  simp [this]

end Forms

section GenPt

variable {F : Type*} [Field F] (Q : Ideal (MRingOver F ι)) [Q.IsPrime]

theorem aeval_genPt (H : MRingOver F ι) :
    aeval (genPt F Q) H = algebraMap (MRingOver F ι ⧸ Q) (FractionRing (MRingOver F ι ⧸ Q))
      (Ideal.Quotient.mk Q H) := by
  have h : (aeval (genPt F Q) : MRingOver F ι →ₐ[F] FractionRing (MRingOver F ι ⧸ Q)) =
      (IsScalarTower.toAlgHom F (MRingOver F ι ⧸ Q) (FractionRing (MRingOver F ι ⧸ Q))).comp
        (Ideal.Quotient.mkₐ F Q) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [genPt]
  exact congrArg (fun φ : MRingOver F ι →ₐ[F] FractionRing (MRingOver F ι ⧸ Q) => φ H) h

theorem aeval_genPt_eq_zero_iff (H : MRingOver F ι) : aeval (genPt F Q) H = 0 ↔ H ∈ Q := by
  rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem mcIdeal_genPt (hQ : IsMultiHomogIdeal Q) : mcIdeal F (genPt F Q) = Q := by
  apply le_antisymm
  · intro H hH
    rw [← aeval_genPt_eq_zero_iff]
    have h : (MvPolynomial.eval (fun _ : K => (1 : FractionRing (MRingOver F ι ⧸ Q)))).comp
        (mcMap F (genPt F Q)).toRingHom = (aeval (genPt F Q)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) fun p => ?_
      · simp [mcMap]
      · simp [mcMap]
    have h2 := congrArg (fun φ => φ H) h
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [← h2]
    change MvPolynomial.eval _ (mcMap F (genPt F Q) H) = 0
    rw [show mcMap F (genPt F Q) H = 0 from hH, map_zero]
  · obtain ⟨S, hS, rfl⟩ := hQ
    rw [Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS g hg
    exact (mem_mcIdeal_iff _ ha).2 ((aeval_genPt_eq_zero_iff _ g).2 (Ideal.subset_span hg))

end GenPt

section Loc

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]

abbrev red : MRingOver O ι →+* MRingOver (kap O) ι := MvPolynomial.map (IsLocalRing.residue O)

variable {O}
variable {x : (Σ k, ι k) → Ω} {Q : Ideal (MRingOver (kap O) ι)} [Q.IsPrime]

theorem aeval_ne_zero (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {G : MRingOver O ι} {α : K → ℕ}
    (hG : IsMultiHomog G α) (hGQ : red O G ∉ Q) : aeval x G ≠ 0 := fun h =>
  hGQ (hPQ (Ideal.mem_map_of_mem _ ((mem_mcIdeal_iff x hG).2 h)))

theorem aeval_genPt_red_ne_zero {G : MRingOver O ι} (hGQ : red O G ∉ Q) :
    aeval (genPt (kap O) Q) (red O G) ≠ 0 := fun h => hGQ ((aeval_genPt_eq_zero_iff Q _).1 h)

variable (O Q) in

def resOf (F G : MRingOver O ι) : FractionRing (MRingOver (kap O) ι ⧸ Q) :=
  aeval (genPt (kap O) Q) (red O F) / aeval (genPt (kap O) Q) (red O G)

theorem isLocFrac_mul {F G F' G' : MRingOver O ι} (h1 : IsLocFrac O Q F G) (h2 : IsLocFrac O Q F' G') :
    IsLocFrac O Q (F * F') (G * G') := by
  obtain ⟨α, hF, hG, hGQ⟩ := h1
  obtain ⟨β, hF', hG', hG'Q⟩ := h2
  refine ⟨α + β, isMultiHomog_mul hF hF', isMultiHomog_mul hG hG', ?_⟩
  rw [map_mul]
  exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hGQ hG'Q

theorem isLocFrac_add {F G F' G' : MRingOver O ι} (h1 : IsLocFrac O Q F G) (h2 : IsLocFrac O Q F' G') :
    IsLocFrac O Q (F * G' + G * F') (G * G') := by
  obtain ⟨α, hF, hG, hGQ⟩ := h1
  obtain ⟨β, hF', hG', hG'Q⟩ := h2
  refine ⟨α + β, isMultiHomog_add (isMultiHomog_mul hF hG') (isMultiHomog_mul hG hF'),
    isMultiHomog_mul hG hG', ?_⟩
  · rw [map_mul]
    exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hGQ hG'Q

theorem isLocFrac_C (c : O) : IsLocFrac O Q (C c) 1 := by
  refine ⟨0, isMultiHomog_C c, isMultiHomog_one, ?_⟩
  rw [map_one]
  exact fun h => ‹Q.IsPrime›.ne_top ((Ideal.eq_top_iff_one Q).2 h)

theorem isLocFrac_swap {F G : MRingOver O ι} (h : IsLocFrac O Q F G) (hF : red O F ∉ Q) :
    IsLocFrac O Q G F := by
  obtain ⟨α, h1, h2, _⟩ := h
  exact ⟨α, h2, h1, hF⟩

theorem resOf_congr (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {F G F' G' : MRingOver O ι}
    (h1 : IsLocFrac O Q F G) (h2 : IsLocFrac O Q F' G')
    (h : aeval x F / aeval x G = aeval x F' / aeval x G') : resOf O Q F G = resOf O Q F' G' := by
  obtain ⟨α, hF, hG, hGQ⟩ := h1
  obtain ⟨β, hF', hG', hG'Q⟩ := h2
  rw [div_eq_div_iff (aeval_ne_zero hPQ hG hGQ) (aeval_ne_zero hPQ hG' hG'Q)] at h
  have hH : IsMultiHomog (F * G' - F' * G) (α + β) := by
    refine isMultiHomog_sub (isMultiHomog_mul hF hG') ?_
    rw [add_comm]
    exact isMultiHomog_mul hF' hG
  have h0 : aeval x (F * G' - F' * G) = 0 := by
    rw [map_sub, map_mul, map_mul, h, sub_self]
  have hmem : red O (F * G' - F' * G) ∈ Q :=
    hPQ (Ideal.mem_map_of_mem _ ((mem_mcIdeal_iff x hH).2 h0))
  rw [← aeval_genPt_eq_zero_iff, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, sub_eq_zero] at hmem
  unfold resOf
  rw [div_eq_div_iff (aeval_genPt_red_ne_zero hGQ) (aeval_genPt_red_ne_zero hG'Q)]
  exact hmem

variable (x Q) in

def locAlg : Subalgebra O Ω where
  carrier := {z | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ aeval x G ≠ 0 ∧ z = aeval x F / aeval x G}
  mul_mem' := by
    rintro _ _ ⟨F, G, h1, hx, rfl⟩ ⟨F', G', h2, hx', rfl⟩
    exact ⟨F * F', G * G', isLocFrac_mul h1 h2, by rw [map_mul]; exact mul_ne_zero hx hx',
      by rw [map_mul, map_mul, mul_div_mul_comm]⟩
  add_mem' := by
    rintro _ _ ⟨F, G, h1, hx, rfl⟩ ⟨F', G', h2, hx', rfl⟩
    exact ⟨F * G' + G * F', G * G', isLocFrac_add h1 h2, by rw [map_mul]; exact mul_ne_zero hx hx',
      by rw [div_add_div _ _ hx hx', map_add, map_mul, map_mul, map_mul]⟩
  algebraMap_mem' c := ⟨C c, 1, isLocFrac_C c, by simp, by simp⟩

theorem mem_locAlg_iff {z : Ω} : z ∈ locAlg x Q ↔
    ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ aeval x G ≠ 0 ∧ z = aeval x F / aeval x G := Iff.rfl

theorem mem_locAlg (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {F G : MRingOver O ι} (h : IsLocFrac O Q F G) :
    aeval x F / aeval x G ∈ locAlg x Q :=
  ⟨F, G, h, aeval_ne_zero hPQ h.choose_spec.2.1 h.choose_spec.2.2, rfl⟩

open Classical in
variable (x Q) in

def rs (z : Ω) : FractionRing (MRingOver (kap O) ι ⧸ Q) :=
  if h : z ∈ locAlg x Q then resOf O Q (mem_locAlg_iff.1 h).choose (mem_locAlg_iff.1 h).choose_spec.choose else 0

theorem rs_eq (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {z : Ω} {F G : MRingOver O ι} (hFG : IsLocFrac O Q F G)
    (hz : z = aeval x F / aeval x G) : rs x Q z = resOf O Q F G := by
  have hm : z ∈ locAlg x Q := hz ▸ mem_locAlg hPQ hFG
  rw [rs, dif_pos hm]
  obtain ⟨h1, _, h2⟩ := (mem_locAlg_iff.1 hm).choose_spec.choose_spec
  exact resOf_congr hPQ h1 hFG (h2.symm.trans hz)

theorem rs_frac (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {F G : MRingOver O ι} (hFG : IsLocFrac O Q F G) :
    rs x Q (aeval x F / aeval x G) = resOf O Q F G :=
  rs_eq hPQ hFG rfl

theorem rs_algebraMap (hPQ : redIdeal O (mcIdeal O x) ≤ Q) (c : O) :
    rs x Q (algebraMap O Ω c) = algebraMap (kap O) _ (IsLocalRing.residue O c) := by
  rw [rs_eq hPQ (isLocFrac_C c) (by simp)]
  simp [resOf]

theorem rs_one (hPQ : redIdeal O (mcIdeal O x) ≤ Q) : rs x Q (1 : Ω) = 1 := by
  simpa using rs_algebraMap (x := x) (Q := Q) hPQ 1

theorem rs_zero (hPQ : redIdeal O (mcIdeal O x) ≤ Q) : rs x Q (0 : Ω) = 0 := by
  simpa using rs_algebraMap (x := x) (Q := Q) hPQ 0

theorem rs_mul (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a b : Ω} (ha : a ∈ locAlg x Q) (hb : b ∈ locAlg x Q) :
    rs x Q (a * b) = rs x Q a * rs x Q b := by
  obtain ⟨F, G, h1, hx, rfl⟩ := ha
  obtain ⟨F', G', h2, hx', rfl⟩ := hb
  rw [rs_frac hPQ h1, rs_frac hPQ h2, rs_eq hPQ (isLocFrac_mul h1 h2)
    (by rw [map_mul, map_mul, mul_div_mul_comm])]
  simp only [resOf, map_mul, mul_div_mul_comm]

theorem rs_add (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a b : Ω} (ha : a ∈ locAlg x Q) (hb : b ∈ locAlg x Q) :
    rs x Q (a + b) = rs x Q a + rs x Q b := by
  obtain ⟨F, G, h1, hx, rfl⟩ := ha
  obtain ⟨F', G', h2, hx', rfl⟩ := hb
  rw [rs_frac hPQ h1, rs_frac hPQ h2, rs_eq hPQ (isLocFrac_add h1 h2)
    (by rw [div_add_div _ _ hx hx', map_add, map_mul, map_mul, map_mul])]
  simp only [resOf, map_add, map_mul]
  rw [div_add_div _ _ (aeval_genPt_red_ne_zero h1.choose_spec.2.2)
    (aeval_genPt_red_ne_zero h2.choose_spec.2.2)]

theorem rs_pow (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a : Ω} (ha : a ∈ locAlg x Q) (n : ℕ) :
    rs x Q (a ^ n) = rs x Q a ^ n := by
  induction n with
  | zero => simp [rs_one hPQ]
  | succ n ih => rw [pow_succ, rs_mul hPQ (pow_mem ha n) ha, ih, pow_succ]

theorem rs_sum (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {β : Type*} (s : Finset β) (f : β → Ω)
    (hf : ∀ i ∈ s, f i ∈ locAlg x Q) : rs x Q (∑ i ∈ s, f i) = ∑ i ∈ s, rs x Q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rs_zero hPQ]
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, rs_add hPQ (hf a (Finset.mem_insert_self a s))
      (sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem rs_prod (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {β : Type*} (s : Finset β) (f : β → Ω)
    (hf : ∀ i ∈ s, f i ∈ locAlg x Q) : rs x Q (∏ i ∈ s, f i) = ∏ i ∈ s, rs x Q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rs_one hPQ]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has, rs_mul hPQ (hf a (Finset.mem_insert_self a s))
      (prod_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem inv_mem_of_rs_ne_zero (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a : Ω} (ha : a ∈ locAlg x Q)
    (h0 : rs x Q a ≠ 0) : a⁻¹ ∈ locAlg x Q ∧ rs x Q a⁻¹ = (rs x Q a)⁻¹ := by
  obtain ⟨F, G, h1, hx, rfl⟩ := ha
  rw [rs_frac hPQ h1] at h0 ⊢
  have hF : red O F ∉ Q := fun h => h0 (by
    rw [resOf, (aeval_genPt_eq_zero_iff Q _).2 h, zero_div])
  have h2 := isLocFrac_swap h1 hF
  rw [inv_div]
  exact ⟨mem_locAlg hPQ h2, by rw [rs_frac hPQ h2, resOf, resOf, inv_div]⟩

theorem ne_zero_of_rs_ne_zero (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a : Ω} (h0 : rs x Q a ≠ 0) : a ≠ 0 :=
  fun h => h0 (by rw [h, rs_zero hPQ])

theorem zpow_mem_of_rs_ne_zero (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {a : Ω} (ha : a ∈ locAlg x Q)
    (h0 : rs x Q a ≠ 0) (n : ℤ) : a ^ n ∈ locAlg x Q ∧ rs x Q (a ^ n) = rs x Q a ^ n := by
  cases n with
  | ofNat m => simp only [Int.ofNat_eq_natCast, zpow_natCast]; exact ⟨pow_mem ha m, rs_pow hPQ ha m⟩
  | negSucc m =>
    rw [zpow_negSucc, zpow_negSucc]
    have h1 : rs x Q (a ^ (m + 1)) ≠ 0 := by rw [rs_pow hPQ ha]; exact pow_ne_zero _ h0
    obtain ⟨h2, h3⟩ := inv_mem_of_rs_ne_zero hPQ (pow_mem ha (m + 1)) h1
    exact ⟨h2, by rw [h3, rs_pow hPQ ha]⟩

end Loc

section Chart

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {x : (Σ k, ι k) → Ω} {Q : Ideal (MRingOver (kap O) ι)} [Q.IsPrime]

theorem red_segForm (s : ∀ k, ι k) : red O (segForm s) = segForm s :=
  map_segForm _ s

theorem red_segForm_notMem {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0) :
    red O (segForm s) ∉ Q := by
  intro h
  rw [red_segForm, ← aeval_genPt_eq_zero_iff, aeval_segForm] at h
  exact hs h

theorem isLocFrac_seg {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0) (t : ∀ k, ι k) :
    IsLocFrac O Q (segForm t) (segForm s) :=
  ⟨fun _ => 1, isMultiHomog_segForm t, isMultiHomog_segForm s, red_segForm_notMem hs⟩

theorem seg_ratio (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0)
    (t : ∀ k, ι k) : mseg x t / mseg x s ∈ locAlg x Q ∧
      rs x Q (mseg x t / mseg x s) = mseg (genPt (kap O) Q) t / mseg (genPt (kap O) Q) s := by
  have h := isLocFrac_seg (O := O) hs t
  have e : mseg x t / mseg x s = aeval x (segForm (R := O) t) / aeval x (segForm (R := O) s) := by
    rw [aeval_segForm, aeval_segForm]
  rw [e]
  refine ⟨mem_locAlg hPQ h, ?_⟩
  rw [rs_frac hPQ h, resOf, red_segForm, red_segForm, aeval_segForm, aeval_segForm]

theorem genPt_ne_zero_of_mseg {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0) (k : K) :
    genPt (kap O) Q ⟨k, s k⟩ ≠ 0 :=
  (Finset.prod_ne_zero_iff.1 hs) k (Finset.mem_univ k)

theorem coord_ratio (hPQ : redIdeal O (mcIdeal O x) ≤ Q) (k : K) (i j : ι k)
    (hj : genPt (kap O) Q ⟨k, j⟩ ≠ 0) : x ⟨k, i⟩ / x ⟨k, j⟩ ∈ locAlg x Q ∧
      rs x Q (x ⟨k, i⟩ / x ⟨k, j⟩) = genPt (kap O) Q ⟨k, i⟩ / genPt (kap O) Q ⟨k, j⟩ := by
  have hQ : red O (X ⟨k, j⟩) ∉ Q := by
    intro h
    rw [map_X, ← aeval_genPt_eq_zero_iff, aeval_X] at h
    exact hj h
  have h : IsLocFrac O Q (X ⟨k, i⟩) (X ⟨k, j⟩) := ⟨_, isMultiHomog_X _, isMultiHomog_X _, hQ⟩
  have e : x ⟨k, i⟩ / x ⟨k, j⟩ = aeval x (X ⟨k, i⟩ : MRingOver O ι) / aeval x (X ⟨k, j⟩ : MRingOver O ι) := by
    rw [aeval_X, aeval_X]
  rw [e]
  refine ⟨mem_locAlg hPQ h, ?_⟩
  rw [rs_frac hPQ h, resOf, map_X, map_X, aeval_X, aeval_X]

theorem chartMon_ratio (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s s₀ : ∀ k, ι k}
    (hs : mseg (genPt (kap O) Q) s ≠ 0) (hs₀ : mseg (genPt (kap O) Q) s₀ ≠ 0) (m : K → ℤ) :
    chartMon x s m / chartMon x s₀ m ∈ locAlg x Q ∧
      rs x Q (chartMon x s m / chartMon x s₀ m) =
        chartMon (genPt (kap O) Q) s m / chartMon (genPt (kap O) Q) s₀ m := by
  have e : chartMon x s m / chartMon x s₀ m = ∏ k, (x ⟨k, s k⟩ / x ⟨k, s₀ k⟩) ^ m k := by
    rw [chartMon, chartMon, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun k _ => (div_zpow _ _ _).symm
  have e' : chartMon (genPt (kap O) Q) s m / chartMon (genPt (kap O) Q) s₀ m =
      ∏ k, (genPt (kap O) Q ⟨k, s k⟩ / genPt (kap O) Q ⟨k, s₀ k⟩) ^ m k := by
    rw [chartMon, chartMon, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun k _ => (div_zpow _ _ _).symm
  have hk : ∀ k, (x ⟨k, s k⟩ / x ⟨k, s₀ k⟩) ^ m k ∈ locAlg x Q ∧
      rs x Q ((x ⟨k, s k⟩ / x ⟨k, s₀ k⟩) ^ m k) =
        (genPt (kap O) Q ⟨k, s k⟩ / genPt (kap O) Q ⟨k, s₀ k⟩) ^ m k := by
    intro k
    obtain ⟨h1, h2⟩ := coord_ratio hPQ k (s k) (s₀ k) (genPt_ne_zero_of_mseg hs₀ k)
    have h0 : rs x Q (x ⟨k, s k⟩ / x ⟨k, s₀ k⟩) ≠ 0 := by
      rw [h2]
      exact div_ne_zero (genPt_ne_zero_of_mseg hs k) (genPt_ne_zero_of_mseg hs₀ k)
    obtain ⟨h3, h4⟩ := zpow_mem_of_rs_ne_zero hPQ h1 h0 (m k)
    exact ⟨h3, by rw [h4, h2]⟩
  rw [e, e']
  exact ⟨prod_mem fun k _ => (hk k).1, by
    rw [rs_prod hPQ _ _ fun k _ => (hk k).1]
    exact Finset.prod_congr rfl fun k _ => (hk k).2⟩

variable (x Q) in

def goodSub (hPQ : redIdeal O (mcIdeal O x) ≤ Q) (s : ∀ k, ι k) : Subalgebra O Ω where
  carrier := {a | a ∈ locAlg x Q ∧ rs x Q a ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s}
  mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨mul_mem ha hb, by rw [rs_mul hPQ ha hb]; exact mul_mem ha' hb'⟩
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨add_mem ha hb, by rw [rs_add hPQ ha hb]; exact add_mem ha' hb'⟩
  algebraMap_mem' c := ⟨Subalgebra.algebraMap_mem _ c, by
    rw [rs_algebraMap hPQ]; exact Subalgebra.algebraMap_mem _ _⟩

theorem chartRing_sub (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k}
    (hs : mseg (genPt (kap O) Q) s ≠ 0) {a : Ω} (ha : a ∈ chartRing O (mseg x) s) :
    a ∈ locAlg x Q ∧ rs x Q a ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s := by
  have h : chartRing O (mseg x) s ≤ goodSub x Q hPQ s := Algebra.adjoin_le (by
    rintro _ ⟨t, rfl⟩
    obtain ⟨h1, h2⟩ := seg_ratio hPQ hs t
    exact ⟨h1, h2 ▸ div_mem_chartRing _ _ _⟩)
  exact h ha

theorem exists_lift (hPQ : redIdeal O (mcIdeal O x) ≤ Q) (s : ∀ k, ι k) {b : FractionRing (MRingOver (kap O) ι ⧸ Q)}
    (hb : b ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s) :
    ∃ a ∈ chartRing O (mseg x) s, a ∈ locAlg x Q ∧ rs x Q a = b := by
  let T : Subalgebra (kap O) (FractionRing (MRingOver (kap O) ι ⧸ Q)) :=
    { carrier := {b | ∃ a ∈ chartRing O (mseg x) s, a ∈ locAlg x Q ∧ rs x Q a = b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
        exact ⟨a * b, mul_mem ha hb, mul_mem ha' hb', rs_mul hPQ ha' hb'⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
        exact ⟨a + b, add_mem ha hb, add_mem ha' hb', rs_add hPQ ha' hb'⟩
      algebraMap_mem' := by
        intro r
        obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective r
        exact ⟨algebraMap O Ω c, Subalgebra.algebraMap_mem _ c, Subalgebra.algebraMap_mem _ c,
          rs_algebraMap hPQ c⟩ }
  have h : chartRing (kap O) (mseg (genPt (kap O) Q)) s ≤ T := Algebra.adjoin_le (by
    rintro _ ⟨t, rfl⟩
    by_cases hs : mseg (genPt (kap O) Q) s = 0
    · refine ⟨0, zero_mem _, zero_mem _, ?_⟩
      simp only [hs, div_zero]
      exact rs_zero hPQ
    · obtain ⟨h1, h2⟩ := seg_ratio hPQ hs t
      exact ⟨_, div_mem_chartRing _ _ _, h1, h2⟩)
  exact h hb

end Chart

end FlagRestrict

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
