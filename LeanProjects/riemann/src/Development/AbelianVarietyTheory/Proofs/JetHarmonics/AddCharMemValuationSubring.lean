import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.FourierCoeffIntSt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PerfectPairings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings

namespace GlobalTheory.FourierChainCompare

section Duality

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]

theorem linearIndependent_addChar (A K : Type) [AddCommGroup A] [Field K] :
    LinearIndependent K (fun χ : AddChar A K => (χ : A → K)) :=
  (linearIndependent_monoidHom (Multiplicative A) K).comp AddChar.toMonoidHomEquiv
    AddChar.toMonoidHomEquiv.injective

theorem finite_addChar (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    Finite (AddChar A K) := (linearIndependent_addChar A K).finite

theorem card_addChar_le (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    Nat.card (AddChar A K) ≤ Fintype.card A := by
  haveI := finite_addChar A K
  letI := Fintype.ofFinite (AddChar A K)
  rw [Nat.card_eq_fintype_card]
  simpa using (linearIndependent_addChar A K).fintype_card_le_finrank

theorem perfect_flip {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    IsPerfectPairing (fun t a => e a t) :=
  ⟨fun t t' a => he.add_right a t t', fun t a a' => he.add_left a a' t, he.nondeg_right,
    he.nondeg_left⟩

theorem pairing_zero {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) : e 0 t = 1 := by
  have h := he.add_left 0 0 t
  rw [add_zero] at h
  exact left_eq_mul.mp h

def chr {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) : AddChar A K where
  toFun a := ((e a t : Kˣ) : K)
  map_zero_eq_one' := by rw [pairing_zero he, Units.val_one]
  map_add_eq_mul' a a' := by rw [he.add_left, Units.val_mul]

theorem chr_apply {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) (a : A) :
    chr he t a = ((e a t : Kˣ) : K) := rfl

theorem chr_neg {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) (a : A) :
    chr he t (-a) = (((e a t)⁻¹ : Kˣ) : K) := by
  rw [AddChar.map_neg_eq_inv, chr_apply, Units.val_inv_eq_inv_val]

theorem chr_injective {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Function.Injective (chr he) := by
  intro t t' h
  refine sub_eq_zero.mp (he.nondeg_right _ fun a => ?_)
  have h1 : e a t = e a t' := Units.ext (DFunLike.congr_fun h a)
  have h2 := he.add_right a (t - t') t'
  rw [sub_add_cancel, h1] at h2
  exact right_eq_mul.mp h2

variable [Fintype A] [Fintype B]

theorem card_le_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Fintype.card B ≤ Nat.card (AddChar A K) := by
  haveI := finite_addChar A K
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective _ (chr_injective he)

theorem card_eq_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Fintype.card A = Fintype.card B :=
  le_antisymm ((card_le_of_perfect (perfect_flip he)).trans (card_addChar_le B K))
    ((card_le_of_perfect he).trans (card_addChar_le A K))

theorem card_addChar_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Nat.card (AddChar A K) = Fintype.card A :=
  le_antisymm (card_addChar_le A K) ((card_eq_of_perfect he).le.trans (card_le_of_perfect he))

def chrEquiv {e : A → B → Kˣ} (he : IsPerfectPairing e) : B ≃ AddChar A K :=
  haveI := finite_addChar A K
  Equiv.ofBijective (chr he) ((chr_injective he).bijective_of_nat_card_le (by
    rw [card_addChar_of_perfect he, card_eq_of_perfect he, Nat.card_eq_fintype_card]))

theorem chrEquiv_apply {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) :
    chrEquiv he t = chr he t := rfl

omit [Fintype B] in
theorem card_ne_zero_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    (Fintype.card A : K) ≠ 0 := by
  intro h
  obtain ⟨p, hp⟩ := CharP.exists K
  have hd : p ∣ Fintype.card A := (CharP.cast_eq_zero_iff K p _).mp h
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact Fintype.card_ne_zero (zero_dvd_iff.mp hd)
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card p hd
  have h0 : a = 0 := he.nondeg_left a fun t => by
    have h1 : chr he t a ^ p = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, ← ha, addOrderOf_nsmul_eq_zero, AddChar.map_zero_eq_one]
    have h2 : (chr he t a - 1) ^ p = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff hp0 |>.mp h2))
  rw [h0, addOrderOf_zero] at ha
  exact (Fact.out : p.Prime).one_lt.ne ha

def ManyChars (A K : Type) [AddCommGroup A] [Fintype A] [Field K] : Prop :=
  (Fintype.card A : K) ≠ 0 ∧ Nat.card (AddChar A K) = Fintype.card A

theorem manyChars_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) : ManyChars A K :=
  ⟨card_ne_zero_of_perfect he, card_addChar_of_perfect he⟩

def evalPairing (A K : Type) [AddCommGroup A] [Field K] (a : A)
    (χ : Additive (Multiplicative A →* Kˣ)) : Kˣ :=
  (Additive.toMul χ) (Multiplicative.ofAdd a)

theorem finite_unitChar (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    Finite (Additive (Multiplicative A →* Kˣ)) :=
  haveI := finite_addChar A K
  Finite.of_equiv (AddChar A K)
    ((AddChar.toMonoidHomEquiv.trans MonoidHom.toHomUnitsMulEquiv.toEquiv).trans Additive.ofMul)

theorem perfect_eval (h : Nat.card (AddChar A K) = Fintype.card A) :
    IsPerfectPairing (evalPairing A K) := by
  classical
  refine ⟨fun a a' t => ?_, fun a t t' => ?_, fun a ha => ?_, fun t ht => ?_⟩
  · simp [evalPairing]
  · simp [evalPairing]
  · haveI := finite_addChar A K
    letI := Fintype.ofFinite (AddChar A K)
    have hs := (linearIndependent_addChar A K).span_eq_top_of_card_eq_finrank
      (by rw [← Nat.card_eq_fintype_card, h]; simp)
    have key : ∀ f : A → K, f a = f 0 := by
      intro f
      have hf : f ∈ Submodule.span K (Set.range fun χ : AddChar A K => (χ : A → K)) := by
        rw [hs]; trivial
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        have := congrArg Units.val (ha (Additive.ofMul χ.toMonoidHom.toHomUnits))
        simpa [evalPairing] using this
      | zero => rfl
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    by_contra hne
    have := key (fun b => if b = 0 then 1 else 0)
    simp [hne] at this
  · ext a
    exact congrArg Units.val (ht (Multiplicative.toAdd a))

theorem manyChars_iff_eval (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    ManyChars A K ↔ IsPerfectPairing (evalPairing A K) := by
  refine ⟨fun h => perfect_eval h.2, fun h => ?_⟩
  haveI := finite_unitChar A K
  letI := Fintype.ofFinite (Additive (Multiplicative A →* Kˣ))
  exact manyChars_of_perfect h

theorem manyChars_iff_exists (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    ManyChars A K ↔ ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (e : A → B → Kˣ),
      IsPerfectPairing e := by
  constructor
  · intro h
    haveI := finite_unitChar A K
    exact ⟨_, inferInstance, Fintype.ofFinite _, _, perfect_eval h.2⟩
  · rintro ⟨B, _, _, e, he⟩
    exact manyChars_of_perfect he

end Duality

section Fourier

variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]

theorem fourierCoeff_eq {e : A → B → Kˣ} (he : IsPerfectPairing e) (φ : A → K) (t : B) :
    IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t = (Fintype.card A : K)⁻¹ * ∑ b, φ b * chr he t (-b) := by
  simp only [IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff, chr_neg, card_eq_of_perfect he]

theorem inversionSum_eq [Fintype (AddChar A K)] {e : A → B → Kˣ} (he : IsPerfectPairing e)
    (φ : A → K) (a : A) :
    ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) =
      ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a := by
  rw [← Equiv.sum_comp (chrEquiv he)]
  exact Finset.sum_congr rfl fun t _ => by rw [fourierCoeff_eq he]; rfl

theorem inversion_iff [Fintype (AddChar A K)] {e : A → B → Kˣ} (he : IsPerfectPairing e)
    (φ : A → K) (a : A) :
    (φ a = ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a) ↔
      φ a = ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) := by
  rw [inversionSum_eq he]

theorem coeff_chr_of_inversion [DecidableEq B] {e : A → B → Kˣ} (he : IsPerfectPairing e) (t₀ : B)
    (h : ∀ a, ((e a t₀ : Kˣ) : K) =
      ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t * ((e a t : Kˣ) : K)) (t : B) :
    IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t = if t = t₀ then 1 else 0 := by
  have li := Fintype.linearIndependent_iff.mp
    ((linearIndependent_addChar A K).comp _ (chr_injective he))
    (fun t => IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t - if t = t₀ then 1 else 0)
    (by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, chr_apply, smul_eq_mul,
        sub_mul, Finset.sum_sub_distrib, ← h a]
      simp)
  exact sub_eq_zero.mp (li t)

theorem fourierInv_iff : FourierInvSt ↔ FourierInversion := by
  classical
  constructor
  · intro H A B K _ _ _ _ _ e he
    haveI := finite_addChar A K
    letI := Fintype.ofFinite (AddChar A K)
    have hm := manyChars_of_perfect he
    have hinv : ∀ (φ : A → K) (a : A),
        φ a = ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t * ((e a t : Kˣ) : K) := fun φ a =>
      (inversion_iff he φ a).mp (H A K hm.1 (by rw [← Nat.card_eq_fintype_card, hm.2]) φ a)
    have hc := fun t₀ : B => coeff_chr_of_inversion he t₀ (hinv _)
    refine ⟨card_eq_of_perfect he, card_eq_of_perfect he ▸ hm.1, hinv,
      fun t₀ => ⟨by rw [hc, if_pos rfl], fun t ht => by rw [hc, if_neg ht]⟩, fun V _ _ θ t₀ => ?_⟩
    simp [onDatum, hc]
  · intro H A _ _ K _ _ h1 h2 φ a
    obtain ⟨B, _, _, e, he⟩ :=
      (manyChars_iff_exists A K).mp ⟨h1, by rw [Nat.card_eq_fintype_card, h2]⟩
    exact (inversion_iff he φ a).mpr ((H A B K e he).2.2.1 φ a)

theorem enoughCharacters_iff : EnoughCharacters ↔
    ∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K]
      [HasEnoughRootsOfUnity K (AddMonoid.exponent A)], ManyChars A K :=
  ⟨fun H A K _ _ _ _ => (manyChars_iff_eval A K).mpr (H A K).2,
    fun H A K _ _ _ _ => ⟨finite_unitChar A K, (manyChars_iff_eval A K).mp (H A K)⟩⟩

theorem denominators_iff {e : A → B → Kˣ} (he : IsPerfectPairing e) (O : Subring K) (φ : A → K)
    (t : B) :
    ((Fintype.card A : K) * ((Fintype.card A : K)⁻¹ * ∑ b, φ b * chr he t (-b)) ∈ O ∨
      (Fintype.card A : K) = 0) ↔ ((Fintype.card B : ℕ) : K) * IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t ∈ O := by
  rw [or_iff_left (card_ne_zero_of_perfect he), fourierCoeff_eq he, card_eq_of_perfect he]

theorem or_card_eq_zero_iff (O : Subring K) (n c : K) : (n * c ∈ O ∨ n = 0) ↔ n * c ∈ O :=
  or_iff_left_of_imp fun h => by rw [h, zero_mul]; exact O.zero_mem

theorem values_iff {e : A → B → Kˣ} (he : IsPerfectPairing e) (O : Subring K) :
    (∀ (χ : AddChar A K) a, χ a ∈ O) ↔ ∀ a t, ((e a t : Kˣ) : K) ∈ O := by
  refine ⟨fun h a t => h (chr he t) a, fun h χ a => ?_⟩
  obtain ⟨t, rfl⟩ := (chrEquiv he).surjective χ
  exact h a t

theorem addChar_mem_valuationSubring (O : ValuationSubring K) (χ : AddChar A K) (a : A) :
    χ a ∈ O := by
  have h1 : χ a ^ Fintype.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  rw [← O.valuation_le_one_iff]
  have h2 : O.valuation (χ a) ^ Fintype.card A = 1 := by rw [← map_pow, h1, map_one]
  exact ((pow_eq_one_iff_of_nonneg zero_le' Fintype.card_ne_zero).mp h2).le

def CoeffIntAllChars : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (K : Type) [Field K] (O : Subring K) (φ : A → K),
    ManyChars A K → (∀ a, φ a ∈ O) → (∀ (χ : AddChar A K) a, χ a ∈ O) → ∀ χ : AddChar A K,
      (Fintype.card A : K) * ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) ∈ O ∨
        (Fintype.card A : K) = 0

theorem coeffIntAllChars_of (H : FourierCoeffIntSt) : CoeffIntAllChars :=
  fun A _ _ K _ O φ _ hφ hχ χ => H A K O φ hφ χ (hχ χ)

theorem coeffIntAllChars_iff : CoeffIntAllChars ↔ FourierDenominators := by
  constructor
  · intro H A B K _ _ _ _ _ e he φ
    have h1 : ∀ O : Subring K, (∀ a, φ a ∈ O) → (∀ a t, ((e a t : Kˣ) : K) ∈ O) →
        ∀ t, ((Fintype.card B : ℕ) : K) * IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t ∈ O := fun O hφ hO t =>
      (denominators_iff he O φ t).mp
        (H A K O φ (manyChars_of_perfect he) hφ ((values_iff he O).mpr hO) (chr he t))
    refine ⟨h1, fun O hφ => ?_⟩
    have h2 : ∀ t, ((Fintype.card B : ℕ) : K) * IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t ∈ O :=
      h1 O.toSubring hφ fun a t => addChar_mem_valuationSubring O (chr he t) a
    refine ⟨h2, fun hu t => ?_⟩
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have h3 : (v : K) * ((Fintype.card B : ℕ) : K) = 1 := by
      simpa using congrArg (fun x : O => (x : K)) hv
    have h4 := O.mul_mem _ _ v.2 (h2 t)
    rwa [← mul_assoc, h3, one_mul] at h4
  · intro H A _ _ K _ O φ hm hφ hχ χ
    obtain ⟨B, _, _, e, he⟩ := (manyChars_iff_exists A K).mp hm
    obtain ⟨t, rfl⟩ := (chrEquiv he).surjective χ
    exact (denominators_iff he O φ t).mpr
      ((H A B K e he φ).1 O hφ ((values_iff he O).mp hχ) t)

end Fourier

section Chain

variable {R : Type} [CommRing R] {d : ℕ}

theorem mulN_eq_mulNat (G : FGLaw R d) (n : ℕ) : mulN G n = mulNat G n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mulN, ih, mulNat_succ]

theorem nChain_iff : NChainSt ↔ ChainNat := by
  constructor
  · intro H R _ d G ι _ u P k hP n f
    rw [← mulN_eq_mulNat]
    exact H R d G n u P k hP f
  · intro H R _ d G n ι _ u P k hP f
    rw [mulN_eq_mulNat]
    exact H R d G ι u P k hP n f

theorem act_zero {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : A.act 0 = 0 := by
  have hc := A.const 0
  have h1 : A.act 0 = G.add (A.act 0) (A.act 0) := by rw [← A.add_act, add_zero]
  have h2 : A.act 0 = comp1 (A.act 0) (A.act 0) := by rw [← A.mul_act, mul_zero]
  have h3 : dLin (A.act 0) = 0 := by
    have := GlobalTheory.FormalMulN.dLin_add G hc hc
    rw [← h1] at this
    exact left_eq_add.mp this
  have h4 : ∀ i, 2 ≤ (A.act 0 i).order := fun i =>
    GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
      obtain ⟨j0, j⟩ := j
      obtain rfl : j0 = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun h3 i) j⟩
  have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (A.act 0 i).order := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
        (a := fun p : Fin 1 × Fin d => (![A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
        (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
        (fun p => by simpa using ih p.2) (h4 i)
      rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
      rw [congrFun h2 i]
      exact this
  funext i
  exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i

theorem act_natCast {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) (n : ℕ) :
    A.act (((n : ℤ) : O)) = mulN G n := by
  rw [Int.cast_natCast]
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, mulN]
  | succ n ih => rw [Nat.cast_succ, A.add_act, A.one_act, ih, mulN]

theorem chainInt_natCast_iff {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (P : MvPolynomial ι R) (k n : ℕ) (f : PS R 1 d) :
    (constantCoeff (DpolyOf G.F u P (ev ![mulN G n] f)) =
        (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)) ↔
      constantCoeff (DpolyOf G.F u P (ev ![A.act (((n : ℤ) : O))] f)) =
        (((n : ℤ) : R)) ^ k * constantCoeff (DpolyOf G.F u P f) := by
  rw [act_natCast, Int.cast_natCast]

def ChainIntOn (s : Set ℤ) : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (O : Type) [CommRing O] (A : OAct O G)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (P : MvPolynomial ι R) (k : ℕ),
      P.IsHomogeneous k → ∀ n ∈ s, ∀ f : PS R 1 d,
        constantCoeff (DpolyOf G.F u P (ev ![A.act (n : O)] f)) =
          (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)

theorem chainIntOn_nonneg (H : NChainSt) : ChainIntOn {n | 0 ≤ n} := by
  intro R _ d G O _ A ι _ u P k hP n hn f
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact (chainInt_natCast_iff A u P k m f).mp (H R d G m u P k hP f)

theorem chainInt_iff_neg_one (H : NChainSt) : ChainInt ↔ ChainIntOn {-1} := by
  refine ⟨fun H' R _ d G O _ A ι _ u P k hP n _ f => H' R d G O A ι u P k hP n f, fun H' => ?_⟩
  intro R _ d G O _ A ι _ u P k hP n f
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact chainIntOn_nonneg H R d G O A ι u P k hP m (Int.natCast_nonneg m) f
  · have e : ev ![A.act ((-(m : ℤ) : ℤ) : O)] f =
        ev ![A.act ((-1 : ℤ) : O)] (ev ![A.act ((m : ℤ) : O)] f) := by
      rw [GlobalTheory.GaugeAdjoint.ev_ev_one (A.const _) (GlobalTheory.GaugeAdjoint.const_one (A.const _)),
        show ((-(m : ℤ) : ℤ) : O) = ((m : ℤ) : O) * ((-1 : ℤ) : O) by push_cast; ring, A.mul_act]
      rfl
    rw [e, H' R d G O A ι u P k hP (-1) rfl,
      chainIntOn_nonneg H R d G O A ι u P k hP m (Int.natCast_nonneg m) f, ← mul_assoc, ← mul_pow]
    push_cast
    rw [neg_one_mul]

end Chain

theorem compare :
    (∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K],
      ManyChars A K ↔ ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (e : A → B → Kˣ),
        IsPerfectPairing e) ∧
    (∀ (A B K : Type) [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [Field K]
      (e : A → B → Kˣ), IsPerfectPairing e → ∃ c : B ≃ AddChar A K,
        (∀ t a, c t a = ((e a t : Kˣ) : K)) ∧ ∀ (φ : A → K) (t : B),
          IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t = (Fintype.card A : K)⁻¹ * ∑ b, φ b * c t (-b)) ∧
    (FourierInvSt ↔ FourierInversion) ∧
    (EnoughCharacters ↔ ∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K]
      [HasEnoughRootsOfUnity K (AddMonoid.exponent A)], ManyChars A K) ∧
    (FourierCoeffIntSt → CoeffIntAllChars) ∧ (CoeffIntAllChars ↔ FourierDenominators) ∧
    (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ), mulN G n = mulNat G n) ∧
    (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (O : Type) [CommRing O] (A : OAct O G)
      (n : ℕ), A.act (((n : ℤ) : O)) = mulN G n) ∧
    (NChainSt ↔ ChainNat) ∧ (NChainSt → ChainIntOn {n | 0 ≤ n}) ∧
    (NChainSt → (ChainInt ↔ ChainIntOn {-1})) :=
  ⟨manyChars_iff_exists,
    fun _ _ _ _ _ _ _ _ _ he => ⟨chrEquiv he, fun _ _ => rfl, fourierCoeff_eq he⟩,
    fourierInv_iff, enoughCharacters_iff, coeffIntAllChars_of, coeffIntAllChars_iff,
    fun _ _ _ => mulN_eq_mulNat, fun _ _ _ _ _ _ => act_natCast, nChain_iff, chainIntOn_nonneg,
    chainInt_iff_neg_one⟩

end GlobalTheory.FourierChainCompare
