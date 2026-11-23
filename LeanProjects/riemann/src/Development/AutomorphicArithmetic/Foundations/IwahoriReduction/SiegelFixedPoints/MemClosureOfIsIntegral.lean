import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntModLevelPrimePowEqAddMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubring
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.InertiaZetaPowers

open Finset

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

private theorem zpow_mem_closure {x : Ω} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) (k : ℤ) :
    x ^ k ∈ Subring.closure {x} := by
  have hxm : x ∈ Subring.closure {x} := Subring.subset_closure (Set.mem_singleton x)
  have hinv : x⁻¹ = x ^ (m - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hm, hx]
  cases k with
  | ofNat a =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hxm a
  | negSucc a =>
    rw [zpow_negSucc, ← inv_pow, hinv]
    exact pow_mem (pow_mem hxm _) _

private theorem zeta_pow (ε : Ω →+* ℂ) (l N L : ℕ) [NeZero l] [NeZero N] :
    eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ N = zt ε l L := by
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  apply ε.injective
  rw [map_pow, zt, (eOm_props ε ε.injective).1, (eOm_props ε ε.injective).1, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

private theorem zeta_zpow_mem (ε : Ω →+* ℂ) (l N L : ℕ) [NeZero l] [NeZero N] (k : ℤ) :
    eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ ((N : ℤ) * k) ∈ Subring.closure {zt ε l L} := by
  rw [zpow_mul, zpow_natCast, zeta_pow]
  exact zpow_mem_closure (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne l))) (IsNTr.isPrimitiveRoot_zt ε l L).pow_eq_one k

private theorem closure_le_adjoin (ε : Ω →+* ℂ) (l L : ℕ) {y : Ω} (h : y ∈ Subring.closure {zt ε l L}) :
    y ∈ IntermediateField.adjoin ℚ {zt ε l L} :=
  (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l L}).toSubring)).2
    (IntermediateField.subset_adjoin ℚ _) h

private theorem eisF_mem (F : IntermediateField ℚ Ω) (j M N : ℕ) (ζ : Ω) (a₁ b : ℤ) (n : ℕ)
    (h : ∀ k : ℤ, ζ ^ ((N : ℤ) * k) ∈ F) : eisF j M ζ a₁ ((N : ℤ) * b) n ∈ F := by
  have hq : ∀ q : ℚ, (q : Ω) ∈ F := fun q => by simpa using F.algebraMap_mem q
  have hh : (1 / 2 : Ω) ∈ F := by simpa using hq (1 / 2)
  unfold eisF
  split_ifs with h0
  · unfold const0
    split_ifs
    · exact div_mem (mul_mem hh (add_mem (one_mem _) (h b))) (sub_mem (one_mem _) (h b))
    · exact hq _
    · exact neg_mem (hq _)
  · unfold coefPos
    refine sum_mem fun d _ => sub_mem ?_ ?_
    · split_ifs
      · refine mul_mem (pow_mem (div_mem (natCast_mem F _) (natCast_mem F _)) _) ?_
        rw [show (N : ℤ) * b * (d : ℤ) = (N : ℤ) * (b * d) by ring]
        exact h _
      · exact zero_mem _
    · split_ifs
      · refine mul_mem (pow_mem (neg_mem (div_mem (natCast_mem F _) (natCast_mem F _))) _) ?_
        rw [show -((N : ℤ) * b * (d : ℤ)) = (N : ℤ) * (-(b * d)) by ring]
        exact h _
      · exact zero_mem _

private theorem zpow_memF (F : IntermediateField ℚ Ω) {x : Ω} (hx : x ∈ F) (k : ℤ) : x ^ k ∈ F := by
  cases k with
  | ofNat a =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hx a
  | negSucc a =>
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hx _)

private theorem smF_mem (F : IntermediateField ℚ Ω) (c : ℤ) (j M N : ℕ) (ζ : Ω) (a₁ a₂ : ℤ) (n : ℕ)
    (hd : (N : ℤ) ∣ a₂) (h : ∀ k : ℤ, ζ ^ ((N : ℤ) * k) ∈ F) : smF c j M ζ a₁ a₂ n ∈ F := by
  obtain ⟨b, rfl⟩ := hd
  unfold smF
  refine sub_mem (mul_mem (pow_mem (intCast_mem F c) _) (eisF_mem F j M N ζ a₁ b n h))
    (mul_mem (zpow_memF F (intCast_mem F c) _) ?_)
  rw [show c * ((N : ℤ) * b) = (N : ℤ) * (c * b) by ring]
  exact eisF_mem F j M N ζ _ _ n h

private theorem mem_closure_of_isIntegral (ε : Ω →+* ℂ) (l L : ℕ) [Fact l.Prime] [CharZero Ω] {y : Ω}
    (hy : y ∈ IntermediateField.adjoin ℚ {zt ε l L}) (hi : IsIntegral ℤ y) :
    y ∈ Subring.closure {zt ε l L} := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero (l ^ L) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz := IsNTr.isPrimitiveRoot_zt ε l L
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI hcyc : IsCyclotomicExtension {l ^ L} ℚ (IntermediateField.adjoin ℚ {zt ε l L}) :=
    by
      convert hz.intermediateField_adjoin_isCyclotomicExtension ℚ
      · rfl
      · exact Subsingleton.elim _ _
  let zF : IntermediateField.adjoin ℚ {zt ε l L} := ⟨zt ε l L, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hzF : IsPrimitiveRoot zF (l ^ L) :=
    IsPrimitiveRoot.of_map_of_injective (f := (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype) hz
      (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.injective
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p := l) (k := L) (ζ := zF) hzF
  have hi' : IsIntegral ℤ (⟨y, hy⟩ : IntermediateField.adjoin ℚ {zt ε l L}) :=
    (isIntegral_algHom_iff ((IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.toIntAlgHom)
      (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.injective).1 hi
  obtain ⟨t, ht⟩ := hcl.isIntegral_iff.1 hi'
  have key : ∀ s ∈ Algebra.adjoin ℤ ({zF} : Set (IntermediateField.adjoin ℚ {zt ε l L})),
      ((s : IntermediateField.adjoin ℚ {zt ε l L}) : Ω) ∈ Subring.closure {zt ε l L} := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact Subring.subset_closure rfl
    | algebraMap r => simpa using intCast_mem (Subring.closure {zt ε l L}) r
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  have e : y = (((t : IntermediateField.adjoin ℚ {zt ε l L})) : Ω) := by
    have := congrArg (fun s : IntermediateField.adjoin ℚ {zt ε l L} => (s : Ω)) ht
    exact this.symm
  rw [e]
  exact key _ t.2

private theorem inZl_of_mem {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {y : Ω} (h : y ∈ Subring.closure {zt ε l L}) :
    InZl ε l L y :=
  ⟨1, fun h1 => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h1), by simpa using h⟩

private theorem inZl_add {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {a b : Ω} (ha : InZl ε l L a) (hb : InZl ε l L b) :
    InZl ε l L (a + b) := by
  obtain ⟨D, hD, h⟩ := ha
  obtain ⟨D', hD', h'⟩ := hb
  refine ⟨D * D', fun hd => ((Fact.out : l.Prime).dvd_mul.1 hd).elim hD hD', ?_⟩
  have e : ((D * D' : ℕ) : Ω) * (a + b) = (D' : Ω) * ((D : Ω) * a) + (D : Ω) * ((D' : Ω) * b) := by
    push_cast
    ring
  rw [e]
  exact add_mem (mul_mem (natCast_mem _ _) h) (mul_mem (natCast_mem _ _) h')

private theorem inZl_mul {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {a b : Ω} (ha : InZl ε l L a) (hb : InZl ε l L b) :
    InZl ε l L (a * b) := by
  obtain ⟨D, hD, h⟩ := ha
  obtain ⟨D', hD', h'⟩ := hb
  refine ⟨D * D', fun hd => ((Fact.out : l.Prime).dvd_mul.1 hd).elim hD hD', ?_⟩
  have e : ((D * D' : ℕ) : Ω) * (a * b) = ((D : Ω) * a) * ((D' : Ω) * b) := by
    push_cast
    ring
  rw [e]
  exact mul_mem h h'

private theorem inZl_sum {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → Ω)
    (h : ∀ i ∈ s, InZl ε l L (f i)) : InZl ε l L (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inZl_of_mem (zero_mem _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inZl_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end UpperTheory.Kd.L.InertiaZetaPowers

namespace UpperTheory.Kd.L.InertiaZetaPowers

open Finset

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]

private theorem smF_one_mem (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c L : ℕ) (hL : 1 ≤ L)
    (hc : Nat.Coprime c (6 * l * N)) (a a₂ : ℤ) (ha : ¬ (l : ℤ) ∣ a) (h₂ : (N : ℤ) ∣ a₂) (r : ℕ) :
    smF (c : ℤ) 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a a₂ r ∈ Subring.closure {zt ε l L} := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, rfl⟩ := h₂
  have hcN : Nat.Coprime c N := hc.coprime_dvd_right (Dvd.intro_left _ rfl)
  have hcl : Nat.Coprime c l := hc.coprime_dvd_right ((Dvd.intro_left _ rfl : l ∣ 6 * l).mul_right N)
  refine smF_one_mem_subring Ω _ c (N * l ^ L) _ a _
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne l))))
    (Nat.Coprime.mul_right hcN (Nat.Coprime.pow_right L hcl)) ?_ (zeta_zpow_mem ε l N L b) ?_ r
  · intro h
    refine ha (dvd_trans ?_ h)
    exact_mod_cast Dvd.dvd.mul_left (dvd_pow_self l (by omega : L ≠ 0)) N
  · rw [show -((N : ℤ) * b) = (N : ℤ) * (-b) by ring]
    exact zeta_zpow_mem ε l N L _

private theorem cong_step (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c L w : ℕ) (hw : 1 ≤ w)
    (h2 : l ≠ 2) (hlN : ¬ l ∣ N) (hc : Nat.Coprime c (6 * l * N)) (hb : (w + 1) ^ 2 * l ≤ l ^ L)
    (α a₁ a₂ : ℤ) (h0 : 0 ≤ α) (hlt : α < (l : ℤ) ^ L) (hcong : a₁ ≡ N * α [ZMOD (l : ℤ) ^ L]) (h₂ : (N : ℤ) ∣ a₂) (r : ℕ) :
    ∃ β : Ω, InZl ε l L β ∧ (l : Ω) ^ (L - 1) * β =
      (α : Ω) ^ w * smF (c : ℤ) 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a₁ a₂ r -
        (l : Ω) ^ (L * w) * smF (c : ℤ) (w + 1) (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a₁ a₂ r := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hζ : IsPrimitiveRoot (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (N * l ^ L) :=
    isPrimitiveRoot_eOm ε (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (NeZero.ne l)))
  have hcl : Nat.Coprime c l := hc.coprime_dvd_right ((Dvd.intro_left _ rfl : l ∣ 6 * l).mul_right N)
  have hlc : ¬ (l : ℤ) ∣ (c : ℤ) := fun h =>
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hcl.symm) (Int.natCast_dvd_natCast.1 h)
  obtain ⟨D, hD, hint⟩ := GlobalTheory.EisCongGen.smF_congr_gen l N L (w + 1) Ω _ h2 hζ
    (Nat.pos_of_ne_zero (NeZero.ne N)) hlN (by omega) hb (c : ℤ) hlc α a₁ a₂ h0 hlt hcong r
  rw [Nat.add_sub_cancel] at hint
  have hF : ∀ k : ℤ, eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ ((N : ℤ) * k) ∈ IntermediateField.adjoin ℚ {zt ε l L} :=
    fun k => closure_le_adjoin ε l L (zeta_zpow_mem ε l N L k)
  refine ⟨_, ?_, mul_div_cancel₀ _ (pow_ne_zero _ hl0)⟩
  refine ⟨D, hD, mem_closure_of_isIntegral ε l L ?_ ?_⟩
  · refine mul_mem (natCast_mem _ _) (div_mem (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) ?_)
      (mul_mem (pow_mem (natCast_mem _ _) _) ?_)) (pow_mem (natCast_mem _ _) _))
    · exact smF_mem _ _ _ _ N _ _ _ _ h₂ hF
    · exact smF_mem _ _ _ _ N _ _ _ _ h₂ hF
  · rw [← mul_div_assoc]
    exact hint

private theorem comb (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (L n w m : ℕ) (hnL : n < L) (A₁ A₂ B : ℕ → Ω)
    (α u : ℤ) (e : ℕ) (he : (e : ℤ) = α ^ w + (l : ℤ) ^ n * u)
    (hA : ∀ r, A₁ r ∈ Subring.closure {zt ε l L}) (hB : ∀ r, B r ∈ Subring.closure {zt ε l L})
    (hβ : ∀ r, ∃ β : Ω, InZl ε l L β ∧ (l : Ω) ^ (L - 1) * β = (α : Ω) ^ w * A₁ r - (l : Ω) ^ (L * w) * A₂ r) :
    ∃ E : Ω, InZl ε l L E ∧ (e : Ω) * cmul A₁ B m = (l : Ω) ^ (L * w) * cmul A₂ B m + (l : Ω) ^ n * E := by
  choose β hβ₁ hβ₂ using hβ
  refine ⟨∑ i ∈ range (m + 1), ((u : Ω) * A₁ i + (l : Ω) ^ (L - 1 - n) * β i) * B (m - i), ?_, ?_⟩
  · refine inZl_sum _ _ fun i _ => inZl_mul (inZl_add (inZl_of_mem (mul_mem (intCast_mem _ _) (hA i)))
      (inZl_mul (inZl_of_mem (pow_mem (natCast_mem _ _) _)) (hβ₁ i))) (inZl_of_mem (hB _))
  · have e1 : (e : Ω) = (α : Ω) ^ w + (l : Ω) ^ n * (u : Ω) := by
      have := congrArg (Int.cast : ℤ → Ω) he
      push_cast at this
      exact this
    have e2 : (l : Ω) ^ n * (l : Ω) ^ (L - 1 - n) = (l : Ω) ^ (L - 1) := by
      rw [← pow_add]
      congr 1
      omega
    unfold cmul
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    linear_combination (A₁ i * B (m - i)) * e1 - B (m - i) * hβ₂ i - (β i * B (m - i)) * e2

private theorem coefQ_nat (M : ℕ) (f : ℕ → Ω) (i : ℕ) : coefQ M f (i : ℚ) = f (M * i) := by
  have e : (i : ℚ) * (M : ℚ) = ((M * i : ℕ) : ℚ) := by
    push_cast
    ring
  unfold coefQ
  rw [e, if_pos ⟨Nat.cast_nonneg _, Rat.den_natCast _⟩, Rat.num_natCast, Int.toNat_natCast]

private theorem ex_eq (l n L w : ℕ) [Fact l.Prime] (hnL : n < L) (g : SL(2, ℤ)) :
    ∃ u : ℤ, ((ex l n w g : ℕ) : ℤ) = (en g 0 0 % (l : ℤ) ^ L) ^ w + (l : ℤ) ^ n * u := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (((((en g 0 0 : ℤ) : ZMod (l ^ n)).val : ℕ) : ℤ) : ZMod (l ^ n)) = ((en g 0 0 : ℤ) : ZMod (l ^ n)) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h2 := (ZMod.intCast_eq_intCast_iff _ _ (l ^ n)).1 h1
  have h3 : (l : ℤ) ^ n ∣ (l : ℤ) ^ L := pow_dvd_pow _ hnL.le
  have h4 : en g 0 0 % (l : ℤ) ^ L ≡ en g 0 0 [ZMOD (l : ℤ) ^ n] := Int.emod_emod_of_dvd _ h3
  have h5 : en g 0 0 % (l : ℤ) ^ L ≡ (((en g 0 0 : ℤ) : ZMod (l ^ n)).val : ℤ) [ZMOD (l : ℤ) ^ n] := by
    refine h4.trans (Int.ModEq.symm ?_)
    simpa using h2
  obtain ⟨u, hu⟩ := Int.modEq_iff_dvd.1 (h5.pow w)
  refine ⟨u, ?_⟩
  unfold ex
  push_cast
  linarith

end UpperTheory.Kd.L.InertiaZetaPowers

open UpperTheory.Kd.L.InertiaZetaPowers in
theorem UpperTheory.Kd.L.inzl :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (L n w : ℕ), 1 ≤ w → n < L → ∀ g : SL(2, ℤ), ¬ (l : ℤ) ∣ en g 0 0 → ¬ (l : ℤ) ∣ en g 1 0 → ∀ i : ℕ, InZl ε l L (EE ε l L N x c d g (i : ℚ)) ∧ ((w + 1) ^ 2 * l ≤ l ^ L → ∃ E : Ω, InZl ε l L E ∧ (ex l n w g : Ω) * EE ε l L N x c d g (i : ℚ) = (l : Ω) ^ (L * w) * cmul (smF c (w + 1) (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF d 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) + (l : Ω) ^ n * E) := by
  intro Ω _ _ _ _ ε l _ N _ c d gm hP x L n w hw hnL g hg0 hg1 i
  have hL : 1 ≤ L := by omega
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hlL : (l : ℤ) ∣ (l : ℤ) ^ L := dvd_pow_self _ (by omega)
  have hNl : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => hP.cop (Int.natCast_dvd_natCast.1 h)
  have ha : ¬ (l : ℤ) ∣ en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) := by
    intro h
    rcases hlp.dvd_or_dvd h with h | h
    · exact hg0 h
    · exact hNl ((dvd_add_left (hlL.mul_left _)).1 h)
  have hb : ¬ (l : ℤ) ∣ en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0 := fun h =>
    hg1 ((dvd_add_right (hlL.mul_left _)).1 h)
  have hA := smF_one_mem ε l N c L hL hP.cc _ ((N : ℤ) ^ 2 * en g 0 1) ha ⟨(N : ℤ) * en g 0 1, by ring⟩
  have hB := smF_one_mem ε l N d L hL hP.dc _ ((N : ℤ) * en g 1 1) hb ⟨en g 1 1, rfl⟩
  have hEE : EE ε l L N x c d g (i : ℚ) = cmul (smF c 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF d 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) :=
    coefQ_nat _ _ _
  rw [hEE]
  refine ⟨inZl_of_mem (sum_mem fun r _ => mul_mem (hA r) (hB _)), fun hbd => ?_⟩
  obtain ⟨u, hu⟩ := ex_eq l n L w hnL g
  have hlpos : (0 : ℤ) < (l : ℤ) ^ L := by
    have := (Fact.out : l.Prime).pos
    positivity
  refine comb ε l L n w _ hnL _ _ _ (en g 0 0 % (l : ℤ) ^ L) u _ hu hA hB fun r => ?_
  refine cong_step ε l N c L w hw hP.odd hP.cop hP.cc hbd _ _ _ (Int.emod_nonneg _ hlpos.ne') (Int.emod_lt_of_pos _ hlpos) ?_
    ⟨(N : ℤ) * en g 0 1, by ring⟩ r
  refine Int.modEq_iff_dvd.2 ⟨-(N : ℤ) * (en g 0 0 / (l : ℤ) ^ L) - en g 0 0 * ((x.val : ℤ) * (topT l L N : ℤ)), ?_⟩
  rw [Int.emod_def]
  ring
