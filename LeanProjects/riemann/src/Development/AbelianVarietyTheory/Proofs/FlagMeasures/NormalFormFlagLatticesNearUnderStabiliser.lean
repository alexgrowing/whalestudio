import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsProdDenominatorUnitriangularFactors
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.PosJ

section Weighted
open LaurentPolynomial
variable {K : Type} [Field K]

def gradedSub (I : ℤ → AddSubgroup K) (h1 : (1 : K) ∈ I 0)
    (hmul : ∀ m n x y, x ∈ I m → y ∈ I n → x * y ∈ I (m + n)) : Subring K[T;T⁻¹] where
  carrier := {f | ∀ n, f.coeff n ∈ I n}
  mul_mem' := by
    intro f g hf hg n
    rw [AddMonoidAlgebra.coeff_mul]
    refine AddSubgroup.sum_mem _ fun a _ => AddSubgroup.sum_mem _ fun b _ => ?_
    dsimp only
    split_ifs with h
    · exact h ▸ hmul _ _ _ _ (hf a) (hg b)
    · exact zero_mem _
  one_mem' := by
    intro n
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · exact h ▸ h1
    · exact zero_mem _
  add_mem' := by
    intro f g hf hg n
    simpa using add_mem (hf n) (hg n)
  zero_mem' := by
    intro n
    simp
  neg_mem' := by
    intro f hf n
    simpa using hf n

theorem mono_mem (I : ℤ → AddSubgroup K) (h1 : (1 : K) ∈ I 0)
    (hmul : ∀ m n x y, x ∈ I m → y ∈ I n → x * y ∈ I (m + n)) (c : K) (m : ℤ) :
    C c * T m ∈ gradedSub I h1 hmul ↔ c ∈ I m := by
  rw [← single_eq_C_mul_T]
  constructor
  · intro h
    have := h m
    rwa [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at this
  · intro h n
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with e
    · exact e ▸ h
    · exact zero_mem _

def sc {α β : Type} (M : Matrix α β K) (p : α → ℤ) (q : β → ℤ) : Matrix α β K[T;T⁻¹] :=
  Matrix.of fun a b => C (M a b) * T (p a + q b)

theorem sc_mul {α : Type} [Fintype α] (M N : Matrix α α K) (p q q' s : α → ℤ) (hq : ∀ a, q a + q' a = 0) :
    sc M p q * sc N q' s = sc (M * N) p s := by
  ext1 a b
  simp only [sc, Matrix.mul_apply, Matrix.of_apply, map_sum, Finset.sum_mul, map_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : p a + s b = (p a + q c) + (q' c + s b) := by linear_combination -hq c
  rw [this, T_add (p a + q c)]
  ring

theorem sc_det {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α K) (p : α → ℤ) :
    (sc M p p).det = C M.det * T (2 * ∑ a, p a) := by
  have hT : ∏ a, (T (p a) : K[T;T⁻¹]) = T (∑ a, p a) := by
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, T_add, ih]
  have h : sc M p p = Matrix.of fun a b => T (p a) *
      (Matrix.of fun a b => T (p b) * ((C : K →+* K[T;T⁻¹]).mapMatrix M) a b) a b := by
    ext1 a b
    simp only [sc, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, T_add]
    ring
  rw [h, Matrix.det_mul_column, Matrix.det_mul_row, ← RingHom.map_det, hT, two_mul, T_add]
  ring

theorem wden (I : ℤ → AddSubgroup K) (h1 : (1 : K) ∈ I 0)
    (hmul : ∀ m n x y, x ∈ I m → y ∈ I n → x * y ∈ I (m + n)) {n l' l : ℕ} (h : l ≤ n) (h' : l' ≤ n)
    (r : ℤ) (k : Fin n → ℤ) (hk : ∀ a, k a = r - (a : ℕ)) (A W B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ I (k a + k b)) (hW : W.det ≠ 0)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0)
    (hc' : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → a ≠ b → A a b = 0)
    (t : K) (ε : Fin n → K) (hε : ∀ b, ε b ∈ I 0) (hε2 : ∀ b, ε b * ε b = 1)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (hrow : ∀ a b : Fin n, l' ≤ (a : ℕ) → (a : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (i : Fin n) (hi' : l' ≤ (i : ℕ)) (hi : (i : ℕ) < l) (j : Fin n) :
    (W.submatrix (Fin.castLE h) (Fin.castLE h)).det * A j i ∈
        I (2 * ∑ a : Fin l, k (Fin.castLE h a) + (k j - k i)) ∧
      (W.submatrix (Fin.castLE h) (Fin.castLE h)).det * (W.submatrix (Fin.castLE h') (Fin.castLE h')).det *
        B i j ∈ I (2 * ∑ a : Fin l, k (Fin.castLE h a) + 2 * ∑ a : Fin l', k (Fin.castLE h' a) +
          (k j - k i)) := by
  set O := gradedSub I h1 hmul
  have gA : ∀ a b : Fin n, a < b → sc A k (-k) a b = 0 := fun a b hab => by simp [sc, hA a b hab]
  have class_group_mod_eq_torsion : ∀ a : Fin n, sc A k (-k) a a = 1 := fun a => by simp [sc, hA1]
  have gB : ∀ a b : Fin n, b < a → sc B (-k) k a b = 0 := fun a b hab => by simp [sc, hB a b hab]
  have gB1 : ∀ a : Fin n, sc B (-k) k a a = 1 := fun a => by simp [sc, hB1]
  have gZ : ∀ a b, (sc A k (-k) * sc W k k * sc B (-k) k) a b ∈ O := fun a b => by
    rw [sc_mul _ _ _ _ _ _ (by simp), sc_mul _ _ _ _ _ _ (by simp)]
    exact (mono_mem I h1 hmul _ _).2 (hZ a b)
  have gW : IsUnit (sc W k k).det := by
    rw [sc_det]
    exact ((IsUnit.mk0 _ hW).map _).mul (isUnit_T _)
  have gc : ∀ a b : Fin n, l ≤ (a : ℕ) → (b : ℕ) < l → sc W k k a b = 0 := fun a b ha hb => by
    simp [sc, hc a b ha hb]
  have gc' : ∀ a b : Fin n, l' ≤ (a : ℕ) → (b : ℕ) < l' → sc W k k a b = 0 := fun a b ha hb => by
    simp [sc, hc' a b ha hb]
  have gAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → sc A k (-k) a b ∈ O := fun a b ha hb => by
    by_cases e : a = b
    · rw [e, class_group_mod_eq_torsion]; exact O.one_mem
    · simp [sc, hAO a b ha hb e]
  have hd : ∀ (m : ℕ) (hm : m ≤ n), ((sc W k k).submatrix (Fin.castLE hm) (Fin.castLE hm)).det =
      C (W.submatrix (Fin.castLE hm) (Fin.castLE hm)).det * T (2 * ∑ a : Fin m, k (Fin.castLE hm a)) :=
    fun m hm => sc_det (W.submatrix (Fin.castLE hm) (Fin.castLE hm)) (fun a => k (Fin.castLE hm a))
  have ht : ∀ a b : Fin n, W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b →
      sc W k k a b = (if (a : ℕ) + b + 1 = l + l' then C t * T (2 * r + 1 - l - l') else 0) * C (ε b) := by
    intro a b e
    simp only [sc, Matrix.of_apply, e]
    split_ifs with e2
    · have : k a + k b = 2 * r + 1 - l - l' := by rw [hk, hk]; omega
      rw [this, map_mul]; ring
    · simp
  have g1 := GlobalTheory.OrbitDenom.low_mem O h _ _ _ gA class_group_mod_eq_torsion gB gB1 gZ gW gc gAO i hi' hi j
  have g2 := GlobalTheory.OrbitDenom.up_mem O h h' _ _ _ gA class_group_mod_eq_torsion gB gB1 gZ gW gc' gAO _ (fun b => C (ε b))
    (fun b => by simpa using (mono_mem I h1 hmul (ε b) 0).2 (hε b))
    (fun b => by rw [← map_mul, hε2, map_one])
    (fun a b hb' hb => ht a b (hcol a b hb' hb)) (fun a b ha' ha => ht a b (hrow a b ha' ha)) i hi' hi j
  rw [hd] at g1
  rw [hd, hd] at g2
  constructor
  · rw [← mono_mem I h1 hmul]
    convert g1 using 1
    simp only [sc, Matrix.of_apply, Pi.neg_apply, T_add, map_mul, sub_eq_add_neg]
    ring
  · rw [← mono_mem I h1 hmul]
    convert g2 using 1
    simp only [sc, Matrix.of_apply, Pi.neg_apply, T_add, map_mul, sub_eq_add_neg]
    ring

end Weighted

section Ipow
variable {K : Type} [Field K] [NumberField K]

theorem ipow_add {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 (m + n) = ipow 𝔡 m * ipow 𝔡 n := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  rw [ipow, ipow, ipow, zpow_add₀ h0, FractionalIdeal.coe_mul]

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  rw [ipow, zpow_zero, FractionalIdeal.coe_one]

theorem ipow_mul {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) {m n : ℤ} {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ ipow 𝔡 (m + n) := by
  rw [ipow_add h]; exact Submodule.mul_mem_mul hx hy

theorem one_mem_ipow (𝔡 : Ideal (𝓞 K)) : (1 : K) ∈ ipow 𝔡 0 := by
  rw [ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩

theorem mem_ipow_of {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (hx : ∀ y ∈ ipow 𝔡 m, y * x ∈ ipow 𝔡 (m + n)) : x ∈ ipow 𝔡 n := by
  have h1 : (1 : K) ∈ ipow 𝔡 (-m) * ipow 𝔡 m := by
    rw [← ipow_add h, neg_add_cancel]; exact one_mem_ipow 𝔡
  have : ∀ u ∈ ipow 𝔡 (-m) * ipow 𝔡 m, u * x ∈ ipow 𝔡 n := by
    intro u hu
    refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have := ipow_mul h ha (hx b hb)
      rwa [neg_add_cancel_left, ← mul_assoc] at this
    · rw [add_mul]; exact add_mem ha hb
  simpa using this 1 h1

variable [StarRing K]

omit [NumberField K] in
theorem star_mem_one {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K y)) :=
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd K).toIntAlgHom
  exact Submodule.mem_one.2 ⟨⟨_, this⟩, rfl⟩

theorem star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (n : ℤ) : ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
  have hm : ∀ m n : ℤ, (∀ x ∈ ipow 𝔡 m, star x ∈ ipow 𝔡 m) → (∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n) →
      ∀ x ∈ ipow 𝔡 (m + n), star x ∈ ipow 𝔡 (m + n) := by
    intro m n hm hn x hx
    rw [ipow_add h] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']; exact ipow_mul h (hm a ha) (hn b hb)
    · rw [star_add]; exact add_mem ha hb
  have h0 : ∀ x ∈ ipow 𝔡 0, star x ∈ ipow 𝔡 0 := by
    rw [ipow_zero]; exact fun x => star_mem_one
  have h1 : ∀ x ∈ ipow 𝔡 1, star x ∈ ipow 𝔡 1 := by
    intro x hx
    rw [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact hs y hy
  have h2 : ∀ x ∈ ipow 𝔡 (-1), star x ∈ ipow 𝔡 (-1) := by
    intro x hx
    refine mem_ipow_of h (m := 1) fun y hy => ?_
    have := h0 _ (by simpa using ipow_mul h (h1 y hy) hx)
    simpa [star_mul'] using this
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact hm _ _ ih h1
  | pred i ih => rw [sub_eq_add_neg]; exact hm _ _ ih h2

end Ipow

section Lat
open GlobalTheory.HL
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def vec {j : ℕ} (e : Fin j → V) (u : Matrix (Fin j) (Fin j) K) (a : Fin j) : V := ∑ b, u b a • e b

omit [NumberField K] [StarRing K] in
theorem near_of {j m : ℕ} (e : Fin j → V) (X : Submodule K V) (L P : Submodule (𝓞 K) V)
    (𝔞 : Fin j → Submodule (𝓞 K) K) (u : Matrix (Fin j) (Fin j) K) (hu : IsUni u) (𝔮 : Ideal (𝓞 K))
    (hq : ∀ x ∈ 𝔮, ∀ a b, ∀ t ∈ 𝔞 a, (x : K) * (t * u b a) ∈ 𝔞 b)
    (h1 : ∀ a, ∀ t ∈ 𝔞 a, t • vec e u a ∈ L)
    (h2 : ∀ y ∈ L, y ∈ X → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • vec e u a)
    (hP1 : ∀ a, ∀ t ∈ 𝔞 a, t • e a ∈ P)
    (hP2 : ∀ y ∈ P, y ∈ X → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • e a)
    (hm : j ≤ m) (hm1 : 1 ≤ m) :
    𝔮 ^ m • (P ⊓ rs (𝓞 K) X) ≤ L ∧ 𝔮 ^ m • (L ⊓ rs (𝓞 K) X) ≤ P := by
  have hs : ∀ (x : 𝓞 K) (y : V), x • y = (x : K) • y := fun x y => (algebraMap_smul K x y).symm
  have key : ∀ a : Fin j, ∀ x ∈ 𝔮 ^ (a : ℕ), ∀ t ∈ 𝔞 a, ((x : K) * t) • e a ∈ L := by
    intro a
    induction a using WellFoundedLT.induction with
    | ind a ih =>
      intro x hx t ht
      have h3 : ((x : K) * t) • vec e u a ∈ L := by
        rw [mul_smul, ← hs]; exact L.smul_mem _ (h1 a t ht)
      rw [vec, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hu.2, one_smul, smul_add] at h3
      refine (L.add_mem_iff_left ?_).1 h3
      rw [Finset.smul_sum]
      refine L.sum_mem fun b hb => ?_
      rcases lt_or_gt_of_ne (Finset.mem_erase.1 hb).1 with h4 | h4
      · have h5 : x ∈ 𝔮 ^ (b : ℕ) * 𝔮 := by
          rw [← pow_succ]; exact Ideal.pow_le_pow_right (by exact h4) hx
        rw [smul_smul]
        refine Submodule.mul_induction_on (C := fun x : 𝓞 K => ((x : K) * t * u b a) • e b ∈ L) h5
          (fun p hp q hq' => ?_) (fun p q hp hq' => ?_)
        · have := ih b h4 p hp _ (hq q hq' a b t ht)
          convert this using 2
          push_cast; ring
        · have := L.add_mem hp hq'
          rw [← add_smul] at this
          convert this using 2
          push_cast; ring
      · rw [hu.1 _ _ h4, zero_smul, smul_zero]; exact L.zero_mem
  constructor
  · refine Submodule.smul_le.2 fun x hx y hy => ?_
    obtain ⟨c, hc, rfl⟩ := hP2 y hy.1 hy.2
    rw [hs, Finset.smul_sum]
    refine L.sum_mem fun a _ => ?_
    rw [smul_smul]
    exact key a x (Ideal.pow_le_pow_right (a.2.le.trans hm) hx) _ (hc a)
  · refine Submodule.smul_le.2 fun x hx y hy => ?_
    obtain ⟨c, hc, rfl⟩ := h2 y hy.1 hy.2
    rw [hs, Finset.smul_sum]
    refine P.sum_mem fun a _ => ?_
    rw [vec, Finset.smul_sum, Finset.smul_sum]
    refine P.sum_mem fun b _ => ?_
    rw [smul_smul, smul_smul, mul_assoc]
    exact hP1 b _ (hq x (Ideal.pow_le_self (by omega) hx) a b _ (hc a))

variable {H : HermSpace K V} {r : ℕ}

def ej (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (a : Fin j) : V := F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem ej_mem (F : FlagD H r) {j l : ℕ} (hj : j ≤ r) (a : Fin j) (h : (a : ℕ) < l) : ej F hj a ∈ F.Xa l :=
  Submodule.subset_span ⟨Fin.castLE hj a, h, rfl⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_Xa (F : FlagD H r) {j l : ℕ} (hj : j ≤ r) (hl : l ≤ j) (x : V) :
    x ∈ F.Xa l ↔ ∃ c : Fin j → K, (∀ b : Fin j, l ≤ (b : ℕ) → c b = 0) ∧ x = ∑ b, c b • ej F hj b := by
  constructor
  · intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨b, hb, rfl⟩
      have hb' : (b : ℕ) < l := hb
      refine ⟨Pi.single ⟨b, by omega⟩ 1, fun a ha => ?_, ?_⟩
      · exact Pi.single_eq_of_ne (fun e => by subst e; simp at ha; omega) _
      · simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rfl
    · exact ⟨0, fun _ _ => rfl, by simp⟩
    · rintro _ _ _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      exact ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], by simp [add_smul, Finset.sum_add_distrib]⟩
    · rintro t _ _ ⟨c, hc, rfl⟩
      exact ⟨t • c, fun b hb => by simp [hc b hb], by simp [Finset.smul_sum, smul_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : l ≤ (b : ℕ)
    · rw [hc b hb, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (ej_mem F hj b (by omega))

theorem exists_frame (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (L : Submodule (𝓞 K) V) {𝔡 : Ideal (𝓞 K)}
    (h : 𝔡 ≠ ⊥) (k : Fin r → ℤ) (hL : ∀ a : Fin r, HermLat.lead F L a.castSucc = ipow 𝔡 (k a)) :
    ∃ u : Matrix (Fin j) (Fin j) K, IsUni u ∧
      (∀ a, ∀ t ∈ ipow 𝔡 (k (Fin.castLE hj a)), t • vec (ej F hj) u a ∈ L) ∧
      ∀ y ∈ L, y ∈ F.Xa j → ∃ c : Fin j → K, (∀ a, c a ∈ ipow 𝔡 (k (Fin.castLE hj a))) ∧
        y = ∑ a, c a • vec (ej F hj) u a := by
  have hs : ∀ (x : 𝓞 K) (y : V), x • y = (x : K) • y := fun x y => (algebraMap_smul K x y).symm
  have hl : ∀ (a : Fin j) (t : K), t ∈ ipow 𝔡 (k (Fin.castLE hj a)) ↔
      ∃ y ∈ L, y - t • ej F hj a ∈ F.Xa a := by
    intro a t
    rw [← hL, HermLat.lead, Submodule.mem_comap, Submodule.mem_sup]
    constructor
    · rintro ⟨y, hy, z, hz, e⟩
      refine ⟨y, hy, ?_⟩
      have e' : y + z = t • ej F hj a := e
      rw [← e']
      simpa using hz
    · rintro ⟨y, hy, hz⟩
      refine ⟨y, hy, -(y - t • ej F hj a), neg_mem hz, ?_⟩
      change _ = t • ej F hj a
      abel
  have h1 : ∀ a : Fin j, ∃ f : V, f - ej F hj a ∈ F.Xa a ∧ ∀ t ∈ ipow 𝔡 (k (Fin.castLE hj a)), t • f ∈ L := by
    intro a
    have h1 : (1 : K) ∈ ipow 𝔡 (-k (Fin.castLE hj a)) * ipow 𝔡 (k (Fin.castLE hj a)) := by
      rw [← ipow_add h, neg_add_cancel]; exact one_mem_ipow 𝔡
    have : ∀ s ∈ ipow 𝔡 (-k (Fin.castLE hj a)) * ipow 𝔡 (k (Fin.castLE hj a)), ∃ f : V,
        f - s • ej F hj a ∈ F.Xa a ∧ ∀ t ∈ ipow 𝔡 (k (Fin.castLE hj a)), t • f ∈ L := by
      intro s hs'
      refine Submodule.mul_induction_on hs' (fun p hp q hq => ?_) ?_
      · obtain ⟨y, hy, hz⟩ := (hl a q).1 hq
        refine ⟨p • y, ?_, fun t ht => ?_⟩
        · rw [mul_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hz
        · have h3 := ipow_mul h ht hp
          rw [add_neg_cancel, ipow_zero] at h3
          obtain ⟨w, hw⟩ := Submodule.mem_one.1 h3
          rw [smul_smul, ← hw, algebraMap_smul]
          exact L.smul_mem _ hy
      · rintro p q ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
        refine ⟨f + g, ?_, fun t ht => ?_⟩
        · rw [add_smul, add_sub_add_comm]; exact add_mem hf hg
        · rw [smul_add]; exact add_mem (hf' t ht) (hg' t ht)
    simpa using this 1 h1
  choose f hf hfL using h1
  choose c hc hcf using fun a : Fin j => (mem_Xa F hj a.2.le _).1 (hf a)
  have hv : ∀ a, vec (ej F hj) (1 + Matrix.of fun b a => c a b) a = f a := by
    intro a
    simp only [vec, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.of_apply, ← hcf,
      Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel
  refine ⟨1 + Matrix.of fun b a => c a b, ⟨fun a b hab => ?_, fun a => ?_⟩, ?_, ?_⟩
  · simp [Matrix.one_apply_ne hab.ne', hc b a (le_of_lt hab)]
  · simp [hc a a le_rfl]
  · simpa only [hv] using hfL
  · simp only [hv]
    have key : ∀ l, l ≤ j → ∀ y ∈ L, y ∈ F.Xa l → ∃ c : Fin j → K,
        (∀ a, c a ∈ ipow 𝔡 (k (Fin.castLE hj a))) ∧ y = ∑ a, c a • f a := by
      intro l
      induction l with
      | zero =>
        intro _ y _ hy
        obtain ⟨d, hd, rfl⟩ := (mem_Xa F hj (Nat.zero_le _) y).1 hy
        exact ⟨0, fun _ => zero_mem _, by simp [fun b => hd b (Nat.zero_le _)]⟩
      | succ l ih =>
        intro hl' y hyL hy
        obtain ⟨d, hd, e⟩ := (mem_Xa F hj hl' y).1 hy
        let a : Fin j := ⟨l, hl'⟩
        have h3 : y - d a • ej F hj a ∈ F.Xa a := by
          rw [e, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_sub_cancel_left]
          refine Submodule.sum_mem _ fun b hb => ?_
          rcases lt_or_gt_of_ne (Finset.mem_erase.1 hb).1 with h4 | h4
          · exact Submodule.smul_mem _ _ (ej_mem F hj b h4)
          · rw [hd b h4, zero_smul]; exact Submodule.zero_mem _
        have h4 := (hl a (d a)).2 ⟨y, hyL, h3⟩
        have h5 : y - d a • f a ∈ F.Xa l := by
          have := sub_mem h3 (Submodule.smul_mem _ (d a) (hf a))
          convert this using 1
          rw [smul_sub]; abel
        obtain ⟨c', hc', e'⟩ := ih (by omega) _ (sub_mem hyL (hfL a _ h4)) h5
        refine ⟨c' + Pi.single a (d a), fun b => add_mem (hc' b) ?_, ?_⟩
        · by_cases hb : b = a
          · rw [hb, Pi.single_eq_same]; exact h4
          · rw [Pi.single_eq_of_ne hb]; exact zero_mem _
        · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← e', Pi.single_apply, ite_smul,
            zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          abel
    exact key j le_rfl

end Lat

section Isom
open GlobalTheory.HL Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) {j : ℕ}

theorem B_vec (e d : Fin j → V) (u v : Matrix (Fin j) (Fin j) K) (a b : Fin j) :
    H.B (vec e u a) (vec d v b) = (uᵀ * (Matrix.of fun a b => H.B (e a) (d b)) * v.map star) a b := by
  simp only [vec, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum,
    starRingEnd_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem B_symm0 {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by rw [← H.herm, h, star_zero]

theorem exists_isom [FiniteDimensional K V] (e d : Fin j → V) (M M' : Matrix (Fin j) (Fin j) K)
    (hee : ∀ a b, H.B (e a) (e b) = 0) (hdd : ∀ a b, H.B (d a) (d b) = 0)
    (hed : ∀ a b, H.B (e a) (d b) = if a = b then 1 else 0) (hM : Mᵀ * M'.map star = 1) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧
      ∀ y, s y = y + ∑ a, H.B y (d a) • (vec e M a - e a) + ∑ a, H.B y (e a) • (vec d M' a - d a) := by
  have hde : ∀ a b, H.B (d a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [← H.herm, hed]
    rcases eq_or_ne a b with h | h
    · simp [h]
    · simp [h, h.symm]
  let π : V → V := fun y => y - ∑ a, H.B y (d a) • e a - ∑ a, H.B y (e a) • d a
  have hπe : ∀ y b, H.B (π y) (e b) = 0 := fun y b => by
    simp [π, hee, hde]
  have hπd : ∀ y b, H.B (π y) (d b) = 0 := fun y b => by
    simp [π, hdd, hed]
  have key : ∀ M M' : Matrix (Fin j) (Fin j) K, Mᵀ * M'.map star = 1 → ∀ x y,
      H.B (π x + ∑ a, H.B x (d a) • vec e M a + ∑ a, H.B x (e a) • vec d M' a)
        (π y + ∑ a, H.B y (d a) • vec e M a + ∑ a, H.B y (e a) • vec d M' a) =
      H.B (π x) (π y) + ∑ a, H.B x (d a) * star (H.B y (e a)) + ∑ a, H.B x (e a) * star (H.B y (d a)) := by
    intro M M' hM x y
    have h1 : ∀ y b, H.B (π y) (vec e M b) = 0 := fun y b => by simp [vec, hπe]
    have h2 : ∀ y b, H.B (π y) (vec d M' b) = 0 := fun y b => by simp [vec, hπd]
    have h3 : ∀ a b, H.B (vec e M a) (vec e M b) = 0 := fun y b => by simp [vec, hee]
    have h4 : ∀ a b, H.B (vec d M' a) (vec d M' b) = 0 := fun y b => by simp [vec, hdd]
    have h5 : ∀ a b, H.B (vec e M a) (vec d M' b) = if a = b then 1 else 0 := fun a b => by
      have : (Matrix.of fun a b => H.B (e a) (d b)) = 1 := by
        ext a b; simp [hed, Matrix.one_apply]
      rw [B_vec, this, Matrix.mul_one, hM, Matrix.one_apply]
    have h6 : ∀ a b, H.B (vec d M' a) (vec e M b) = if a = b then 1 else 0 := fun a b => by
      rw [← H.herm, h5]
      rcases eq_or_ne a b with h | h
      · simp [h]
      · simp [h, h.symm]
    simp [h1, h2, h3, h4, h5, h6, fun y b => B_symm0 H (h1 y b), fun y b => B_symm0 H (h2 y b), mul_comm]
    rfl
  let g : V →ₗ[K] V := LinearMap.id + ∑ a, (H.B.flip (d a)).smulRight (vec e M a - e a) +
    ∑ a, (H.B.flip (e a)).smulRight (vec d M' a - d a)
  have hg : ∀ y, g y = y + ∑ a, H.B y (d a) • (vec e M a - e a) + ∑ a, H.B y (e a) • (vec d M' a - d a) :=
    fun y => by simp [g]
  have hiso : ∀ x y, H.B (g x) (g y) = H.B x y := by
    intro x y
    have h1 := key M M' hM x y
    have h2 := key 1 1 (by simp) x y
    have h3 : ∀ y, π y + ∑ a, H.B y (d a) • vec e M a + ∑ a, H.B y (e a) • vec d M' a = g y := fun y => by
      simp only [hg, π, smul_sub, Finset.sum_sub_distrib]; abel
    have h4 : ∀ y, π y + ∑ a, H.B y (d a) • vec e (1 : Matrix (Fin j) (Fin j) K) a +
        ∑ a, H.B y (e a) • vec d (1 : Matrix (Fin j) (Fin j) K) a = y := fun y => by
      simp only [π, vec, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      abel
    rw [h3, h3] at h1
    rw [h4, h4] at h2
    rw [h1, h2]
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine H.nondeg x fun y => ?_
    rw [← hiso, hx]; simp
  exact ⟨LinearEquiv.ofInjectiveEndo g hinj, hiso, hg⟩

omit [StarRing K] in
theorem map_vec (s : V ≃ₗ[K] V) (e : Fin j → V) (S u : Matrix (Fin j) (Fin j) K)
    (hs : ∀ a, s (e a) = vec e S a) (a : Fin j) : s (vec e u a) = vec e (S * u) a := by
  simp only [vec, map_sum, map_smul, hs, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

omit [StarRing K] in
theorem uni_mul {A B : Matrix (Fin j) (Fin j) K} (hA : IsUni A) (hB : IsUni B) : IsUni (A * B) := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c < a
    · rw [hA.1 _ _ hc, zero_mul]
    · rw [hB.1 _ _ (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a, hA.2, hB.2, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 _ _ h, zero_mul]
      · rw [hB.1 _ _ h, mul_zero]
    · simp

variable {H} {r : ℕ}

theorem vec_sub_mem (F : FlagD H r) (hj : j ≤ r) {S : Matrix (Fin j) (Fin j) K} (hS : IsUni S) (a : Fin j) :
    vec (ej F hj) S a - ej F hj a ∈ F.Xa a := by
  rw [vec, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hS.2, one_smul, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun b hb => ?_
  rcases lt_or_gt_of_ne (Finset.mem_erase.1 hb).1 with h4 | h4
  · exact Submodule.smul_mem _ _ (ej_mem F hj b h4)
  · rw [hS.1 _ _ h4, zero_smul]; exact Submodule.zero_mem _

theorem vec_mem (F : FlagD H r) (hj : j ≤ r) (S : Matrix (Fin j) (Fin j) K) (a : Fin j) {l : ℕ} (hl : j ≤ l) :
    vec (ej F hj) S a ∈ F.Xa l :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (ej_mem F hj b (lt_of_lt_of_le b.2 hl))

theorem transport [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (F : FlagD H r) (hj : j ≤ r) (s : V ≃ₗ[K] V) {S u : Matrix (Fin j) (Fin j) K} (hS : IsUni S)
    (hs : ∀ a, s (ej F hj a) = vec (ej F hj) S a) (L : Submodule (𝓞 K) V) (𝔞 : Fin j → Submodule (𝓞 K) K)
    (h1 : ∀ a, ∀ t ∈ 𝔞 a, t • vec (ej F hj) u a ∈ L)
    (h2 : ∀ y ∈ L, y ∈ F.Xa j → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • vec (ej F hj) u a) :
    (∀ a, ∀ t ∈ 𝔞 a, t • vec (ej F hj) (S * u) a ∈ s • L) ∧
    ∀ y ∈ s • L, y ∈ F.Xa j → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧
      y = ∑ a, c a • vec (ej F hj) (S * u) a := by
  constructor
  · intro a t ht
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨_, h1 a t ht, by rw [← map_vec s _ S u hs, ← map_smul]; rfl⟩
  · intro y hy hyX
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    obtain ⟨S', hS', -⟩ := BlockStab.inv_facts S hS
    obtain ⟨c, -, hc⟩ := (mem_Xa F hj le_rfl _).1 hyX
    have hx' : x = ∑ a, c a • vec (ej F hj) S' a := by
      apply s.injective
      change s • x = _
      simp only [hc, map_sum, map_smul, map_vec s _ S S' hs, hS']
      simp [vec, Matrix.one_apply]
    obtain ⟨c', hc', e⟩ := h2 x hx (hx' ▸ Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (vec_mem F hj S' a le_rfl))
    refine ⟨c', hc', ?_⟩
    change s x = _
    rw [e]
    simp only [map_sum, map_smul, map_vec s _ S u hs]

end Isom

section Normal
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_ej (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (a : Fin (r + 1)) (b : Fin j) :
    H.B (F.e a) (ej F hj b) = 0 := by
  induction a using Fin.lastCases with
  | last => exact B_symm0 H (F.zperp (Fin.castLE hj b))
  | cast a => exact F.iso a (Fin.castLE hj b)

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem X_ej (F : FlagD H r) {j l : ℕ} (hj : j ≤ r) {y : V} (hy : y ∈ F.Xa l) (b : Fin j) :
    H.B y (ej F hj b) = 0 := by
  have : F.Xa l ≤ LinearMap.ker (H.B.flip (ej F hj b)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, -, rfl⟩
    exact e_ej F hj _ b
  exact this hy

variable (N : NF H r)

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_ej' (a : Fin (r + 1)) (ha : N.j ≤ (a : ℕ)) (b : Fin N.j) :
    H.B (N.F.e a) (ej N.F' N.j_le b) = 0 := by
  have h := e_ej N.F' N.j_le a b
  have hc : N.c ≠ 0 := fun e => by simpa [e] using N.c_norm
  rw [N.same a ha, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hc

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e'_ej (a : Fin (r + 1)) (ha : N.j ≤ (a : ℕ)) (b : Fin N.j) :
    H.B (N.F'.e a) (ej N.F N.j_le b) = 0 := by
  rw [N.same a ha, map_smul, LinearMap.smul_apply, e_ej, smul_zero]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem ist_ej (a : Fin r) (ha : N.j ≤ (a : ℕ)) (b : Fin N.j) :
    H.B (N.ist a) (ej N.F N.j_le b) = 0 ∧ H.B (N.ist a) (ej N.F' N.j_le b) = 0 := by
  constructor
  · refine B_symm0 H ((N.ist_e (Fin.castLE N.j_le b) a ha).trans (if_neg fun e => ?_))
    have := b.2
    rw [← e] at ha
    simp at ha
    omega
  · exact B_symm0 H (N.ist_e' (Fin.castLE N.j_le b) a b.2 ha)

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem exists_mono : ∃ (σ : Fin N.j → Fin N.j) (β : Fin N.j → ℕ) (c : Fin N.j → K),
    (∀ a, σ (σ a) = a) ∧ (∀ a b, a ≤ b → β a ≤ β b) ∧ (∀ a b, β a = β b → a < b → σ b < σ a) ∧
    (∀ a b : Fin N.j, sameBlock N.w.blocks a b = true → β a = β b) ∧ (∀ a, c a ≠ 0) ∧
    ∀ a b, H.B (ej N.F N.j_le a) (ej N.F' N.j_le b) = if b = σ a then c a else 0 := by
  obtain ⟨σ, β, t, h⟩ := BlockStab.exists_monomial N.w.blocks
  rw [N.w.size] at h
  let σ' : Fin N.j → Fin N.j := fun a => ⟨σ a, (h a a.2).1⟩
  refine ⟨σ', fun a => β a, fun a => (t (β a) : K) * ((N.sgn (σ' a) : ℤ) : K),
    fun a => Fin.ext (h a a.2).2.1, fun a b hab => ((h a a.2).2.2.2 b b.2).2.1 hab, fun a b hab hl => ?_,
    fun a b hab => ((h a a.2).2.2.2 b b.2).1.1 hab, fun a => ?_, fun a b => ?_⟩
  · have h1 := ((h a a.2).2.2.2 b b.2).2.2.1 hab
    have h2 : (a : ℕ) < b := hl
    show σ b < σ a
    omega
  · rcases Int.units_eq_one_or (N.sgn (σ' a)) with h | h <;> simp [h]
  · rw [ej, ej, N.pair, Pt.mat, ((h a a.2).2.2.2 b b.2).2.2.2]
    by_cases h2 : b = σ' a
    · subst h2; simp [σ']
    · have h3 : ¬ (b : ℕ) = σ a := fun h => h2 (Fin.ext h)
      simp [h2, h3]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem inN_of (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (s : V ≃ₗ[K] V) (hiso : ∀ x y, H.B (s x) (s y) = H.B x y)
    {S : Matrix (Fin j) (Fin j) K} (hS : IsUni S) (hs : ∀ a, s (ej F hj a) = vec (ej F hj) S a)
    (hfix : ∀ a : Fin r, j ≤ (a : ℕ) → s (F.e a.castSucc) = F.e a.castSucc)
    (hp : ∀ y, (∀ a, H.B y (ej F hj a) = 0) → s y - y ∈ F.X) : F.InN (s : V →ₗ[K] V) := by
  refine ⟨hiso, s.bijective, fun a => ?_, fun y hy => hp y fun a => B_symm0 H (hy (Fin.castLE hj a))⟩
  by_cases ha : (a : ℕ) < j
  · have := vec_sub_mem F hj hS ⟨a, ha⟩
    rwa [← hs] at this
  · rw [LinearEquiv.coe_coe, hfix a (not_lt.1 ha), sub_self]; exact Submodule.zero_mem _

set_option maxHeartbeats 800000 in
theorem exists_elt [FiniteDimensional K V] (u : Matrix (Fin N.j) (Fin N.j) K) (hu : IsUni u) :
    ∃ s ∈ N.Rs, (∀ y ∈ II N.F N.F' ⊔ Submodule.span K {N.F.z} ⊔ N.Ist, s y = y) ∧
      (∀ x y, H.B (s x) (s y) = H.B x y) ∧
      ∃ M S : Matrix (Fin N.j) (Fin N.j) K, IsUni M ∧ IsUni S ∧
        (∀ a, s (ej N.F N.j_le a) = vec (ej N.F N.j_le) M a) ∧
        (∀ a, s (ej N.F' N.j_le a) = vec (ej N.F' N.j_le) S a) ∧
        ∀ a b : Fin N.j, sameBlock N.w.blocks a b = true → a ≠ b → (M * u) a b = 0 := by
  obtain ⟨σ, β, c, hσ, hm, hr, hsb, hc, hW⟩ := exists_mono N
  set e := ej N.F N.j_le with he
  set e' := ej N.F' N.j_le with he'
  let m : Matrix (Fin N.j) (Fin N.j) K := Matrix.of fun a b => if β a = β b then u a b else 0
  have hmu : IsUni m := ⟨fun a b h => by simp [m, hu.1 a b h], fun a => by simp [m, hu.2]⟩
  obtain ⟨M, hM1, hM2, hM3, -, hM4⟩ := BlockStab.inv_facts m hmu
  have hM5 := hM4 β fun a b h => by simp [m, h.ne]
  let d : Fin N.j → V := fun a => (star (c a))⁻¹ • e' (σ a)
  have hσi : ∀ a b, σ a = σ b ↔ a = b := fun a b => ⟨fun h => by rw [← hσ a, h, hσ], fun h => by rw [h]⟩
  have hee : ∀ a b, H.B (e a) (e b) = 0 := fun a b => e_ej _ _ _ _
  have hee' : ∀ a b, H.B (e' a) (e' b) = 0 := fun a b => e_ej _ _ _ _
  have hed : ∀ a b, H.B (e a) (d b) = if a = b then 1 else 0 := fun a b => by
    rcases eq_or_ne a b with h | h
    · simp [d, hW, h, hc, starRingEnd_apply]
    · simp [d, hW, h, hσi, h.symm]
  obtain ⟨s, hiso, hs⟩ := exists_isom H e d M (mᵀ.map star) hee (fun a b => by simp [d, hee']) hed (by
    have : (mᵀ.map star).map star = mᵀ := by ext a b; simp
    rw [this, ← Matrix.transpose_mul, hM1, Matrix.transpose_one])
  have hfix : ∀ y, (∀ b, H.B y (e b) = 0) → (∀ b, H.B y (e' b) = 0) → s y = y := fun y h1 h2 => by
    simp [hs, d, h1, h2]
  let S : Matrix (Fin N.j) (Fin N.j) K := Matrix.of fun p q =>
    star (c (σ q)) * star (m (σ q) (σ p)) * (star (c (σ p)))⁻¹
  have hS : IsUni S := by
    refine ⟨fun p q h => ?_, fun p => by simp [S, hmu.2, hc]⟩
    have : m (σ q) (σ p) = 0 := by
      by_cases h1 : β (σ q) = β (σ p)
      · refine hmu.1 _ _ (lt_of_le_of_ne (not_lt.1 fun h2 => ?_) fun h2 => h.ne' ((hσi _ _).1 h2))
        have := hr _ _ h1 h2
        rw [hσ, hσ] at this
        exact absurd this (not_lt.2 h.le)
      · simp [m, h1]
    simp [S, this]
  have hse : ∀ a, s (e a) = vec e M a := fun a => by simp [hs, hee, hed]
  have hse' : ∀ a, s (e' a) = vec e' S a := fun a => by
    have h1 : ∀ b, H.B (e' a) (e b) = if b = σ a then star (c b) else 0 := fun b => by
      rw [← H.herm, hW]
      rcases eq_or_ne b (σ a) with h | h
      · simp [h, hσ]
      · have : a ≠ σ b := fun h' => h (by rw [h', hσ])
        simp [h, this]
    have h2 : ∀ b, H.B (e' a) (d b) = 0 := fun b => by simp [d, hee']
    have h3 : star (c (σ a)) • d (σ a) = e' a := by
      simp [d, hσ, smul_smul, hc]
    simp only [hs, h1, h2, zero_smul, Finset.sum_const_zero, add_zero, ite_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [smul_sub, h3, add_sub_cancel]
    simp only [vec, Finset.smul_sum, d, smul_smul]
    refine Fintype.sum_equiv (Function.Involutive.toPerm σ hσ) _ _ fun b => ?_
    change _ = S (σ b) a • e' (σ b)
    simp only [S, Matrix.of_apply, hσ, Matrix.map_apply, Matrix.transpose_apply, mul_assoc]
  have hX : ∀ a, e a ∈ N.F.X := fun a => ej_mem _ _ _ (lt_of_lt_of_le a.2 N.j_le)
  have hX' : ∀ a, e' a ∈ N.F'.X := fun a => ej_mem _ _ _ (lt_of_lt_of_le a.2 N.j_le)
  refine ⟨s, ⟨Subgroup.subset_closure ⟨?_, ?_⟩, ?_⟩, ?_, hiso, M, S, hM3, hS, hse, hse', ?_⟩
  · refine inN_of N.F N.j_le s hiso hM3 hse
      (fun a ha => hfix _ (e_ej _ _ _) (e_ej' N _ ha)) fun y hy => ?_
    simp only [hs, ← he] at hy ⊢
    simp only [hy, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
      (sub_mem (vec_mem N.F N.j_le M a N.j_le) (hX a))
  · refine inN_of N.F' N.j_le s hiso hS hse'
      (fun a ha => hfix _ (e'_ej N _ ha) (e_ej _ _ _)) fun y hy => ?_
    have hd : ∀ a, H.B y (d a) = 0 := fun a => by
      have : H.B y (e' (σ a)) = 0 := hy _
      simp [d, this]
    have hdX : ∀ a, d a ∈ N.F'.X := fun a => Submodule.smul_mem _ _ (hX' _)
    simp only [hs, hd, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
      (sub_mem (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hdX b)) (hdX a))
  · refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    have hy' := (mem_perp_iff H _ y).1 hy
    exact hfix y (fun b => hy' _ (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_left (hX b))))) (fun b => hy' _ (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (hX' b)))))
  · have : II N.F N.F' ⊔ Submodule.span K {N.F.z} ⊔ N.Ist ≤
        LinearMap.eqLocus (s : V →ₗ[K] V) LinearMap.id := by
      refine sup_le (sup_le (fun y hy => hfix y (X_ej _ _ hy.1) (X_ej _ _ hy.2)) ?_) ?_
      · refine Submodule.span_le.2 ?_
        rintro _ rfl
        exact hfix _ (e_ej _ _ _) (e_ej' N _ N.j_le)
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        exact hfix _ (fun b => (ist_ej N a ha b).1) (fun b => (ist_ej N a ha b).2)
    exact fun y hy => this hy
  · intro a b hab hne
    have h1 := congrFun (congrFun hM2 a) b
    rw [Matrix.one_apply_ne hne] at h1
    rw [← h1, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : β x = β b
    · simp [m, hx]
    · have : M a x = 0 := by
        rcases lt_or_gt_of_ne hx with h | h
        · exact hM3.1 _ _ (not_le.1 fun h' => absurd (hm _ _ h') (by rw [hsb a b hab]; omega))
        · exact hM5 _ _ (by rw [hsb a b hab]; exact h)
      simp [this]

end Normal

section Final
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem ref_coef (d : V) (A : Submodule (𝓞 K) K)
    (h1 : ∀ b : Fin N.j, ∀ t ∈ N.aa (Fin.castLE N.j_le b), t * H.B (ej N.F N.j_le b) d ∈ A)
    (h2 : ∀ b : Fin N.j, ∀ t ∈ N.aa (Fin.castLE N.j_le b), t * H.B (ej N.F' N.j_le b) d ∈ A)
    (h3 : ∀ b : Fin (r + 1), N.j ≤ (b : ℕ) → H.B (N.F.e b) d = 0)
    (h4 : ∀ b : Fin r, N.j ≤ (b : ℕ) → H.B (N.ist b) d = 0) : ∀ y ∈ N.P0, H.B y d ∈ A := by
  have hl : ∀ (B : Submodule (𝓞 K) K) (v : V), (∀ t ∈ B, t * H.B v d ∈ A) →
      line B v ≤ A.comap ((H.B.flip d).restrictScalars (𝓞 K)) := by
    rintro B v h _ ⟨t, ht, rfl⟩
    simpa using h t ht
  have : N.P0 ≤ A.comap ((H.B.flip d).restrictScalars (𝓞 K)) := by
    refine sup_le (sup_le (sup_le (iSup_le fun a => hl _ _ fun t ht => ?_)
      (iSup₂_le fun a ha => hl _ _ (h2 ⟨a, ha⟩))) (hl _ _ fun t _ => ?_))
      (iSup₂_le fun a ha => hl _ _ fun t _ => ?_)
    · by_cases ha : (a : ℕ) < N.j
      · exact h1 ⟨a, ha⟩ t ht
      · rw [h3 _ (not_lt.1 ha), mul_zero]; exact A.zero_mem
    · rw [FlagD.z, h3 _ N.j_le, mul_zero]; exact A.zero_mem
    · rw [h4 _ ha, mul_zero]; exact A.zero_mem
  exact fun y hy => this hy

theorem ref_facts :
    (∀ a, ∀ t ∈ N.aa (Fin.castLE N.j_le a), t • ej N.F N.j_le a ∈ N.P0) ∧
    (∀ a, ∀ t ∈ N.aa (Fin.castLE N.j_le a), t • ej N.F' N.j_le a ∈ N.P0) ∧
    (∀ y ∈ N.P0, y ∈ N.F.Xa N.j → ∃ c : Fin N.j → K, (∀ a, c a ∈ N.aa (Fin.castLE N.j_le a)) ∧
      y = ∑ a, c a • ej N.F N.j_le a) ∧
    (∀ y ∈ N.P0, y ∈ N.F'.Xa N.j → ∃ c : Fin N.j → K, (∀ a, c a ∈ N.aa (Fin.castLE N.j_le a)) ∧
      y = ∑ a, c a • ej N.F' N.j_le a) := by
  obtain ⟨σ, β, c, hσ, -, -, -, hc, hW⟩ := exists_mono N
  have hσi : ∀ a b, σ a = σ b ↔ a = b := fun a b => ⟨fun h => by rw [← hσ a, h, hσ], fun h => by rw [h]⟩
  refine ⟨fun a t ht => ?_, fun a t ht => ?_, fun y hy hyX => ?_, fun y hy hyX => ?_⟩
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_iSup_of_mem (Fin.castLE N.j_le a) ⟨t, ht, rfl⟩)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem (Fin.castLE N.j_le a) (Submodule.mem_iSup_of_mem a.2 ⟨t, ht, rfl⟩))))
  · obtain ⟨x, -, hx⟩ := (mem_Xa N.F N.j_le le_rfl y).1 hyX
    refine ⟨x, fun a => ?_, hx⟩
    have hd : ∀ b, H.B (ej N.F N.j_le b) ((star (c a))⁻¹ • ej N.F' N.j_le (σ a)) = if b = a then 1 else 0 := by
      intro b
      rcases eq_or_ne b a with h | h
      · simp [hW, h, hc, starRingEnd_apply]
      · simp [hW, h, hσi, h.symm]
    have := ref_coef N ((star (c a))⁻¹ • ej N.F' N.j_le (σ a)) (N.aa (Fin.castLE N.j_le a))
      (fun b t ht => by
        rw [hd]; split_ifs with h
        · rw [mul_one, ← h]; exact ht
        · simp)
      (fun b t _ => by
        have : H.B (ej N.F' N.j_le b) (ej N.F' N.j_le (σ a)) = 0 := e_ej _ _ _ _
        simp [this])
      (fun b hb => by simp [e_ej' N b hb]) (fun b hb => by simp [(ist_ej N b hb _).2]) y hy
    rw [hx] at this
    simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hd, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using this
  · obtain ⟨x, -, hx⟩ := (mem_Xa N.F' N.j_le le_rfl y).1 hyX
    refine ⟨x, fun a => ?_, hx⟩
    have hd : ∀ b, H.B (ej N.F' N.j_le b) ((c (σ a))⁻¹ • ej N.F N.j_le (σ a)) = if b = a then 1 else 0 := by
      intro b
      rw [← H.herm, map_smul, LinearMap.smul_apply, hW, hσ]
      split_ifs <;> simp [hc]
    have := ref_coef N ((c (σ a))⁻¹ • ej N.F N.j_le (σ a)) (N.aa (Fin.castLE N.j_le a))
      (fun b t _ => by
        have : H.B (ej N.F N.j_le b) (ej N.F N.j_le (σ a)) = 0 := e_ej _ _ _ _
        simp [this])
      (fun b t ht => by
        rw [hd]; split_ifs with h
        · rw [mul_one, ← h]; exact ht
        · simp)
      (fun b _ => by simp [e_ej]) (fun b hb => by simp [(ist_ej N b hb _).1]) y hy
    rw [hx] at this
    simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hd, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using this

theorem denom (𝔠 : Ideal (𝓞 K))
    (hD : ∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠,
      ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K))
    (A B : Matrix (Fin N.j) (Fin N.j) K) (hA : IsUni A) (hB : IsUni B)
    (hA0 : ∀ a b : Fin N.j, sameBlock N.w.blocks a b = true → a ≠ b → A a b = 0)
    (hZ : ∀ a b : Fin N.j, H.B (vec (ej N.F N.j_le) A a) (vec (ej N.F' N.j_le) B b) ∈
      ipow N.𝔡 (((r : ℤ) - (a : ℕ)) + ((r : ℤ) - (b : ℕ)))) (a b : Fin N.j) :
    (∀ x ∈ 𝔠, (x : K) * A b a ∈ ipow N.𝔡 (((r : ℤ) - (a : ℕ)) - ((r : ℤ) - (b : ℕ)))) ∧
    ∀ x ∈ 𝔠, ∀ x' ∈ 𝔠, (x : K) * x' * star (B b a) ∈ ipow N.𝔡 (((r : ℤ) - (a : ℕ)) - ((r : ℤ) - (b : ℕ))) := by
  obtain ⟨l', l, t, e1, e2, e3, e4, e5, e6, e7⟩ :=
    GlobalTheory.OrbitDenom.block_of N.w.blocks b (by rw [N.w.size]; exact b.2)
  rw [N.w.size] at e3
  have e3' : l' ≤ N.j := by omega
  set W : Matrix (Fin N.j) (Fin N.j) K := Matrix.of fun a b => H.B (ej N.F N.j_le a) (ej N.F' N.j_le b) with hW
  have hWe : ∀ a b : Fin N.j, W a b = ptEntryL N.w.blocks a b * ((N.sgn b : ℤ) : K) := fun a b => N.pair a b
  have hc : ∀ a b : Fin N.j, l ≤ (a : ℕ) → (b : ℕ) < l → W a b = 0 := fun a b ha hb => by
    rw [hWe, e6 _ _ ha hb, zero_mul]
  have hc' : ∀ a b : Fin N.j, l' ≤ (a : ℕ) → (b : ℕ) < l' → W a b = 0 := fun a b ha hb => by
    rw [hWe, e7 _ _ ha hb, zero_mul]
  have hdet : W.det ≠ 0 := by
    obtain ⟨σ, β, c, hσ, -, -, -, hc, hW'⟩ := exists_mono N
    have : W * Matrix.of (fun p q => if q = σ p then (c q)⁻¹ else 0) = 1 := by
      ext p q
      simp only [hW, Matrix.mul_apply, Matrix.of_apply, hW', ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hσ]
      rcases eq_or_ne p q with h | h
      · subst h; simp [hc]
      · simp [h, h.symm]
    exact (Matrix.isUnit_det_of_right_inverse this).ne_zero
  obtain ⟨g1, g2⟩ := wden (fun n => (ipow N.𝔡 n).toAddSubgroup) (one_mem_ipow N.𝔡)
    (fun _ _ _ _ hx hy => ipow_mul N.𝔡_ne hx hy) e3 e3' r (fun a => (r : ℤ) - (a : ℕ)) (fun _ => rfl)
    Aᵀ W (B.map star) (fun p q h => hA.1 _ _ h) hA.2 (fun p q h => by simp [hB.1 _ _ h])
    (fun p => by simp [hB.2]) (fun p q => by rw [← B_vec]; exact hZ p q) hdet hc hc'
    (fun p q hp hq hne => by
      rcases lt_or_gt_of_ne hne with h | h
      · exact hA.1 _ _ h
      · have h' : (q : ℕ) < p := h
        exact hA0 _ _ (e4 _ _ hq (by omega) (by omega) hp) hne.symm)
    t (fun b => ((N.sgn b : ℤ) : K))
    (fun b => by
      rcases Int.units_eq_one_or (N.sgn b) with h | h
      · simpa [h] using one_mem_ipow N.𝔡
      · simpa [h] using one_mem_ipow N.𝔡)
    (fun b => by rcases Int.units_eq_one_or (N.sgn b) with h | h <;> simp [h])
    (fun a b hb' hb => by rw [hWe, GlobalTheory.OrbitDenom.entry_symm, e5 _ _ hb' hb, add_comm (b : ℕ) a])
    (fun a b ha' ha => by rw [hWe, e5 _ _ ha' ha]) b e1 e2 a
  have key : ∀ (m : ℕ) (hm : m ≤ N.j), (∀ a b : Fin N.j, m ≤ (a : ℕ) → (b : ℕ) < m → W a b = 0) →
      (W.submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 ∧
      ∀ x ∈ 𝔠, (x : K) / (W.submatrix (Fin.castLE hm) (Fin.castLE hm)).det ∈
        ipow N.𝔡 (-(2 * ∑ a : Fin m, ((r : ℤ) - ((Fin.castLE hm a : Fin N.j) : ℕ)))) := by
    intro m hm h0
    have h1 := (GlobalTheory.OrbitDenom.unit_cut hm W (IsUnit.mk0 _ hdet) h0).ne_zero
    refine ⟨h1, fun x hx => mem_ipow_of N.𝔡_ne (m := 2 * ∑ a ∈ Finset.range m, ((r : ℤ) - a)) fun y hy => ?_⟩
    have h2 := hD m (hm.trans (N.j_le.trans (Nat.le_succ r))) hm h1 x hx y hy
    have h3 : ∑ a : Fin m, ((r : ℤ) - ((Fin.castLE hm a : Fin N.j) : ℕ)) =
        ∑ a ∈ Finset.range m, ((r : ℤ) - a) := Fin.sum_univ_eq_sum_range (fun a : ℕ => (r : ℤ) - a) m
    rw [h3, add_neg_cancel, ipow_zero, ← mul_div_assoc, mul_comm y]
    exact h2
  obtain ⟨k1, k2⟩ := key l e3 hc
  obtain ⟨k3, k4⟩ := key l' e3' hc'
  refine ⟨fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · have := ipow_mul N.𝔡_ne (k2 x hx) g1
    convert this using 1
    · congr 1; ring
    · rw [Matrix.transpose_apply]; field_simp
  · have := ipow_mul N.𝔡_ne (k4 x' hx') (ipow_mul N.𝔡_ne (k2 x hx) g2)
    convert this using 1
    · congr 1; ring
    · rw [Matrix.map_apply]; field_simp

end Final

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ II N.F N.F' ⊔ Submodule.span K {N.F.z} ⊔ N.Ist, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 := by
  intro K V _ _ _ _ _ _ _ _ H _ r N g Λ _ hΛ 𝔠 _ h𝔠 _ hD
  obtain ⟨⟨hU, hF, hF'⟩, -⟩ := hΛ
  obtain ⟨u, hu, u1, u2⟩ := exists_frame N.F N.j_le Λ N.𝔡_ne _ hF.1
  obtain ⟨u', hu', u1', u2'⟩ := exists_frame N.F' N.j_le Λ N.𝔡_ne _ hF'.1
  obtain ⟨s, hs, hfix, hiso, M, S, hM, hS, hse, hse', h0⟩ := exists_elt N u hu
  obtain ⟨p1, p2, p3, p4⟩ := ref_facts N
  obtain ⟨t1, t2⟩ := transport N.F N.j_le s hM hse Λ _ u1 u2
  obtain ⟨t1', t2'⟩ := transport N.F' N.j_le s hS hse' Λ _ u1' u2'
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H Λ x).1 (by rw [hU.2]; exact hx)).2
  have hd := denom N 𝔠 (fun l hl h1 h2 x hx y hy => (hD l hl h1 h2 x hx y hy).1) (M * u) (S * u')
    (uni_mul hM hu) (uni_mul hS hu') h0 (fun a b => by
      rw [← map_vec s _ M u hse, ← map_vec s _ S u' hse', hiso]
      refine mem_ipow_of N.𝔡_ne (m := -((r : ℤ) - (a : ℕ))) fun x hx => ?_
      refine mem_ipow_of N.𝔡_ne (m := -((r : ℤ) - (b : ℕ))) fun y hy => ?_
      have h1 := hint _ (u1 a x hx) _ (u1' b _ (star_mem_ipow N.𝔡_ne N.𝔡_star _ y hy))
      rw [neg_add_cancel_left, neg_add_cancel, ipow_zero]
      simpa [starRingEnd_apply] using h1)
  have hq : ∀ A : Matrix (Fin N.j) (Fin N.j) K, (∀ x ∈ 𝔠, ∀ x' ∈ 𝔠, ∀ a b : Fin N.j,
      (x : K) * x' * A b a ∈ ipow N.𝔡 (((r : ℤ) - (a : ℕ)) - ((r : ℤ) - (b : ℕ)))) →
      ∀ x ∈ 𝔠 ^ 2, ∀ a b : Fin N.j, ∀ t ∈ N.aa (Fin.castLE N.j_le a),
        (x : K) * (t * A b a) ∈ N.aa (Fin.castLE N.j_le b) := by
    intro A hA x hx a b t ht
    rw [pow_two] at hx
    refine Submodule.mul_induction_on
      (C := fun x : 𝓞 K => (x : K) * (t * A b a) ∈ N.aa (Fin.castLE N.j_le b)) hx
      (fun p hp q hq => ?_) (fun p q hp hq => ?_)
    · have := ipow_mul N.𝔡_ne ht (hA p hp q hq a b)
      convert this using 1
      · rw [NF.aa]; congr 1; simp
      · push_cast; ring
    · push_cast; rw [add_mul]; exact add_mem hp hq
  have hj := N.j_le
  have n1 := near_of (m := r + 1) _ _ _ _ _ _ (uni_mul hM hu) (𝔠 ^ 2) (hq _ fun x _ x' hx' a b => by
    rw [mul_assoc]; exact Submodule.smul_mem _ x ((hd a b).1 x' hx')) t1 t2 p1 p3 (by omega) (by omega)
  have n2 := near_of (m := r + 1) _ _ _ _ _ _ (uni_mul hS hu') (𝔠 ^ 2) (hq _ fun x hx x' hx' a b => by
    obtain ⟨y, hy, e⟩ := h𝔠 x hx
    obtain ⟨y', hy', e'⟩ := h𝔠 x' hx'
    have := star_mem_ipow N.𝔡_ne N.𝔡_star _ _ ((hd a b).2 y hy y' hy')
    simpa [e, e', star_mul'] using this) t1' t2' p2 p4 (by omega) (by omega)
  rw [← pow_mul, show 2 * (r + 1) = 2 * r + 2 by ring] at n1 n2
  refine ⟨s, hs, hfix, ?_⟩
  rintro _ rfl
  exact ⟨n1.1, n2.1, n1.2, n2.2⟩

end GlobalTheory.DegCnt.PosJ
