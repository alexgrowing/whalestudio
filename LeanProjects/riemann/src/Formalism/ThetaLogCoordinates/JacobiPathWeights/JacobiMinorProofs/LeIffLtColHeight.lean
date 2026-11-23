import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace Paths

end Paths

open Paths

namespace Paths

theorem le_iff_lt_colHeight {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) (c : ℤ) (m : Fin n) :
    c ≤ μ m ↔ m.val < colHeight μ c := by
  unfold colHeight
  constructor
  · intro hm
    have hsub : Finset.Iic m ⊆ univ.filter fun m => c ≤ μ m := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and]
      exact hm.trans (h (Finset.mem_Iic.1 hx))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hm
    by_contra hc
    have hsub : (univ.filter fun m => c ≤ μ m) ⊆ Finset.Iio m := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [Finset.mem_Iio]
      by_contra hx'
      exact hc (hx.trans (h (not_lt.1 hx')))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem colHeight_le {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : colHeight μ c ≤ n :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

theorem colHeight_zero (n : ℕ) (c : ℤ) : colHeight (0 : Fin n → ℤ) c = if 1 ≤ c then 0 else n := by
  unfold colHeight
  by_cases hc : 1 ≤ c
  · rw [if_pos hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    simp only [Pi.zero_apply]
    omega
  · rw [if_neg hc, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro m _
    simp only [Pi.zero_apply]
    omega

theorem strip_height {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) (c : ℤ) :
    colHeight ν c = colHeight μ c ∨ colHeight ν c = colHeight μ c + 1 := by
  obtain ⟨h1, h2, -⟩ := hs
  have l1 : colHeight μ c ≤ colHeight ν c := by
    by_contra hlt
    have hn := colHeight_le μ c
    have hm : (⟨colHeight ν c, by omega⟩ : Fin n).val < colHeight μ c := by
      show colHeight ν c < colHeight μ c
      omega
    have := (le_iff_lt_colHeight hν c _).1 (((le_iff_lt_colHeight hμ c _).2 hm).trans (h1 _))
    exact absurd this (lt_irrefl _)
  have l2 : colHeight ν c ≤ colHeight μ c + 1 := by
    by_contra hlt
    have hn := colHeight_le ν c
    have hm : (⟨colHeight μ c + 1, by omega⟩ : Fin n).val < colHeight ν c := by
      show colHeight μ c + 1 < colHeight ν c
      omega
    have := (le_iff_lt_colHeight hμ c _).1 (((le_iff_lt_colHeight hν c _).2 hm).trans
      (h2 ⟨colHeight μ c, by omega⟩ _ rfl))
    exact absurd this (lt_irrefl _)
  omega

theorem changed_eq {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) :
    {c : ℤ | colHeight ν c ≠ colHeight μ c} =
      ↑(univ.biUnion fun m : Fin n => Finset.Ioc (μ m) (ν m)) := by
  ext c
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_Ioc]
  constructor
  · intro hne
    have hh := strip_height hν hμ hs c
    have hn := colHeight_le ν c
    refine ⟨⟨colHeight μ c, by omega⟩, ?_, ?_⟩
    · refine not_le.1 fun hle => ?_
      exact absurd ((le_iff_lt_colHeight hμ c _).1 hle) (lt_irrefl _)
    · refine (le_iff_lt_colHeight hν c _).2 ?_
      show colHeight μ c < colHeight ν c
      omega
  · rintro ⟨m, m1, m2⟩
    have a1 := (le_iff_lt_colHeight hν c m).1 m2
    have a2 : ¬ m.val < colHeight μ c := fun hlt =>
      absurd ((le_iff_lt_colHeight hμ c m).2 hlt) (not_le.2 m1)
    omega

theorem changed_ncard {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) : {c : ℤ | colHeight ν c ≠ colHeight μ c}.ncard = b := by
  rw [changed_eq hν hμ hs, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp only [Int.card_Ioc]
    obtain ⟨h1, -, h3⟩ := hs
    have : ((∑ m : Fin n, (ν m - μ m).toNat : ℕ) : ℤ) = (b : ℤ) := by
      push_cast
      rw [← h3, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => Int.toNat_of_nonneg (sub_nonneg.2 (h1 m))
    exact_mod_cast this
  · intro x _ y _ hxy
    show Disjoint (Finset.Ioc (μ x) (ν x)) (Finset.Ioc (μ y) (ν y))
    rw [Finset.disjoint_left]
    intro c hx hy
    rw [Finset.mem_Ioc] at hx hy
    apply hxy
    have hh := strip_height hν hμ hs c
    have a1 := (le_iff_lt_colHeight hν c x).1 hx.2
    have a2 : ¬ x.val < colHeight μ c := fun hlt =>
      absurd ((le_iff_lt_colHeight hμ c x).2 hlt) (not_le.2 hx.1)
    have b1 := (le_iff_lt_colHeight hν c y).1 hy.2
    have b2 : ¬ y.val < colHeight μ c := fun hlt =>
      absurd ((le_iff_lt_colHeight hμ c y).2 hlt) (not_le.2 hy.1)
    exact Fin.ext (by omega)

theorem changed_finite {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) : {c : ℤ | colHeight ν c ≠ colHeight μ c}.Finite := by
  rw [changed_eq hν hμ hs]
  exact Finset.finite_toSet _

theorem path_height {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) {i : ℕ} (hi : i < N) (c : ℤ) :
    if isVec i then
      colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c = colHeight (μ i) c + 1
    else
      colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c + 1 = colHeight (μ i) c := by
  obtain ⟨-, ha, hs⟩ := hp
  have h := hs i hi
  by_cases hv : isVec i = true
  · rw [if_pos hv] at h ⊢
    exact strip_height (ha _ hi) (ha _ hi.le) h c
  · rw [if_neg hv] at h ⊢
    rcases strip_height (ha _ hi.le) (ha _ hi) h c with e | e
    · exact Or.inl e.symm
    · exact Or.inr e.symm

theorem path_ncard {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) {i : ℕ} (hi : i < N) :
    {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}.ncard = B i := by
  obtain ⟨-, ha, hs⟩ := hp
  have h := hs i hi
  by_cases hv : isVec i = true
  · rw [if_pos hv] at h
    exact changed_ncard (ha _ hi) (ha _ hi.le) h
  · rw [if_neg hv] at h
    have := changed_ncard (ha _ hi.le) (ha _ hi) h
    simp only [ne_comm] at this ⊢
    exact this

theorem path_finite {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) {i : ℕ} (hi : i < N) :
    {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}.Finite := by
  obtain ⟨-, ha, hs⟩ := hp
  have h := hs i hi
  by_cases hv : isVec i = true
  · rw [if_pos hv] at h
    exact changed_finite (ha _ hi) (ha _ hi.le) h
  · rw [if_neg hv] at h
    have := changed_finite (ha _ hi.le) (ha _ hi) h
    simp only [ne_comm] at this ⊢
    exact this

end Paths

namespace Paths

def chg {n : ℕ} (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ) (i : ℕ) : Prop :=
  colHeight (μ (i + 1)) c ≠ colHeight (μ i) c ∨ N ≤ i

instance {n : ℕ} (μ : ℕ → Fin n → ℤ) (c : ℤ) (N : ℕ) : DecidablePred (chg μ c N) := fun i => by
  unfold chg; infer_instance

end Paths

namespace Paths

theorem pathWord_unchanged {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ)
    (c : ℤ) (Xr : ℕ → Fin n → R) : ∀ j : ℕ,
    (∀ i < j, colHeight (μ (i + 1)) c = colHeight (μ i) c) →
      pathWord isVec μ c Xr j = oneF ∧ colHeight (μ j) c = colHeight (μ 0) c := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro h
    obtain ⟨a, b⟩ := ih fun i hi => h i (by omega)
    refine ⟨?_, (h j (by omega)).trans b⟩
    rw [pathWord, if_pos (h j (by omega))]
    exact a

theorem hom_intCast {σ R : Type*} [CommRing R] (w : σ → ℕ) (z : ℤ) :
    IsWeightedHomogeneous w ((z : ℤ) : MvPolynomial σ R) 0 := by
  rw [← map_intCast (C : R →+* MvPolynomial σ R)]
  exact isWeightedHomogeneous_C w _

theorem hom_step {σ R : Type*} [CommRing R] {n : ℕ} (w : σ → ℕ) (up : Bool)
    (Kf : Form (MvPolynomial σ R) n) (Xv : Fin n → MvPolynomial σ R) (d e : ℕ)
    (hK : ∀ J, IsWeightedHomogeneous w (Kf J) d) (hX : ∀ m, IsWeightedHomogeneous w (Xv m) e)
    (J : Finset (Fin n)) : IsWeightedHomogeneous w (stepF up Kf Xv J) (d + e) := by
  unfold stepF
  split
  · unfold wedgeF
    refine IsWeightedHomogeneous.sum _ _ _ fun m _ => ?_
    have := ((hom_intCast (R := R) w (sg J m)).mul (hK (J.erase m))).mul (hX m)
    rwa [zero_add] at this
  · unfold contrF
    refine IsWeightedHomogeneous.sum _ _ _ fun m _ => ?_
    have := ((hom_intCast (R := R) w (sg J m)).mul (hX m)).mul (hK (insert m J))
    rwa [zero_add, add_comm] at this

theorem pathWord_hom (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ)
    (c : ℤ) (i : ℕ) : ∀ (j : ℕ) (J : Finset (Fin n)),
    IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j J)
      (if i < j ∧ colHeight (μ (i + 1)) c ≠ colHeight (μ i) c then 1 else 0) := by
  intro j
  induction j with
  | zero =>
    intro J
    rw [if_neg (by omega)]
    show IsWeightedHomogeneous _ (if J = ∅ then 1 else 0) 0
    split
    · exact isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  | succ j ih =>
    intro J
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, if_pos hch]
      have := ih J
      convert this using 2
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 h1) with h | h
        · exact h
        · subst h; exact absurd hch h2
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    · rw [pathWord, if_neg hch]
      have := hom_step (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) (isVec j == decide (1 ≤ c))
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j)
        (fun a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) _ (if j = i then 1 else 0) ih
        (fun m => isWeightedHomogeneous_X R _ (j, m)) J
      convert this using 1
      by_cases hji : j = i
      · subst hji
        simp [hch]
      · have : (i < j + 1) ↔ i < j := by omega
        simp [hji, this]

end Paths

theorem pathProductDegrees : PsiDegrees := by
  intro R _ n N isVec B μ I hp hI
  have hfin : (⋃ i ∈ Set.Iio N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}).Finite :=
    Set.Finite.biUnion (Set.finite_Iio N) fun i hi => path_finite hp hi
  have hsub : (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)) ⊆
      ⋃ i ∈ Set.Iio N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c} := by
    intro c hc
    by_contra hn
    apply hc
    have hun : ∀ i < N, colHeight (μ (i + 1)) c = colHeight (μ i) c := by
      intro i hi
      by_contra hne
      exact hn (Set.mem_biUnion (show i ∈ Set.Iio N from hi) hne)
    obtain ⟨a, b⟩ := pathWord_unchanged isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N hun
    have hcard := hI c
    rw [b, hp.1, colHeight_zero] at hcard
    have h0 : (I c).card = 0 := by
      rw [hcard]; split_ifs <;> simp
    show pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c) = 1
    rw [a, Finset.card_eq_zero.1 h0]
    simp [oneF]
  refine ⟨hfin.subset hsub, fun i => ?_⟩
  unfold psiPath
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rwa [Set.Finite.coe_toFinset])]
  have key := IsWeightedHomogeneous.prod hfin.toFinset
    (fun c : ℤ => pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c))
    (fun c : ℤ => if i < N ∧ colHeight (μ (i + 1)) c ≠ colHeight (μ i) c then 1 else 0)
    (w := fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
    (fun c _ => pathWord_hom R isVec μ c i N (I c))
  convert key using 1
  by_cases hi : i < N
  · rw [if_pos hi, ← path_ncard hp hi, ← Finset.card_filter, ← Set.ncard_coe_finset]
    congr 1
    ext c
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨Set.mem_biUnion (show i ∈ Set.Iio N from hi) h, hi, h⟩
    · rintro ⟨-, -, h⟩
      exact h
  · rw [if_neg hi]
    exact (Finset.sum_eq_zero fun c _ => if_neg fun h => hi h.1).symm

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
