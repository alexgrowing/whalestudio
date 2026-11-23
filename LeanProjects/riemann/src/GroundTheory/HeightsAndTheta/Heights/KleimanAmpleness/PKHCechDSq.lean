import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace KHCechDSq

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def rem (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) : ∀ k, Finset (ι k) :=
  fun l => (I l).filter fun j => (⟨l, j⟩ : Σ k, ι k) ≠ p

def sg (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) : ℤ := KH.faceSign I p.1 p.2

theorem rem_same (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) : rem I ⟨k, i⟩ k = (I k).erase i := by
  ext j
  simp [rem, and_comm]

theorem rem_ne (I : ∀ k, Finset (ι k)) {k l : K} (i : ι k) (h : l ≠ k) : rem I ⟨k, i⟩ l = I l :=
  Finset.filter_true_of_mem fun _ _ e => h (congrArg Sigma.fst e)

theorem rem_subset (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) (l : K) : rem I p l ⊆ I l :=
  Finset.filter_subset _ _

theorem rem_comm (I : ∀ k, Finset (ι k)) (p q : Σ k, ι k) : rem (rem I p) q = rem (rem I q) p := by
  funext l
  ext j
  simp only [rem, Finset.mem_filter]
  tauto

theorem rem_self (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) : rem (rem I p) p = rem I p := by
  funext l
  ext j
  simp only [rem, Finset.mem_filter]
  tauto

theorem update_erase_eq_rem (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) :
    Function.update I k ((I k).erase i) = rem I ⟨k, i⟩ := by
  funext l
  rcases eq_or_ne l k with rfl | hl
  · rw [Function.update_self, rem_same]
  · rw [Function.update_of_ne hl, rem_ne I i hl]

theorem sigma_rem (I : ∀ k, Finset (ι k)) (p : Σ k, ι k) :
    Finset.univ.sigma (rem I p) = (Finset.univ.sigma I).erase p := by
  ext ⟨l, j⟩
  simp [rem, and_comm]

theorem deg_add_card (J : ∀ k, Finset (ι k)) (hJ : ∀ l, (J l).Nonempty) :
    ∑ l, ((J l).card - 1) + Fintype.card K = (Finset.univ.sigma J).card := by
  have h : Fintype.card K = ∑ _l : K, 1 := by simp
  rw [h, Finset.card_sigma, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => Nat.sub_add_cancel (Finset.card_pos.2 (hJ l))

theorem deg_rem {I : ∀ k, Finset (ι k)} {m : ℕ} (hI : (∀ l, (I l).Nonempty) ∧ ∑ l, ((I l).card - 1) = m + 1)
    {p : Σ k, ι k} (hp : p ∈ Finset.univ.sigma I) (hne : ∀ l, (rem I p l).Nonempty) :
    ∑ l, ((rem I p l).card - 1) = m := by
  have h1 := deg_add_card (rem I p) hne
  have h2 := deg_add_card I hI.1
  rw [sigma_rem, Finset.card_erase_of_mem hp] at h1
  have := hI.2
  omega

theorem cellRes_comp (S : Type) [CommRing S] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M]
    {J' J I : ∀ k, Finset (ι k)} (h₁ : ∀ l, J' l ⊆ J l) (h₂ : ∀ l, J l ⊆ I l)
    (x : LocalizedModule (KH.cellMon S J') M) :
    KH.cellRes S M J I (KH.cellRes S M J' J x) = KH.cellRes S M J' I x := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono (S := S) h₁),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono (S := S) h₂),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono (S := S) fun l => (h₁ l).trans (h₂ l))]

theorem faceSign_block_lt (I : ∀ k, Finset (ι k)) {k k' : K} (hk : k < k') {i : ι k} (i' : ι k')
    (hi : i ∈ I k) (h2 : 2 ≤ (I k).card) :
    KH.faceSign I k' i' = -KH.faceSign (rem I ⟨k, i⟩) k' i' := by
  have hkm : k ∈ Finset.univ.filter (· < k') := by simp [hk]
  have e1 := Finset.add_sum_erase (Finset.univ.filter (· < k')) (fun l => ((rem I ⟨k, i⟩ l).card - 1)) hkm
  have e2 := Finset.add_sum_erase (Finset.univ.filter (· < k')) (fun l => ((I l).card - 1)) hkm
  have e3 : ∑ l ∈ (Finset.univ.filter (· < k')).erase k, ((rem I ⟨k, i⟩ l).card - 1) =
      ∑ l ∈ (Finset.univ.filter (· < k')).erase k, ((I l).card - 1) :=
    Finset.sum_congr rfl fun l hl => by rw [rem_ne I i (Finset.ne_of_mem_erase hl)]
  have e4 : (rem I ⟨k, i⟩ k).card = (I k).card - 1 := by rw [rem_same, Finset.card_erase_of_mem hi]
  have hoff : ∑ l ∈ Finset.univ.filter (· < k'), ((I l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k'), ((rem I ⟨k, i⟩ l).card - 1) + 1 := by omega
  unfold KH.faceSign
  rw [rem_ne I i hk.ne', hoff, ← add_assoc, pow_succ]
  ring

theorem faceSign_block_gt (I : ∀ k, Finset (ι k)) {k k' : K} (hk : k < k') (i : ι k) (i' : ι k') :
    KH.faceSign (rem I ⟨k', i'⟩) k i = KH.faceSign I k i := by
  unfold KH.faceSign
  rw [rem_ne I i' hk.ne, Finset.sum_congr rfl fun l hl =>
    by rw [rem_ne I i' ((Finset.mem_filter.1 hl).2.trans hk).ne]]

theorem faceSign_lt (I : ∀ k, Finset (ι k)) {k : K} {i i' : ι k} (h : i < i') (hi : i ∈ I k) :
    KH.faceSign I k i' = -KH.faceSign (rem I ⟨k, i⟩) k i' := by
  have hmem : i ∈ (I k).filter (· < i') := Finset.mem_filter.2 ⟨hi, h⟩
  have e1 : (((I k).erase i).filter (· < i')).card + 1 = ((I k).filter (· < i')).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one hmem]
  have e2 : ∑ l ∈ Finset.univ.filter (· < k), ((rem I ⟨k, i⟩ l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
    Finset.sum_congr rfl fun l hl => by rw [rem_ne I i (Finset.mem_filter.1 hl).2.ne]
  unfold KH.faceSign
  rw [rem_same, e2, ← e1, add_right_comm, pow_succ]
  ring

theorem faceSign_gt (I : ∀ k, Finset (ι k)) {k : K} {i i' : ι k} (h : i < i') :
    KH.faceSign (rem I ⟨k, i'⟩) k i = KH.faceSign I k i := by
  have e1 : ((I k).erase i').filter (· < i) = (I k).filter (· < i) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp only [Finset.mem_filter, not_and, not_lt]
    exact fun _ => h.le
  have e2 : ∑ l ∈ Finset.univ.filter (· < k), ((rem I ⟨k, i'⟩ l).card - 1) =
      ∑ l ∈ Finset.univ.filter (· < k), ((I l).card - 1) :=
    Finset.sum_congr rfl fun l hl => by rw [rem_ne I i' (Finset.mem_filter.1 hl).2.ne]
  unfold KH.faceSign
  rw [rem_same, e1, e2]

theorem sg_swap (I : ∀ k, Finset (ι k)) {p q : Σ k, ι k} (hp : p ∈ Finset.univ.sigma I)
    (hq : q ∈ Finset.univ.sigma I) (hpq : p ≠ q) (hX : ∀ l, (rem (rem I p) q l).Nonempty) :
    sg I p * sg (rem I p) q = -(sg I q * sg (rem I q) p) := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', i'⟩ := q
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hp hq
  simp only [sg]
  rcases lt_trichotomy k k' with hk | rfl | hk
  · have hX' := hX k
    rw [rem_ne _ i' hk.ne, rem_same] at hX'
    have h1 := Finset.card_pos.2 hX'
    rw [Finset.card_erase_of_mem hp] at h1
    rw [faceSign_block_lt I hk i' hp (by omega), faceSign_block_gt I hk i i']
    ring
  · have hii : i ≠ i' := fun h => hpq (by rw [h])
    rcases lt_or_gt_of_ne hii with h | h
    · rw [faceSign_lt I h hp, faceSign_gt I h]
      ring
    · rw [faceSign_lt I h hq, faceSign_gt I h]
      ring
  · have hX' := hX k'
    rw [rem_same, rem_ne _ i hk.ne] at hX'
    have h1 := Finset.card_pos.2 hX'
    rw [Finset.card_erase_of_mem hq] at h1
    rw [faceSign_block_lt I hk i hq (by omega), faceSign_block_gt I hk i' i]
    ring

variable (S : Type) [CommRing S] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M]

def val (n : ℕ) (φ : KH.CechC S ι M n) (X : ∀ k, Finset (ι k)) : LocalizedModule (KH.cellMon S X) M :=
  if h : (∀ l, (X l).Nonempty) ∧ ∑ l, ((X l).card - 1) = n then φ ⟨X, h⟩ else 0

theorem cechD_apply (n : ℕ) (φ : KH.CechC S ι M n) (I : KH.Cell K ι (n + 1)) :
    KH.cechD S ι M n φ I = ∑ p ∈ Finset.univ.sigma I.1,
      if (∀ l, (rem I.1 p l).Nonempty) ∧ ∑ l, ((rem I.1 p l).card - 1) = n then
        sg I.1 p • KH.cellRes S M (rem I.1 p) I.1 (val S M n φ (rem I.1 p)) else 0 := by
  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  have e := update_erase_eq_rem I.1 k i
  have key : ∀ (X Y : ∀ k, Finset (ι k)) (_ : X = Y) hX,
      KH.cellRes S M X I.1 (φ ⟨X, hX⟩) = KH.cellRes S M Y I.1 (val S M n φ Y) := by
    rintro X _ rfl hX
    unfold val
    rw [dif_pos hX]
  by_cases h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n
  · have h' : (∀ l, (rem I.1 ⟨k, i⟩ l).Nonempty) ∧ ∑ l, ((rem I.1 ⟨k, i⟩ l).card - 1) = n := e ▸ h
    rw [dif_pos h, if_pos h']
    exact congrArg (KH.faceSign I.1 k i • ·) (key _ _ e h)
  · have h' : ¬((∀ l, (rem I.1 ⟨k, i⟩ l).Nonempty) ∧ ∑ l, ((rem I.1 ⟨k, i⟩ l).card - 1) = n) := e ▸ h
    rw [dif_neg h, if_neg h']
    rfl

theorem val_cechD (n : ℕ) (φ : KH.CechC S ι M n) (X : ∀ k, Finset (ι k))
    (hX : (∀ l, (X l).Nonempty) ∧ ∑ l, ((X l).card - 1) = n + 1) :
    val S M (n + 1) (KH.cechD S ι M n φ) X = ∑ p ∈ Finset.univ.sigma X,
      if (∀ l, (rem X p l).Nonempty) ∧ ∑ l, ((rem X p l).card - 1) = n then
        sg X p • KH.cellRes S M (rem X p) X (val S M n φ (rem X p)) else 0 :=
  (dif_pos hX).trans (cechD_apply S M n φ ⟨X, hX⟩)

def pairTerm (n : ℕ) (φ : KH.CechC S ι M n) (I : ∀ k, Finset (ι k)) (p q : Σ k, ι k) :
    LocalizedModule (KH.cellMon S I) M :=
  if (∀ l, (rem (rem I p) q l).Nonempty) ∧ ∑ l, ((rem (rem I p) q l).card - 1) = n then
    (sg I p * sg (rem I p) q) • KH.cellRes S M (rem (rem I p) q) I (val S M n φ (rem (rem I p) q)) else 0

theorem pairTerm_self (n : ℕ) (φ : KH.CechC S ι M n) (I : ∀ k, Finset (ι k))
    (hI : (∀ l, (I l).Nonempty) ∧ ∑ l, ((I l).card - 1) = n + 1 + 1) {p : Σ k, ι k}
    (hp : p ∈ Finset.univ.sigma I) : pairTerm S M n φ I p p = 0 := by
  unfold pairTerm
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [rem_self] at h1 h2
  have := deg_rem hI hp h1
  omega

theorem pairTerm_swap (n : ℕ) (φ : KH.CechC S ι M n) (I : ∀ k, Finset (ι k)) {p q : Σ k, ι k}
    (hp : p ∈ Finset.univ.sigma I) (hq : q ∈ Finset.univ.sigma I) (hpq : p ≠ q) :
    pairTerm S M n φ I p q + pairTerm S M n φ I q p = 0 := by
  unfold pairTerm
  rw [rem_comm I q p]
  by_cases h : (∀ l, (rem (rem I p) q l).Nonempty) ∧ ∑ l, ((rem (rem I p) q l).card - 1) = n
  · rw [if_pos h, if_pos h, sg_swap I hp hq hpq h.1, neg_zsmul, neg_add_cancel]
  · rw [if_neg h, if_neg h, add_zero]

theorem step (n : ℕ) (φ : KH.CechC S ι M n) (I : ∀ k, Finset (ι k))
    (hI : (∀ l, (I l).Nonempty) ∧ ∑ l, ((I l).card - 1) = n + 1 + 1) {p : Σ k, ι k}
    (hp : p ∈ Finset.univ.sigma I) :
    (if (∀ l, (rem I p l).Nonempty) ∧ ∑ l, ((rem I p l).card - 1) = n + 1 then
        sg I p • KH.cellRes S M (rem I p) I (val S M (n + 1) (KH.cechD S ι M n φ) (rem I p)) else 0) =
      ∑ q ∈ Finset.univ.sigma I, pairTerm S M n φ I p q := by
  by_cases h : (∀ l, (rem I p l).Nonempty) ∧ ∑ l, ((rem I p l).card - 1) = n + 1
  · rw [if_pos h, val_cechD S M n φ _ h, map_sum, ← Finset.sum_zsmul, sigma_rem,
      ← Finset.sum_erase (Finset.univ.sigma I) (pairTerm_self S M n φ I hI hp)]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold pairTerm
    by_cases h' : (∀ l, (rem (rem I p) q l).Nonempty) ∧ ∑ l, ((rem (rem I p) q l).card - 1) = n
    · rw [if_pos h', if_pos h', map_zsmul, ← mul_zsmul,
        cellRes_comp S M (rem_subset _ q) (rem_subset _ p)]
    · rw [if_neg h', if_neg h', map_zero, zsmul_zero]
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    unfold pairTerm
    rw [if_neg]
    intro h'
    have hne : ∀ l, (rem I p l).Nonempty := fun l => (h'.1 l).mono (rem_subset _ q l)
    exact h ⟨hne, deg_rem hI hp hne⟩

theorem cechD_cechD (n : ℕ) (φ : KH.CechC S ι M n) :
    KH.cechD S ι M (n + 1) (KH.cechD S ι M n φ) = 0 := by
  funext I
  obtain ⟨I, hI⟩ := I
  refine (cechD_apply S M (n + 1) (KH.cechD S ι M n φ) ⟨I, hI⟩).trans ?_
  refine (Finset.sum_congr rfl fun p hp => step S M n φ I hI hp).trans ?_
  refine (Finset.sum_product' _ _ (fun p q => pairTerm S M n φ I p q)).symm.trans ?_
  refine Finset.sum_involution (fun x _ => x.swap) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hx
    obtain ⟨hp, hq⟩ := Finset.mem_product.1 hx
    show pairTerm S M n φ I p q + pairTerm S M n φ I q p = 0
    by_cases hpq : p = q
    · subst hpq
      rw [pairTerm_self S M n φ I hI hp, add_zero]
    · exact pairTerm_swap S M n φ I hp hq hpq
  · rintro ⟨p, q⟩ hx hne heq
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hne (pairTerm_self S M n φ I hI (Finset.mem_product.1 hx).1)
  · rintro ⟨p, q⟩ hx
    obtain ⟨hp, hq⟩ := Finset.mem_product.1 hx
    exact Finset.mem_product.2 ⟨hq, hp⟩
  · rintro x -
    exact Prod.swap_swap x

end KHCechDSq

theorem KHCechDSq.full : KH.CechDSqStatement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ n
  exact LinearMap.ext fun φ => KHCechDSq.cechD_cechD S M n φ

end

end GroundTheory.Heights₂.Heights.Kleiman
