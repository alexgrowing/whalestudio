import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KoszulCechComplex

set_option linter.unusedSectionVars false

open KoszulCech GenTwistGenerated

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem card_zeroCell (C : KH.Cell K ι 0) (l : K) : (C.1 l).card = 1 := by
  have h0 := (Finset.sum_eq_zero_iff.mp C.2.2) l (Finset.mem_univ _)
  have := (C.2.1 l).card_pos
  omega

theorem frontCell_sub {n : ℕ} (C : KH.Cell K ι n) (l : K) : (frontCell C).1 l ⊆ C.1 l :=
  Finset.singleton_subset_iff.mpr (Finset.min'_mem _ _)

theorem cellRes_comp {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] {A F I : ∀ k, Finset (ι k)}
    (h₁ : KH.cellMon S A ≤ KH.cellMon S F) (h₂ : KH.cellMon S F ≤ KH.cellMon S I)
    (x : LocalizedModule (KH.cellMon S A) M) :
    KH.cellRes S M F I (KH.cellRes S M A F x) = KH.cellRes S M A I x := by
  induction x using LocalizedModule.induction_on with
  | h m t => rw [cellRes_mk h₁, cellRes_mk h₂, cellRes_mk (h₁.trans h₂)]

theorem cellRes_smul {V : Ideal (MRingOver S ι)} {J I : ∀ k, Finset (ι k)}
    (h : KH.cellMon S J ≤ KH.cellMon S I) (s : S) (x : LocalizedModule (KH.cellMon S J) (MRingOver S ι ⧸ V)) :
    KH.cellRes S (MRingOver S ι ⧸ V) J I (s • x) = s • KH.cellRes S (MRingOver S ι ⧸ V) J I x := by
  induction x using LocalizedModule.induction_on with
  | h m t => rw [LocalizedModule.smul'_mk, cellRes_mk h, cellRes_mk h, LocalizedModule.smul'_mk]

theorem cellRes_mem_locPart {V : Ideal (MRingOver S ι)} {J I : ∀ k, Finset (ι k)}
    (h : KH.cellMon S J ≤ KH.cellMon S I) {c : K → ℤ}
    {x : LocalizedModule (KH.cellMon S J) (MRingOver S ι ⧸ V)}
    (hx : x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S J) c) :
    KH.cellRes S (MRingOver S ι ⧸ V) J I x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I) c := by
  unfold KH.locPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [cellRes_mk h]
    exact mk_mem_locPart m _ a ht hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [cellRes_smul h]; exact Submodule.smul_mem _ s hx

theorem cechD_pair {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] (E : KH.Cell K ι 1) (k₀ : K)
    (a b : ι k₀) (hab : a ≠ b) (hE : E.1 k₀ = {a, b}) (A B : KH.Cell K ι 0)
    (hA : A.1 = Function.update E.1 k₀ {a}) (hB : B.1 = Function.update E.1 k₀ {b}) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ f : KH.CechC S ι M 0,
      KH.cechD S ι M 0 f E = σ • (KH.cellRes S M A.1 E.1 (f A) - KH.cellRes S M B.1 E.1 (f B)) := by
  classical
  have hne : ∀ k, (E.1 k).Nonempty := E.2.1
  have hsum : ∑ k, ((E.1 k).card - 1) = 1 := E.2.2
  have hpos : ∀ k, 1 ≤ (E.1 k).card := fun k => Finset.card_pos.mpr (hne k)
  have hcard₀ : (E.1 k₀).card = 2 := by rw [hE]; exact Finset.card_pair hab
  have hother : ∀ l, l ≠ k₀ → (E.1 l).card = 1 := by
    intro l hl
    have h2 := Finset.sum_le_sum_of_subset (f := fun k => (E.1 k).card - 1) (Finset.subset_univ {l, k₀})
    rw [Finset.sum_pair hl] at h2
    have h3 := h2.trans hsum.le
    have := hpos l
    omega
  have hface : ∀ i ∈ E.1 k₀, (∀ l, (Function.update E.1 k₀ ((E.1 k₀).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update E.1 k₀ ((E.1 k₀).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((E.1 k₀).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, hcard₀]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]; exact hne l
    · by_cases hl : l = k₀
      · subst hl; rw [Function.update_self, hc]; rfl
      · rw [Function.update_of_ne hl, hother l hl]; rfl
  have ha : a ∈ E.1 k₀ := by rw [hE]; simp
  have hb : b ∈ E.1 k₀ := by rw [hE]; simp
  have hsign : KH.faceSign E.1 k₀ a = -KH.faceSign E.1 k₀ b := by
    unfold KH.faceSign
    rcases lt_or_gt_of_ne hab with h | h
    · have e₁ : ((E.1 k₀).filter (· < a)).card = 0 := by
        rw [hE]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      have e₂ : ((E.1 k₀).filter (· < b)).card = 1 := by
        rw [hE]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      rw [e₁, e₂]; ring
    · have e₁ : ((E.1 k₀).filter (· < a)).card = 1 := by
        rw [hE]; simp [Finset.filter_insert, Finset.filter_singleton, h]
      have e₂ : ((E.1 k₀).filter (· < b)).card = 0 := by
        rw [hE]; simp [Finset.filter_insert, Finset.filter_singleton, h.not_gt]
      rw [e₁, e₂]; ring
  have key : ∀ (f : KH.CechC S ι M 0) (C C' : KH.Cell K ι 0), C = C' →
      KH.cellRes S M C.1 E.1 (f C) = KH.cellRes S M C'.1 E.1 (f C') := by
    rintro f C _ rfl; rfl
  have eA : (⟨_, hface b hb⟩ : KH.Cell K ι 0) = A := by
    apply Subtype.ext
    show Function.update E.1 k₀ ((E.1 k₀).erase b) = A.1
    rw [hA, hE, Finset.pair_comm, Finset.erase_insert (by simpa using hab.symm)]
  have eB : (⟨_, hface a ha⟩ : KH.Cell K ι 0) = B := by
    apply Subtype.ext
    show Function.update E.1 k₀ ((E.1 k₀).erase a) = B.1
    rw [hB, hE, Finset.erase_insert (by simpa using hab)]
  refine ⟨KH.faceSign E.1 k₀ b, by unfold KH.faceSign; exact neg_one_pow_eq_or ℤ _, fun f => ?_⟩
  change (∑ k : K, ∑ i ∈ E.1 k, _ :
    KH.CechC S ι M 0 →ₗ[MRingOver S ι] LocalizedModule (KH.cellMon S E.1) M) f = _
  rw [Finset.sum_eq_single k₀, Finset.sum_eq_add_of_mem a b ha hb hab, dif_pos (hface a ha),
    dif_pos (hface b hb)]
  · rw [hsign, LinearMap.add_apply]
    change (-KH.faceSign E.1 k₀ b) • KH.cellRes S M _ E.1 (f ⟨_, hface a ha⟩) +
      KH.faceSign E.1 k₀ b • KH.cellRes S M _ E.1 (f ⟨_, hface b hb⟩) = _
    rw [key f _ _ eA, key f _ _ eB]
    generalize KH.faceSign E.1 k₀ b = σ
    generalize KH.cellRes S M A.1 E.1 (f A) = x
    generalize KH.cellRes S M B.1 E.1 (f B) = y
    have alg : ∀ {N : Type _} [AddCommGroup N] (σ : ℤ) (x y : N), -σ • y + σ • x = σ • (x - y) := by
      intros; rw [smul_sub, neg_smul, neg_add_eq_sub]
    exact alg σ x y
  · intro i hi hne'
    have : i = a ∨ i = b := by rw [hE] at hi; simpa using hi
    tauto
  · intro l _ hl
    refine Finset.sum_eq_zero fun i hi => dif_neg fun h => ?_
    have := (h.1 l)
    rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl] at this
    omega
  · intro h; exact absurd (Finset.mem_univ k₀) h

theorem res_agree {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] {z : KH.CechC S ι M 0}
    (hz : KH.cechD S ι M 0 z = 0) (I : ∀ k, Finset (ι k)) (A B : KH.Cell K ι 0) (hA : ∀ l, A.1 l ⊆ I l)
    (hB : ∀ l, B.1 l ⊆ I l) (k₀ : K) (hAB : ∀ l, l ≠ k₀ → A.1 l = B.1 l) :
    KH.cellRes S M A.1 I (z A) = KH.cellRes S M B.1 I (z B) := by
  classical
  by_cases hk : A.1 k₀ = B.1 k₀
  · have : A = B := Subtype.ext (funext fun l => by
      by_cases hl : l = k₀
      · rw [hl]; exact hk
      · exact hAB l hl)
    subst this; rfl
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (card_zeroCell A k₀)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (card_zeroCell B k₀)
  have hab : a ≠ b := fun h => hk (by rw [ha, hb, h])
  have hEne : ∀ l, (Function.update A.1 k₀ {a, b} l).Nonempty := by
    intro l
    by_cases hl : l = k₀
    · rw [hl, Function.update_self]; exact Finset.insert_nonempty _ _
    · rw [Function.update_of_ne hl]; exact A.2.1 l
  have hEsum : ∑ l, ((Function.update A.1 k₀ {a, b} l).card - 1) = 1 := by
    rw [Finset.sum_eq_single k₀]
    · rw [Function.update_self, Finset.card_pair hab]
    · intro l _ hl
      rw [Function.update_of_ne hl, card_zeroCell A l]; rfl
    · intro h; exact absurd (Finset.mem_univ k₀) h
  let E : KH.Cell K ι 1 := ⟨Function.update A.1 k₀ {a, b}, hEne, hEsum⟩
  have hAE : ∀ l, A.1 l ⊆ E.1 l := by
    intro l
    show A.1 l ⊆ Function.update A.1 k₀ {a, b} l
    by_cases hl : l = k₀
    · rw [hl, Function.update_self, ha]; simp
    · rw [Function.update_of_ne hl]
  have hBE : ∀ l, B.1 l ⊆ E.1 l := by
    intro l
    show B.1 l ⊆ Function.update A.1 k₀ {a, b} l
    by_cases hl : l = k₀
    · rw [hl, Function.update_self, hb]; simp
    · rw [Function.update_of_ne hl, hAB l hl]
  have hEI : ∀ l, E.1 l ⊆ I l := by
    intro l
    show Function.update A.1 k₀ {a, b} l ⊆ I l
    by_cases hl : l = k₀
    · rw [hl, Function.update_self]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hA _ (by rw [ha]; simp)
      · rw [Finset.mem_singleton] at hx; subst hx; exact hB _ (by rw [hb]; simp)
    · rw [Function.update_of_ne hl]; exact hA l
  have hA' : A.1 = Function.update E.1 k₀ {a} := by
    funext l
    show A.1 l = Function.update (Function.update A.1 k₀ {a, b}) k₀ {a} l
    by_cases hl : l = k₀
    · rw [hl, Function.update_self, ha]
    · rw [Function.update_of_ne hl, Function.update_of_ne hl]
  have hB' : B.1 = Function.update E.1 k₀ {b} := by
    funext l
    show B.1 l = Function.update (Function.update A.1 k₀ {a, b}) k₀ {b} l
    by_cases hl : l = k₀
    · rw [hl, Function.update_self, hb]
    · rw [Function.update_of_ne hl, Function.update_of_ne hl, hAB l hl]
  obtain ⟨σ, hσ, hd⟩ := cechD_pair (S := S) (M := M) E k₀ a b hab (Function.update_self _ _ _) A B hA' hB'
  rw [← cellRes_comp (cellMon_mono hAE) (cellMon_mono hEI), ← cellRes_comp (cellMon_mono hBE) (cellMon_mono hEI),
    res_eq_of_cechD hσ (hd z) hz]

theorem cellRes_restrict0_face {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {z : KH.CechC S ι M 0}
    (hz : KH.cechD S ι M 0 z = 0) {n : ℕ} (I : KH.Cell K ι (n + 1)) (k : K) (i : ι k)
    (h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n) :
    KH.cellRes S M (Function.update I.1 k ((I.1 k).erase i)) I.1 (restrict0 z (⟨_, h⟩ : KH.Cell K ι n)) =
      restrict0 z I := by
  have hFI : ∀ l, Function.update I.1 k ((I.1 k).erase i) l ⊆ I.1 l := by
    intro l
    by_cases hl : l = k
    · subst hl; rw [Function.update_self]; exact Finset.erase_subset _ _
    · rw [Function.update_of_ne hl]
  unfold restrict0
  rw [cellRes_comp (cellMon_mono (frontCell_sub (⟨_, h⟩ : KH.Cell K ι n))) (cellMon_mono hFI)]
  refine res_agree hz I.1 _ _ (fun l => (frontCell_sub _ l).trans (hFI l)) (frontCell_sub I) k fun l hl => ?_
  show {(Function.update I.1 k ((I.1 k).erase i) l).min' _} = {(I.1 l).min' _}
  simp only [Function.update_of_ne hl]

theorem cechD_mul_restrict0 {V : Ideal (MRingOver S ι)} {z : KH.CechC S ι (MRingOver S ι ⧸ V) 0}
    (hz : KH.cechD S ι (MRingOver S ι ⧸ V) 0 z = 0) {n : ℕ} (ψ : KH.CechC S ι (MRingOver S ι ⧸ V) n) :
    KH.cechD S ι (MRingOver S ι ⧸ V) n (fun I => restrict0 z I * ψ I) =
      fun I => restrict0 z I * KH.cechD S ι (MRingOver S ι ⧸ V) n ψ I := by
  funext I
  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  have hms : ∀ {κ : Type} (s : Finset κ) (r : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V))
      (g : κ → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)), r * ∑ k ∈ s, g k = ∑ k ∈ s, r * g k :=
    fun s r g => Finset.mul_sum s g r
  rw [hms]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hms]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · change KH.faceSign I.1 k i • KH.cellRes S _ _ I.1 (restrict0 z ⟨_, h⟩ * ψ ⟨_, h⟩) =
      restrict0 z I * (KH.faceSign I.1 k i • KH.cellRes S _ _ I.1 (ψ ⟨_, h⟩))
    rw [cellRes_mul, cellRes_restrict0_face hz I k i h]
    have alg : ∀ {A : Type} [CommRing A] (m : ℤ) (a b : A), m • (a * b) = a * (m • b) := by
      intros; simp only [zsmul_eq_mul]; ring
    exact alg (A := LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) _ _ _
  · exact (mul_zero (restrict0 z I)).symm

def kosExt {V : Ideal (MRingOver S ι)} {R q n : ℕ} (φ : KosC S ι V R q n) (T : Finset (Fin R)) :
    KH.CechC S ι (MRingOver S ι ⧸ V) n :=
  if h : T.card = q then φ ⟨T, h⟩ else 0

theorem kosExt_of_card {V : Ideal (MRingOver S ι)} {R q n : ℕ} (φ : KosC S ι V R q n) {T : Finset (Fin R)}
    (h : T.card = q) : kosExt φ T = φ ⟨T, h⟩ :=
  dif_pos h

theorem kosD_apply {V : Ideal (MRingOver S ι)} {R : ℕ} (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0) (p n : ℕ)
    (φ : KosC S ι V R (p + 1) n) (J : {J : Finset (Fin R) // J.card = p}) (I : KH.Cell K ι n) :
    kosD z p n φ J I = ∑ j : Fin R, if j ∈ J.1 then 0 else
      (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
        (restrict0 (z j) I * kosExt φ (insert j J.1) I) := by
  change (∑ j : Fin R, _) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ∈ J.1
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h, kosExt_of_card φ (by rw [Finset.card_insert_of_notMem h, J.2])]

theorem kosExt_kosCech {V : Ideal (MRingOver S ι)} {R q n : ℕ} (φ : KosC S ι V R q n) (T : Finset (Fin R)) :
    kosExt (kosCech S ι V R q n φ) T = KH.cechD S ι (MRingOver S ι ⧸ V) n (kosExt φ T) := by
  unfold kosExt
  split_ifs
  · rfl
  · exact (map_zero _).symm

theorem kosD_mem_kosPart {V : Ideal (MRingOver S ι)} {α : K → ℤ} {R : ℕ}
    {z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0} (hz : ∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0)
    (c : K → ℤ) (p n : ℕ) (φ : KosC S ι V R (p + 1) n) (hφ : φ ∈ kosPart S ι V R α c (p + 1) n) :
    kosD z p n φ ∈ kosPart S ι V R α c p n := by
  simp only [kosPart, KH.cechCc, Submodule.mem_toAddSubgroup, Submodule.mem_pi, Set.mem_univ,
    true_implies] at hφ ⊢
  have hr : ∀ j (I : KH.Cell K ι n), restrict0 (z j) I ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) α :=
    fun j I => cellRes_mem_locPart (cellMon_mono (frontCell_sub I))
      (Submodule.mem_pi.mp (hz j).1 (frontCell I) (Set.mem_univ _))
  have e : α + (c - ((p + 1 : ℕ) : ℤ) • α) = c - (p : ℤ) • α := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  intro J I
  rw [kosD_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  split_ifs with h
  · exact Submodule.zero_mem _
  · have hx : restrict0 (z j) I * kosExt φ (insert j J.1) I ∈
        KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (c - (p : ℤ) • α) := by
      rw [← e]
      refine locPart_mul (hr j I) ?_
      rw [kosExt_of_card φ (by rw [Finset.card_insert_of_notMem h, J.2])]
      exact hφ _ I
    convert zsmul_mem hx (kosSign J.1 j) using 1
    exact (zsmul_eq_mul (restrict0 (z j) I * kosExt φ (insert j J.1) I) (kosSign J.1 j)).symm

theorem kosCech_kosD {V : Ideal (MRingOver S ι)} {R : ℕ} {z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0}
    (hz : ∀ j, KH.cechD S ι (MRingOver S ι ⧸ V) 0 (z j) = 0) (p n : ℕ) (φ : KosC S ι V R (p + 1) n) :
    kosCech S ι V R p n (kosD z p n φ) = kosD z p (n + 1) (kosCech S ι V R (p + 1) n φ) := by
  funext J I
  have hsplit : kosD z p n φ J = ∑ j : Fin R, if j ∈ J.1 then 0 else
      (kosSign J.1 j) • (fun I' => restrict0 (z j) I' * kosExt φ (insert j J.1) I') := by
    funext I'
    rw [kosD_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · exact (zsmul_eq_mul (restrict0 (z j) I' * kosExt φ (insert j J.1) I') (kosSign J.1 j)).symm
  show KH.cechD S ι _ n (kosD z p n φ J) I = kosD z p (n + 1) (kosCech S ι V R (p + 1) n φ) J I
  rw [hsplit, map_sum, Finset.sum_apply, kosD_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [map_zero]; rfl
  · rw [map_zsmul, cechD_mul_restrict0 (hz j), kosExt_kosCech]
    exact zsmul_eq_mul (restrict0 (z j) I * KH.cechD S ι _ n (kosExt φ (insert j J.1)) I) (kosSign J.1 j)

theorem kosSign_insert_lt {R : ℕ} {J : Finset (Fin R)} {a b : Fin R} (ha : a ∉ J) (hab : a < b) :
    kosSign (insert a J) b = -kosSign J b := by
  unfold kosSign
  rw [Finset.filter_insert, if_pos hab,
    Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1), pow_succ]
  ring

theorem kosSign_insert_gt {R : ℕ} {J : Finset (Fin R)} {a b : Fin R} (hab : b < a) :
    kosSign (insert a J) b = kosSign J b := by
  unfold kosSign
  rw [Finset.filter_insert, if_neg (not_lt.mpr hab.le)]

theorem kosSign_swap {R : ℕ} {J : Finset (Fin R)} {j j' : Fin R} (hj : j ∉ J) (hj' : j' ∉ J) (hne : j ≠ j') :
    kosSign J j * kosSign (insert j J) j' = -(kosSign J j' * kosSign (insert j' J) j) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [kosSign_insert_lt hj h, kosSign_insert_gt h]; ring
  · rw [kosSign_insert_gt h, kosSign_insert_lt hj' h]; ring

theorem kosD_kosD {V : Ideal (MRingOver S ι)} {R : ℕ} (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0) (p n : ℕ)
    (φ : KosC S ι V R (p + 1 + 1) n) : kosD z p n (kosD z (p + 1) n φ) = 0 := by
  classical
  funext J I
  rw [kosD_apply]
  have hms : ∀ (r : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V))
      (g : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)),
      r * ∑ k, g k = ∑ k, r * g k :=
    fun r g => Finset.mul_sum Finset.univ g r
  have hm0 : ∀ (a b : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)), a * (b * 0) = 0 :=
    fun a b => (congrArg (fun y => a * y) (mul_zero b)).trans (mul_zero a)
  obtain ⟨G, hG⟩ : ∃ G : Fin R → Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V), ∀ j j',
      G j j' = if j ∈ J.1 then 0 else if j' ∈ insert j J.1 then 0 else
        (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * (restrict0 (z j) I *
          ((kosSign (insert j J.1) j' : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
            (restrict0 (z j') I * kosExt φ (insert j' (insert j J.1)) I))) := ⟨_, fun _ _ => rfl⟩
  have hA : ∀ j, (if j ∈ J.1 then 0 else
      (kosSign J.1 j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
        (restrict0 (z j) I * kosExt (kosD z (p + 1) n φ) (insert j J.1) I)) = ∑ j', G j j' := by
    intro j
    by_cases hj : j ∈ J.1
    · rw [if_pos hj]; exact (Finset.sum_eq_zero fun j' _ => (hG j j').trans (if_pos hj)).symm
    · rw [if_neg hj, kosExt_of_card _ (by rw [Finset.card_insert_of_notMem hj, J.2]), kosD_apply, hms, hms]
      refine Finset.sum_congr rfl fun j' _ => ?_
      dsimp only
      by_cases hj' : j' ∈ insert j J.1
      · rw [if_pos hj', hm0, hG, if_neg hj, if_pos hj']
      · rw [if_neg hj', hG, if_neg hj, if_neg hj']
  have hG0 : ∀ j j', (j ∈ J.1 ∨ j' ∈ J.1 ∨ j = j') → G j j' = 0 := by
    intro j j' h
    rw [hG]
    by_cases hj : j ∈ J.1
    · rw [if_pos hj]
    · rw [if_neg hj, if_pos]
      rcases h with h | h | h
      · exact absurd h hj
      · exact Finset.mem_insert_of_mem h
      · rw [h]; exact Finset.mem_insert_self _ _
  rw [Finset.sum_congr rfl fun j _ => hA j, ← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => x.swap) ?_ ?_ (fun x _ => Finset.mem_product.mpr
    ⟨Finset.mem_univ _, Finset.mem_univ _⟩) (fun x _ => Prod.swap_swap x)
  · rintro ⟨j, j'⟩ _
    show G j j' + G j' j = 0
    by_cases h : j ∈ J.1 ∨ j' ∈ J.1 ∨ j = j'
    · rw [hG0 j j' h, hG0 j' j (by tauto)]
      exact add_zero 0
    · simp only [not_or] at h
      obtain ⟨hj, hj', hne⟩ := h
      replace hne : j ≠ j' := hne
      have hs := kosSign_swap hj hj' hne
      have hs' : ((kosSign J.1 j : ℤ) : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
          (kosSign (insert j J.1) j' : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) =
          -((kosSign J.1 j' : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
            (kosSign (insert j' J.1) j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V))) := by
        have cast : ∀ {A : Type} [CommRing A] (a b c d : ℤ), a * b = -(c * d) →
            (a : A) * (b : A) = -((c : A) * (d : A)) := by
          intro A _ a b c d h; exact_mod_cast congrArg (fun x : ℤ => (x : A)) h
        exact cast (A := LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) _ _ _ _ hs
      rw [hG, hG, if_neg hj, if_neg hj', if_neg (by simp [Finset.mem_insert, hne.symm, hj']),
        if_neg (by simp [Finset.mem_insert, hne, hj]), Finset.insert_comm j j' J.1]
      linear_combination (restrict0 (z j) I * restrict0 (z j') I *
        kosExt φ (insert j' (insert j J.1)) I) * hs'
  · rintro ⟨j, j'⟩ _ hne heq
    apply hne
    have : j' = j := (Prod.ext_iff.mp heq).1
    exact hG0 j j' (Or.inr (Or.inr this.symm))

end KoszulCechComplex

open KoszulCech KoszulCechComplex in

theorem KoszulCechComplex.proof : KoszulCechComplex.Statement := by
  intro S _ K _ _ ι _ _ V α R z hz c p n
  exact ⟨kosD_mem_kosPart hz c p n, kosCech_kosD (fun j => LinearMap.mem_ker.mp (hz j).2) p n,
    kosD_kosD z p n⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
