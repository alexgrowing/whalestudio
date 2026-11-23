import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCechExact
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

namespace KoszulCechExact

section Algebra

variable {L : Type*} [CommRing L] {R : ℕ}

def contr (w : Fin R → L) (F : Finset (Fin R) → L) (J : Finset (Fin R)) : L :=
  ∑ j, if j ∈ J then 0 else (kosSign J j : L) * (w j * F (insert j J))

def wedge (v : Fin R → L) (F : Finset (Fin R) → L) (J : Finset (Fin R)) : L :=
  ∑ j, if j ∈ J then (kosSign (J.erase j) j : L) * (v j * F (J.erase j)) else 0

theorem kosSign_insert (A : Finset (Fin R)) {x : Fin R} (hx : x ∉ A) (y : Fin R) :
    kosSign (insert x A) y = (if x < y then -1 else 1) * kosSign A y := by
  unfold kosSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hx]), pow_succ]; ring
  · ring

theorem kosSign_mul_self (A : Finset (Fin R)) (x : Fin R) : kosSign A x * kosSign A x = 1 := by
  unfold kosSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem kosSign_mul_self_cast (A : Finset (Fin R)) (x : Fin R) : (kosSign A x : L) * kosSign A x = 1 := by
  rw [← Int.cast_mul, kosSign_mul_self, Int.cast_one]

theorem kosSign_swap {J : Finset (Fin R)} {j k : Fin R} (hj : j ∉ J) (hk : k ∈ J) (hjk : j ≠ k) :
    kosSign J j * kosSign (insert j (J.erase k)) k = -(kosSign (J.erase k) k * kosSign (J.erase k) j) := by
  have hjA : j ∉ J.erase k := fun h => hj (Finset.mem_of_mem_erase h)
  have hkA : k ∉ J.erase k := Finset.notMem_erase k J
  have e : kosSign J j = kosSign (insert k (J.erase k)) j := by rw [Finset.insert_erase hk]
  rw [e, kosSign_insert _ hkA, kosSign_insert _ hjA]
  rcases lt_or_gt_of_ne hjk with h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
  · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring

theorem wedge_zero (v : Fin R → L) (J : Finset (Fin R)) : wedge v (fun _ => 0) J = 0 := by
  unfold wedge
  simp

theorem contr_wedge (v w : Fin R → L) (F : Finset (Fin R) → L) (J : Finset (Fin R)) :
    contr w (wedge v F) J + wedge v (contr w F) J = (∑ j, v j * w j) * F J := by
  have h1 : contr w (wedge v F) J = ∑ j, ∑ k, (if j ∈ J then 0 else if k ∈ insert j J then
      (kosSign J j : L) * (w j * ((kosSign ((insert j J).erase k) k : L) * (v k * F ((insert j J).erase k))))
      else 0) := by
    unfold contr wedge
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
  have h2 : wedge v (contr w F) J = ∑ j, ∑ k, (if k ∈ J then (if j ∈ J.erase k then 0 else
      (kosSign (J.erase k) k : L) * (v k * ((kosSign (J.erase k) j : L) * (w j * F (insert j (J.erase k))))))
      else 0) := by
    unfold contr wedge
    rw [Finset.sum_comm (f := fun j k => (if k ∈ J then (if j ∈ J.erase k then 0 else
      (kosSign (J.erase k) k : L) * (v k * ((kosSign (J.erase k) j : L) * (w j * F (insert j (J.erase k))))))
      else 0))]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · simp
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_eq_single j]
  · by_cases hj : j ∈ J
    · rw [if_pos hj, if_pos hj, if_neg (Finset.notMem_erase j J), Finset.insert_erase hj, zero_add]
      linear_combination (v j * w j * F J) * kosSign_mul_self_cast (L := L) (J.erase j) j
    · rw [if_neg hj, if_pos (Finset.mem_insert_self j J), Finset.erase_insert hj, if_neg hj, add_zero]
      linear_combination (v j * w j * F J) * kosSign_mul_self_cast (L := L) J j
  · intro k _ hkj
    by_cases hj : j ∈ J
    · rw [if_pos hj, zero_add]
      split_ifs with hk hjk
      · rfl
      · exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hkj, hj⟩) hjk
      · rfl
    · rw [if_neg hj]
      by_cases hk : k ∈ J
      · have hjk : j ∉ J.erase k := fun h => hj (Finset.mem_of_mem_erase h)
        rw [if_pos (Finset.mem_insert_of_mem hk), if_pos hk, if_neg hjk,
          Finset.erase_insert_of_ne (Ne.symm hkj)]
        have hs := congrArg (Int.cast : ℤ → L) (kosSign_swap hj hk (Ne.symm hkj))
        push_cast at hs
        linear_combination (w j * v k * F (insert j (J.erase k))) * hs
      · have hk' : k ∉ insert j J := by simp [Finset.mem_insert, hkj, hk]
        rw [if_neg hk', if_neg hk, add_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem ring_neg_one_mul (x : L) : (-1 : L) * x = -x := neg_one_mul x

end Algebra

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {V : Ideal (MRingOver S ι)} {R : ℕ}

def coeffs {p n : ℕ} (φ : KosC S ι V R p n) (I : KH.Cell K ι n) :
    Finset (Fin R) → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
  fun J => if h : J.card = p then φ ⟨J, h⟩ I else 0

def homotopy {n : ℕ} (v : ∀ I : KH.Cell K ι n, Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V))
    (p : ℕ) (φ : KosC S ι V R p n) : KosC S ι V R (p + 1) n :=
  fun J I => ∑ j : Fin R, if h : j ∈ J.1 then
    ((kosSign (J.1.erase j) j : ℤ) : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) *
      (v I j * φ ⟨J.1.erase j, by rw [Finset.card_erase_of_mem h, J.2, Nat.add_sub_cancel]⟩ I) else 0

theorem eq_of_coeffs {p n : ℕ} {φ ψ : KosC S ι V R p n} (h : ∀ I, coeffs φ I = coeffs ψ I) : φ = ψ := by
  funext J I
  have := congrFun (h I) J.1
  unfold coeffs at this
  rw [dif_pos J.2, dif_pos J.2] at this
  exact this

theorem coeffs_zero {p n : ℕ} (I : KH.Cell K ι n) : coeffs (0 : KosC S ι V R p n) I = fun _ => 0 := by
  funext J
  unfold coeffs
  split_ifs <;> rfl

theorem coeffs_kosD (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0) {p n : ℕ} (φ : KosC S ι V R (p + 1) n)
    (I : KH.Cell K ι n) : coeffs (kosD z p n φ) I = contr (fun j => restrict0 (z j) I) (coeffs φ I) := by
  funext J
  unfold coeffs contr
  dsimp only
  split_ifs with hJ
  · simp only [kosD, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj hc
    · rfl
    · rfl
    · exact absurd (by rw [Finset.card_insert_of_notMem hj, hJ]) hc
  · symm
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hj hc
    · rfl
    · rw [Finset.card_insert_of_notMem hj] at hc
      exact absurd (by omega) hJ
    · exact (congrArg (fun x => (kosSign J j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_zero _)).trans (mul_zero _)

theorem coeffs_homotopy {n : ℕ}
    (v : ∀ I : KH.Cell K ι n, Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V))
    {p : ℕ} (φ : KosC S ι V R p n) (I : KH.Cell K ι n) :
    coeffs (homotopy v p φ) I = wedge (v I) (coeffs φ I) := by
  funext J
  unfold coeffs wedge homotopy
  dsimp only
  split_ifs with hJ
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj hc
    · rfl
    · exact absurd (by rw [Finset.card_erase_of_mem hj, hJ, Nat.add_sub_cancel]) hc
    · rfl
  · symm
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hj hc
    · rw [Finset.card_erase_of_mem hj] at hc
      have := Finset.card_pos.mpr ⟨j, hj⟩
      exact absurd (by omega) hJ
    · exact (congrArg (fun x => (kosSign (J.erase j) j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_zero _)).trans (mul_zero _)
    · rfl

theorem contr_coeffs_zero {n : ℕ} (φ : KosC S ι V R 0 n) (I : KH.Cell K ι n)
    (w : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) : contr w (coeffs φ I) = fun _ => 0 := by
  funext J
  unfold contr coeffs
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hj hc
  · rfl
  · exact absurd hc (Finset.card_ne_zero.mpr (Finset.insert_nonempty j J))
  · exact (congrArg (fun x => (kosSign J j : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V)) * x)
        (mul_zero _)).trans (mul_zero _)

theorem cellRes_mem_locPart {J I : ∀ k, Finset (ι k)} (h : KH.cellMon S J ≤ KH.cellMon S I) {c : K → ℤ}
    {x : LocalizedModule (KH.cellMon S J) (MRingOver S ι ⧸ V)}
    (hx : x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S J) c) :
    KH.cellRes S _ J I x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I) c := by
  unfold KH.locPart at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [GenTwistGenerated.cellRes_mk h]
    exact GenTwistGenerated.mk_mem_locPart m _ a ht hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx =>
    induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [GenTwistGenerated.cellRes_mk h] at hx
      rw [LocalizedModule.smul'_mk, GenTwistGenerated.cellRes_mk h, ← LocalizedModule.smul'_mk]
      exact Submodule.smul_mem _ s hx

theorem cellRes_one {J I : ∀ k, Finset (ι k)} (h : KH.cellMon S J ≤ KH.cellMon S I) :
    KH.cellRes S (MRingOver S ι ⧸ V) J I 1 = 1 := by
  have e : ∀ T : Submonoid (MRingOver S ι),
      (1 : LocalizedModule T (MRingOver S ι ⧸ V)) = LocalizedModule.mk 1 1 := fun _ => OreLocalization.one_def
  rw [e, GenTwistGenerated.cellRes_mk h, e]
  rfl

theorem one_mul_mem_locPart {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    (1 : LocalizedModule T (MRingOver S ι ⧸ V)) * x ∈ KH.locPart ι (KH.quotPart S V) T c := by
  have e : (1 : LocalizedModule T (MRingOver S ι ⧸ V)) * x = x := one_mul x
  rw [e]; exact hx

theorem neg_one_mul_mem_locPart {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    (-1 : LocalizedModule T (MRingOver S ι ⧸ V)) * x ∈ KH.locPart ι (KH.quotPart S V) T c := by
  have e : (-1 : LocalizedModule T (MRingOver S ι ⧸ V)) * x = -x := ring_neg_one_mul x
  rw [e]; exact neg_mem hx

theorem mem_kosPart_iff {α c : K → ℤ} {p n : ℕ} (φ : KosC S ι V R p n) :
    φ ∈ kosPart S ι V R α c p n ↔
      ∀ J I, φ J I ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (c - (p : ℤ) • α) := by
  simp [kosPart, KH.cechCc, Submodule.mem_pi]

theorem homotopy_mem {α c : K → ℤ} {n : ℕ}
    (v : ∀ I : KH.Cell K ι n, Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V))
    (hv : ∀ I j, v I j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α))
    {p : ℕ} (φ : KosC S ι V R p n) (hφ : φ ∈ kosPart S ι V R α c p n) :
    homotopy v p φ ∈ kosPart S ι V R α c (p + 1) n := by
  rw [mem_kosPart_iff] at hφ ⊢
  intro J I
  refine Submodule.sum_mem _ fun j _ => ?_
  split_ifs with hj
  · have hm := GenTwistGenerated.locPart_mul (hv I j)
      (hφ ⟨J.1.erase j, by rw [Finset.card_erase_of_mem hj, J.2, Nat.add_sub_cancel]⟩ I)
    have e : -α + (c - (p : ℤ) • α) = c - ((p + 1 : ℕ) : ℤ) • α := by
      funext k
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e] at hm
    unfold kosSign
    rcases neg_one_pow_eq_or ℤ ((J.1.erase j).filter (· < j)).card with h | h
    · rw [h, Int.cast_one]
      exact one_mul_mem_locPart hm
    · rw [h, Int.cast_neg, Int.cast_one]
      exact neg_one_mul_mem_locPart hm
  · exact Submodule.zero_mem _

end KoszulCechExact

open KoszulCechExact in

theorem KoszulCechExact.proof : KoszulCechExact.Statement := by
  intro S _ K _ _ ι _ _ V α R z hz c n
  choose u hu h1 using hz
  have hle : ∀ I : KH.Cell K ι n, KH.cellMon S (frontCell I).1 ≤ KH.cellMon S I.1 := fun I =>
    GenTwistGenerated.cellMon_mono fun k => Finset.singleton_subset_iff.mpr (Finset.min'_mem _ _)
  let v : ∀ I : KH.Cell K ι n, Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    fun I j => KH.cellRes S _ (frontCell I).1 I.1 (u (frontCell I) j)
  have hvdeg : ∀ I j, v I j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α) := fun I j =>
    cellRes_mem_locPart (hle I) (hu _ j)
  have hone : ∀ I : KH.Cell K ι n, ∑ j, v I j * restrict0 (z j) I = 1 := by
    intro I
    simp only [v, restrict0, ← GenTwistGenerated.cellRes_mul]
    rw [← map_sum, h1, cellRes_one (hle I)]
  have key : ∀ {p : ℕ} (φ : KosC S ι V R p n),
      (∀ I, contr (fun j => restrict0 (z j) I) (coeffs φ I) = fun _ => 0) →
      kosD z p n (homotopy v p φ) = φ := by
    intro p φ h0
    refine eq_of_coeffs fun I => ?_
    funext J
    rw [coeffs_kosD, coeffs_homotopy]
    have := contr_wedge (v I) (fun j => restrict0 (z j) I) (coeffs φ I) J
    rw [h0 I, wedge_zero, add_zero, hone I] at this
    exact this.trans (one_mul (coeffs φ I J))
  refine ⟨fun φ hφ => ⟨homotopy v 0 φ, homotopy_mem v hvdeg φ hφ,
    key φ fun I => contr_coeffs_zero φ I _⟩, fun p φ hφ hd => ⟨homotopy v (p + 1) φ,
    homotopy_mem v hvdeg φ hφ, key φ fun I => ?_⟩⟩
  rw [← coeffs_kosD, hd]
  exact coeffs_zero I

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
