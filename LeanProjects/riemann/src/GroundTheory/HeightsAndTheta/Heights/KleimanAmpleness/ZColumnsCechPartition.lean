import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechCone
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech.Partition

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V]
  [Module R V]

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then
    s ⟨⟨A, Finset.card_pos.mp (h.1 ▸ Nat.succ_pos i), h.2⟩, h.1⟩
  else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by
  unfold onSet
  rw [dif_pos ⟨I.2, I.1.2.2⟩]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

def coneY {i : ℕ} (k : Fin n) (z : Cech.Cochain (fun _ : Cell U => V) (i + 1)) (A : Finset (Fin n)) : V :=
  if k ∈ A then 0 else Cech.sgn (insert k A) k • onSet z (insert k A)

theorem cone_d {i : ℕ} {z : Cech.Cochain (fun _ : Cell U => V) (i + 1)}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0) {k : Fin n} (hk : k ∈ U)
    (K : Cech.Idx U (i + 1)) :
    ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) = z K := by
  have hcoc : ∀ L : Finset (Fin n), L ⊆ U → L.card = i + 1 + 1 + 1 →
      ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
    intro L hLU hL
    have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), hLU⟩, hL⟩
    rw [d_eq] at h
    exact h
  rw [← onSet_idx z K]
  have hK : K.1.1.card = i + 1 + 1 := K.2
  have hKU : K.1.1 ⊆ U := K.1.2.2
  generalize K.1.1 = Kf at hK hKU ⊢
  by_cases h : k ∈ Kf
  · rw [Finset.sum_eq_single k]
    · rw [coneY, if_neg (Finset.notMem_erase k Kf), Finset.insert_erase h, smul_smul,
        Cech.Cone.sgn_mul_self, one_smul]
    · intro j hj hne
      rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
    · exact fun h' => absurd h h'
  · have hc := hcoc (insert k Kf) (Finset.insert_subset hk hKU)
      (by rw [Finset.card_insert_of_notMem h, hK])
    rw [Finset.sum_insert h, Finset.erase_insert h] at hc
    have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
    have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY k z (Kf.erase j) =
        -(Cech.sgn (insert k Kf) k •
          ∑ j ∈ Kf, Cech.sgn (insert k Kf) j • onSet z ((insert k Kf).erase j)) := by
      rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : k ≠ j := fun e => h (e ▸ hj)
      have hni : k ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
      rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
        Cech.Cone.sgn_key h hj, neg_smul]
    rw [hs, hb, smul_neg, neg_neg, smul_smul, Cech.Cone.sgn_mul_self, one_smul]

theorem exact_of_partition {A : Type w} [Semiring A] [Module A V] (M : Cell U → Submodule R V)
    {i : ℕ} (z : Cech.Cochain (fun _ : Cell U => V) (i + 1))
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0)
    (a : Fin n → A) (ha : ∑ k ∈ U, a k = 1)
    (hmem : ∀ (K : Cech.Idx U i) (k : Fin n), k ∈ U → k ∉ K.1.1 →
      a k • onSet z (insert k K.1.1) ∈ M K.1) :
    ∃ t ∈ Cech.Cdeg (fun _ : Cell U => V) M i,
      Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i t = z := by
  refine ⟨fun K => ∑ k ∈ U, a k • coneY k z K.1.1, fun K _ => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k hk => ?_
    unfold coneY
    split_ifs with h
    · rw [smul_zero]; exact zero_mem _
    · rw [smul_comm]; exact zsmul_mem (hmem K k hk h) _
  · funext K
    rw [d_eq]
    have hY : ∀ j ∈ K.1.1, onSet (fun I => ∑ k ∈ U, a k • coneY k z I.1.1 :
        Cech.Cochain (fun _ : Cell U => V) i) (K.1.1.erase j) =
          ∑ k ∈ U, a k • coneY k z (K.1.1.erase j) := by
      intro j hj
      unfold onSet
      rw [dif_pos ⟨by rw [Finset.card_erase_of_mem hj, K.2]; rfl,
        (Finset.erase_subset _ _).trans K.1.2.2⟩]
    rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
    calc ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • ∑ k ∈ U, a k • coneY k z (K.1.1.erase j)
        = ∑ k ∈ U, a k • ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) := by
          simp_rw [Finset.smul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      _ = ∑ k ∈ U, a k • z K := Finset.sum_congr rfl fun k hk => by rw [cone_d hz hk K]
      _ = z K := by rw [← Finset.sum_smul, ha, one_smul]

theorem onSet_pair {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    {a b : Fin n} (haU : a ∈ U) (hbU : b ∈ U) (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin n)).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _,
    Finset.insert_subset haU (Finset.singleton_subset_iff.mpr hbU)⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin n)), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin n)) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, Cech.Cone.sgn_insert ha, Cech.Cone.sgn_insert ha, if_neg (lt_irrefl _),
    if_pos hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin n)) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin n)) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    (I K : Cech.Idx U 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  have haU : a ∈ U := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  have hbU : b ∈ U := K.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self b)
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz haU hbU h
  · rfl
  · exact (onSet_pair hz hbU haU h).symm

end Cech.Partition

end

end GroundTheory.Heights₂.Heights.Kleiman
