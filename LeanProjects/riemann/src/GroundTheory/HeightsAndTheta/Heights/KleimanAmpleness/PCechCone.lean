import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace Cech.Cone

section Signs

variable {n : ℕ}

theorem sgn_insert {a b : Fin n} {A : Finset (Fin n)} (ha : a ∉ A) :
    Cech.sgn (insert a A) b = Cech.sgn A b * (if a < b then -1 else 1) := by
  unfold Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), pow_succ]
  · rw [mul_one]

theorem sgn_mul_self (A : Finset (Fin n)) (b : Fin n) : Cech.sgn A b * Cech.sgn A b = 1 := by
  unfold Cech.sgn
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgn_key {K : Finset (Fin n)} {i₀ j : Fin n} (hi₀ : i₀ ∉ K) (hj : j ∈ K) :
    Cech.sgn K j * Cech.sgn (insert i₀ (K.erase j)) i₀ =
      -(Cech.sgn (insert i₀ K) i₀ * Cech.sgn (insert i₀ K) j) := by
  have hne : j ≠ i₀ := fun e => hi₀ (e ▸ hj)
  have h1 : Cech.sgn (insert i₀ (K.erase j)) i₀ = Cech.sgn (K.erase j) i₀ := by
    rw [sgn_insert (fun hm => hi₀ (Finset.mem_of_mem_erase hm)), if_neg (lt_irrefl _), mul_one]
  have h2 : Cech.sgn (insert i₀ K) i₀ = Cech.sgn K i₀ := by
    rw [sgn_insert hi₀, if_neg (lt_irrefl _), mul_one]
  have h3 := sgn_insert (b := j) hi₀
  have h4 := sgn_insert (b := i₀) (Finset.notMem_erase j K)
  rw [Finset.insert_erase hj] at h4
  rw [h1, h2, h3, h4]
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [if_pos h, if_neg (lt_asymm h)]; ring
  · simp only [if_neg (lt_asymm h), if_pos h]; ring

end Signs

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i) (A : Finset (Fin (N + 1))) : V :=
  if h : A.card = i + 1 then
    s ⟨⟨A, Finset.card_pos.mp (by omega), Finset.subset_univ A⟩, h⟩
  else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) : onSet s I.1.1 = s I := by
  unfold onSet
  rw [dif_pos I.2]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) :
    Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

def coneY {i : ℕ} (i₀ : Fin (N + 1)) (z : Cech.Cochain (fun _ : StdCell N => V) (i + 1))
    (A : Finset (Fin (N + 1))) : V :=
  if i₀ ∈ A then 0 else Cech.sgn (insert i₀ A) i₀ • onSet z (insert i₀ A)

theorem onSet_pair {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    {a b : Fin (N + 1)} (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin (N + 1))).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin (N + 1))), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin (N + 1))) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, sgn_insert ha, sgn_insert ha, if_neg (lt_irrefl _), if_pos hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin (N + 1))) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin (N + 1))) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    (I K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz h
  · rfl
  · exact (onSet_pair hz h).symm

end Cech.Cone

open Cech.Cone in

theorem Cech.Cone.proof : Cech.Cone.Statement.{u, v} := by
  intro R _ V _ _ N J
  refine ⟨?_, ?_, fun z hz I K => const hz I K⟩
  · intro W i₀ hi₀ i z hz hW hJ
    have hWs : ∀ A, onSet z A ∈ W := by
      intro A; unfold onSet; split_ifs
      · exact hW _
      · exact W.zero_mem
    have hJs : ∀ A, ¬ J ⊆ A → onSet z A = 0 := by
      intro A hA; unfold onSet; split_ifs
      · exact hJ _ hA
      · rfl
    have hcoc : ∀ L : Finset (Fin (N + 1)), L.card = i + 1 + 1 + 1 →
        ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
      intro L hL
      have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), Finset.subset_univ L⟩, hL⟩
      rw [d_eq] at h
      exact h
    refine ⟨fun I => coneY i₀ z I.1.1, fun I => ?_, fun I hI => ?_, ?_⟩
    · change coneY i₀ z I.1.1 ∈ W
      unfold coneY; split_ifs
      · exact W.zero_mem
      · exact zsmul_mem (hWs _) _
    · change coneY i₀ z I.1.1 = 0
      unfold coneY; split_ifs
      · rfl
      · rw [hJs _ fun hs => hI fun x hx =>
          (Finset.mem_insert.mp (hs hx)).resolve_left fun (e : x = i₀) => hi₀ (e ▸ hx), smul_zero]
    · funext K
      rw [d_eq, ← onSet_idx z K]
      have hK : K.1.1.card = i + 1 + 1 := K.2
      have hY : ∀ j ∈ K.1.1, onSet (fun I => coneY i₀ z I.1.1 :
          Cech.Cochain (fun _ : StdCell N => V) i) (K.1.1.erase j) = coneY i₀ z (K.1.1.erase j) := by
        intro j hj
        unfold onSet
        rw [dif_pos (by rw [Finset.card_erase_of_mem hj, hK]; rfl)]
      rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
      generalize K.1.1 = Kf at hK ⊢
      by_cases h : i₀ ∈ Kf
      · rw [Finset.sum_eq_single i₀]
        · rw [coneY, if_neg (Finset.notMem_erase i₀ Kf), Finset.insert_erase h, smul_smul,
            sgn_mul_self, one_smul]
        · intro j hj hne
          rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
        · exact fun h' => absurd h h'
      · have hc := hcoc (insert i₀ Kf) (by rw [Finset.card_insert_of_notMem h, hK])
        rw [Finset.sum_insert h, Finset.erase_insert h] at hc
        have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
        have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY i₀ z (Kf.erase j) =
            -(Cech.sgn (insert i₀ Kf) i₀ •
              ∑ j ∈ Kf, Cech.sgn (insert i₀ Kf) j • onSet z ((insert i₀ Kf).erase j)) := by
          rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : i₀ ≠ j := fun e => h (e ▸ hj)
          have hni : i₀ ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
          rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
            sgn_key h hj, neg_smul]
        rw [hs, hb, smul_neg, neg_neg, smul_smul, sgn_mul_self, one_smul]
  · intro hJne i₀ hi₀ z hz hJ
    obtain ⟨j, hj⟩ := hJne
    funext I
    let I₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{i₀}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    rw [const hz I I₀]
    exact hJ I₀ fun hs => hi₀ (Finset.mem_singleton.mp (hs hj) ▸ hj)

end

end GroundTheory.Heights₂.Heights.Kleiman
