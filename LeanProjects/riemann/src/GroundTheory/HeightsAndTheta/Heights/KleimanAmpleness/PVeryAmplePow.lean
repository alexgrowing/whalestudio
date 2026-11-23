import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmplePowSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise

noncomputable section

universe u w

namespace VeryAmplePow

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def mono {r j : ℕ} (h : Fin (r + 1) → Ω) (w : Fin j → Fin (r + 1)) : Ω := ∏ t, h (w t)

theorem range_mono {r j : ℕ} (h : Fin (r + 1) → Ω) :
    Set.range (mono (j := j) h) = Set.range h ^ j := by
  ext a
  rw [Set.mem_pow_iff_prod]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨fun t => h (w t), fun t => ⟨w t, rfl⟩, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    choose w hw using hf
    exact ⟨w, by simp only [mono, hw]⟩

theorem mono_mem {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hH : ∀ l I, h l ∈ H.sub I) (w : Fin j → Fin (r + 1)) (I : Chart x) :
    mono h w ∈ H.sub I ^ j := by
  rw [Submodule.pow_eq_span_pow_set]
  exact Submodule.subset_span (Set.mem_pow_iff_prod.mpr ⟨fun t => h (w t), fun t => hH _ I, rfl⟩)

theorem mono_succ {r j : ℕ} (h : Fin (r + 1) → Ω) (w : Fin (j + 1) → Fin (r + 1)) :
    mono h w = h (w 0) * mono h (Fin.tail w) := by
  simp only [mono, Fin.prod_univ_succ, Fin.tail]

theorem mono_cons {r j : ℕ} (h : Fin (r + 1) → Ω) (v : Fin (r + 1)) (t : Fin j → Fin (r + 1)) :
    mono h (Fin.cons v t : Fin (j + 1) → Fin (r + 1)) = h v * mono h t := by
  simp only [mono, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem ampleChart_le {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hH : ∀ l I, h l ∈ H.sub I) (w : Fin (j + 1) → Fin (r + 1)) (I : Chart x) :
    ampleChart H 1 (h (w 0)) I ⊆ ampleChart (H.pow (j + 1)) 1 (mono h w) I := by
  rintro a ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [SubSystem.pow_sub, one_mul] at hn
  rw [SubSystem.pow_sub, SubSystem.pow_sub, one_mul, ← pow_mul, mono_succ, mul_pow, ← mul_assoc,
    show (j + 1) * n = n + j * n by ring, pow_add, pow_mul]
  exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ (mono_mem hH _ I) n)

theorem isVeryAmpleBy_mono {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy H h) {m : ℕ} (E : (Fin (j + 1) → Fin (r + 1)) ≃ Fin (m + 1)) :
    IsVeryAmpleBy (H.pow (j + 1)) (fun k => mono h (E.symm k)) := by
  have hH : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  have hgen : ∀ k w', mono h w' / mono h (E.symm k) ∈
      ampleBase (S := S) (fun k => mono h (E.symm k)) k :=
    fun k w' => Algebra.subset_adjoin ⟨E w', by simp⟩
  refine ⟨fun k => ?_, fun I => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · exact (Submodule.mem_iInf _).mpr fun I => by
      rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
      exact mono_mem hH _ I
  · change Submodule.span _ (Set.range (mono h ∘ E.symm)) = _
    rw [EquivLike.range_comp, range_mono, ← Submodule.span_pow, hv.generates I, SubSystem.pow_sub]
  · have hk' : mono h (E.symm k) ≠ 0 := hk
    rw [mono_succ] at hk'
    have hl : h (E.symm k 0) ≠ 0 := left_ne_zero_of_mul hk'
    have hq : mono h (Fin.tail (E.symm k)) ≠ 0 := right_ne_zero_of_mul hk'
    intro a ha
    have hI : ∀ I, ∃ n, a * mono h (E.symm k) ^ n ∈ H.sub I ^ ((j + 1) * n) := fun I => by
      obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
      refine ⟨n, ?_⟩
      rwa [SubSystem.pow_sub, SubSystem.pow_sub, one_mul, ← pow_mul] at hn
    choose nI hnI using hI
    classical
    have hn0 : ∀ I, a * mono h (E.symm k) ^ (∑ I', nI I') ∈ H.sub I ^ ((j + 1) * ∑ I', nI I') :=
      fun I => by
        obtain ⟨d, hd⟩ : ∃ d, ∑ I', nI I' = nI I + d :=
          ⟨_, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ I))).symm⟩
        rw [hd, pow_add, ← mul_assoc, mul_add, pow_add]
        exact Submodule.mul_mem_mul (hnI I)
          (by rw [pow_mul]; exact Submodule.pow_mem_pow _ (mono_mem hH _ I) d)
    have hb : a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') ∈
        ampleRing H 1 (h (E.symm k 0)) := Set.mem_iInter.mpr fun I => ⟨(j + 1) * ∑ I', nI I', by
      rw [SubSystem.pow_sub, one_mul]
      have : a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') *
          h (E.symm k 0) ^ ((j + 1) * ∑ I', nI I') = a * mono h (E.symm k) ^ (∑ I', nI I') := by
        rw [pow_mul, div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hl))]
      rw [this]
      exact hn0 I⟩
    have hbase : ampleBase (S := S) h (E.symm k 0) ≤
        ampleBase (S := S) (fun k => mono h (E.symm k)) k := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨v, rfl⟩
      have : h v / h (E.symm k 0) =
          mono h (Fin.cons v (Fin.tail (E.symm k)) : Fin (j + 1) → Fin (r + 1)) / mono h (E.symm k) := by
        rw [mono_cons, mono_succ h (E.symm k), mul_div_mul_right _ _ hq]
      change h v / h (E.symm k 0) ∈ _
      rw [this]
      exact hgen k _
    have hinv : h (E.symm k 0) ^ (j + 1) / mono h (E.symm k) ∈
        ampleBase (S := S) (fun k => mono h (E.symm k)) k := by
      have : h (E.symm k 0) ^ (j + 1) = mono h (fun _ => E.symm k 0 : Fin (j + 1) → Fin (r + 1)) := by
        simp [mono, Finset.prod_const]
      rw [this]
      exact hgen k _
    have ha' : a = a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') *
        (h (E.symm k 0) ^ (j + 1) / mono h (E.symm k)) ^ (∑ I', nI I') := by
      rw [mul_assoc, ← mul_pow, div_mul_div_cancel₀ (pow_ne_zero _ hl),
        div_self (by rw [mono_succ]; exact hk'), one_pow, mul_one]
    rw [ha']
    exact Subalgebra.mul_mem _ (hbase (hv.closed _ hl hb)) (Subalgebra.pow_mem _ hinv _)
  · have hk' : mono h (E.symm k) ≠ 0 := hk
    rw [mono_succ] at hk'
    have hl : h (E.symm k 0) ≠ 0 := left_ne_zero_of_mul hk'
    obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hv.affine (E.symm k 0) hl
    have hR : ampleRing H 1 (h (E.symm k 0)) ⊆ ampleRing (H.pow (j + 1)) 1 (mono h (E.symm k)) :=
      fun c hc => Set.mem_iInter.mpr fun I => ampleChart_le hH _ I (Set.mem_iInter.mp hc I)
    refine ⟨n, a, b, J, fun i => hR (ha i), fun i => hR (hb i), hsum, fun i I => ?_⟩
    obtain ⟨e, he⟩ := hJ i I
    exact ⟨e, ampleChart_le hH _ I he⟩

end VeryAmplePow

theorem VeryAmplePow.proof : VeryAmplePow.Statement.{u, w} := by
  intro S _ Ω _ _ N x H j hH hj
  obtain ⟨r, h, hv⟩ := hH
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have hc : (r + 1) ^ (j + 1) - 1 + 1 = (r + 1) ^ (j + 1) :=
    Nat.sub_add_cancel (Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.succ_ne_zero r)))
  exact ⟨_, _, VeryAmplePow.isVeryAmpleBy_mono hv (finFunctionFinEquiv.trans (finCongr hc.symm))⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
