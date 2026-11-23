import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.BorderedDeterminants

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem subRel : SubRel := by
  intro A _ n E hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold GlRel
    intro a b c d
    simpa [subA, Fin.castSucc_inj] using hE a.castSucc b.castSucc c.castSucc d.castSucc
  · unfold IsCov
    intro a b c
    have h := hE a.castSucc b.castSucc c.castSucc (Fin.last n)
    rw [if_neg (Fin.castSucc_lt_last a).ne', sub_zero] at h
    simp only [subA, etaK]
    rw [h]
    by_cases hbc : b = c
    · subst hbc; simp
    · rw [if_neg (fun e => hbc (Fin.castSucc_injective _ e)), if_neg hbc]
  · unfold IsVec
    intro a b c
    have h := hE a.castSucc b.castSucc (Fin.last n) c.castSucc
    rw [if_neg (Fin.castSucc_lt_last b).ne, zero_sub] at h
    simp only [subA, yK]
    rw [h]
    by_cases hac : a = c
    · subst hac; simp
    · rw [if_neg (fun e => hac (Fin.castSucc_injective _ e).symm), if_neg hac, neg_zero]
  · intro a b
    have h := hE a.castSucc (Fin.last n) b.castSucc (Fin.last n)
    rw [if_neg (Fin.castSucc_lt_last b).ne', if_neg (Fin.castSucc_lt_last a).ne', sub_zero] at h
    exact sub_eq_zero.mp h
  · intro a b
    have h := hE (Fin.last n) a.castSucc (Fin.last n) b.castSucc
    rw [if_neg (Fin.castSucc_lt_last a).ne, if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
    exact sub_eq_zero.mp h
  · intro a b
    have h := hE (Fin.last n) (Fin.last n) a.castSucc b.castSucc
    rw [if_neg (Fin.castSucc_lt_last a).ne', if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
    exact sub_eq_zero.mp h

section alg

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Tm_sub {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (v : ℂ) (a b : Fin n) :
    Tm (subA E) v a b = Tm E v a.castSucc b.castSucc := by
  simp [Tm, subA]

theorem qminor_sub {n t : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (a b : Fin t → Fin n) (u : ℂ) :
    qminor (subA E) a b u = qminor E (Fin.castSucc ∘ a) (Fin.castSucc ∘ b) u := by
  simp only [qminor, Tm_sub, Function.comp_apply]

theorem qdet_sub {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (u : ℂ) :
    qdet (subA E) u = qminor E Fin.castSucc Fin.castSucc u := by
  simp only [qdet, qminor_sub, Function.comp_id]

theorem bS_id (n : ℕ) : bS (Fin.castSucc : Fin n → Fin (n + 1)) (Fin.last n) = id := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [bS]
  | cast j => simp [bS]

theorem borderS' {n m : ℕ} (E : Fin n → Fin n → A) (es : Fin n) (v : Fin m → Fin n) (hE : GlRel E)
    (hvs : ∀ j, v j ≠ es) (u : ℂ) :
    qminor E (bS v es) (bS v es) u = qminor E v v u * Tm E (u - (m : ℂ)) es es -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) u * E (v w) es) := by
  rw [Qx6.expLCS E expansion_last_column, add_comm]
  refine Qx6.add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Qx6.qm_dropS E expansion_first_line quantumMinorRowSkew_holds hE, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Qx6.Tm_ne E _ (hvs w), Qx6.Tm_ne E _ (hvs x).symm, ← zsmul_eq_mul, smul_mul_assoc, smul_smul, ← pow_add,
    ← neg_smul]
  congr 1
  rw [Qx6.sgn_congr (b := (w : ℕ) + (x : ℕ) + 1) (by omega), pow_succ]
  ring

theorem borderE' {n m : ℕ} (E : Fin n → Fin n → A) (e : Fin n) (v : Fin m → Fin n) (hE : GlRel E)
    (hve : ∀ j, v j ≠ e) (u : ℂ) :
    qminor E (bE e v) (bE e v) u = Tm E u e e * qminor E v v (u - 1) -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x)) := by
  rw [Qx6.expFCE E expansion_first_column]
  refine Qx6.add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Qx6.qm_dropE E expansion_last_line quantumMinorRowSkew_holds hE, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Qx6.Tm_ne E _ (hve w), Qx6.Tm_ne E _ (hve x).symm, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add,
    ← neg_smul, show u - 1 - 1 = u - 2 by ring, mul_assoc]
  congr 1
  rw [show (w : ℕ) + 1 + (x : ℕ) = (w : ℕ) + (x : ℕ) + 1 by ring, pow_succ]
  ring

theorem qdet_bE {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (hE : GlRel E) (u : ℂ) :
    qdet E u = qminor E (bE (Fin.last n) Fin.castSucc) (bE (Fin.last n) Fin.castSucc) u := by
  unfold qdet
  rw [← bS_id, ← Qx6.bE_cyc, quantumMinorRowSkew_holds A, quantumMinorColSkew_holds A _ _ E hE, ← mul_assoc, ← Int.cast_mul,
    ← Units.val_mul, Int.units_mul_self]
  simp

end alg

theorem borderLast : BorderLast := by
  intro A _ _ n E hE u
  have h := borderS' E (Fin.last n) Fin.castSucc hE (fun j => (Fin.castSucc_lt_last j).ne) u
  rw [bS_id] at h
  rw [qdet_sub]
  simp only [qminor_sub]
  exact h

theorem borderFirst : BorderFirst := by
  intro A _ _ n E hE u
  have h := borderE' E (Fin.last n) Fin.castSucc hE (fun j => (Fin.castSucc_lt_last j).ne) u
  rw [qdet_bE E hE u, qdet_sub]
  simp only [qminor_sub]
  exact h

section mod

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem icast_apply (z : ℤ) (f : Module.End ℂ V) (v : V) :
    (((z : ℤ) : Module.End ℂ V) * f) v = (z : ℂ) • f v := by
  rw [Module.End.mul_apply]
  first
  | (simp [Int.cast_smul_eq_zsmul]; done)
  | (simp; exact (Int.cast_smul_eq_zsmul ℂ z (f v)).symm)

theorem sumBorder {n : ℕ} (Y H : Fin n → Module.End ℂ V) (M : Fin n → Fin n → Module.End ℂ V)
    (Ψ : Fin n → Fin n → V) (c : Fin n → ℂ) (v : V) (h1 : ∀ x, ∑ i, Ψ i x = H x v)
    (h3 : ∀ i x : Fin n, ∑ a : Fin n, ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • M a x (Ψ i a) = c i • Ψ i x) :
    (∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) * (Y x * M w x * H w)) v =
      ∑ x, Y x (∑ i, c i • Ψ i x) := by
  have key : ∀ w x : Fin n, ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) * (Y x * M w x * H w)) v =
      Y x (∑ i, ((-1 : ℂ) ^ ((w : ℕ) + (x : ℕ))) • M w x (Ψ i w)) := by
    intro w x
    rw [icast_apply, Module.End.mul_apply, Module.End.mul_apply, ← h1 w]
    simp only [map_sum, map_smul, Finset.smul_sum, Int.cast_pow, Int.cast_neg, Int.cast_one]
  simp only [LinearMap.sum_apply, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← map_sum (Y x), Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => h3 i x)

theorem sumBorder_zero {n : ℕ} (Y : Fin n → Module.End ℂ V) (Ψ : Fin n → Fin n → V) (c : Fin n → ℂ) (i : Fin n)
    (hΨ : ∀ x, Ψ i x = 0) (hc : ∀ i', i' ≠ i → c i' = 0) : ∑ x, Y x (∑ i', c i' • Ψ i' x) = 0 := by
  have h0 : ∀ x, ∑ i', c i' • Ψ i' x = 0 := by
    intro x
    refine Finset.sum_eq_zero (fun i' _ => ?_)
    by_cases h : i' = i
    · subst h; rw [hΨ x, smul_zero]
    · rw [hc i' h, zero_smul]
  simp [h0]

theorem comm_last {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hE : GlRel E) (c u : ℂ) :
    Commute (Tm E c (Fin.last n) (Fin.last n)) (qdet (subA E) u) := by
  have hc : ∀ a b : Fin n, Commute (E (Fin.last n) (Fin.last n)) (subA E a b) := by
    intro a b
    have h := hE (Fin.last n) (Fin.last n) a.castSucc b.castSucc
    rw [if_neg (Fin.castSucc_lt_last a).ne', if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
    exact sub_eq_zero.mp h
  have hT : ∀ w (a b : Fin n), Commute (Tm E c (Fin.last n) (Fin.last n)) (Tm (subA E) w a b) := by
    intro w a b
    unfold Tm
    rw [if_pos (rfl : Fin.last n = Fin.last n)]
    apply Commute.add_left
    · exact Algebra.commute_algebraMap_left _ _
    · apply Commute.add_right
      · split_ifs
        · exact Algebra.commute_algebraMap_right _ _
        · exact Commute.zero_right _
      · exact hc a b
  unfold qdet qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ (fun y hy => ?_)
  simp only [List.mem_ofFn, Set.mem_range] at hy
  obtain ⟨k, rfl⟩ := hy
  exact hT _ _ _

theorem cpol_self {n : ℕ} (m : Fin n → ℂ) (i : Fin n) : cpol m (-m i) = 0 := by
  unfold cpol
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)

theorem erase_zero {n : ℕ} (m : Fin n → ℂ) (i i' : Fin n) (h : i' ≠ i) :
    ∏ j ∈ Finset.univ.erase i', (-m i + m j) = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ _⟩) (by ring)

end mod

theorem raiseNZ_of (hC : CovUp) : RaiseNZ := by
  intro V _ _ n E l hE hq m hm hne i hi hbot
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hgl, hcov, -, -, -, -⟩ := subRel (Module.End ℂ V) n E hE
  obtain ⟨Ψ, h1, h2, h3⟩ := hC V n (subA E) (etaK E) hgl hcov m hm v hv
  have hΨ : ∀ x, Ψ i x = 0 := by
    intro x
    have hx := h2 i x
    rw [hbot] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have hmem : ∀ w, qdet (subA E) w v = cpol m w • v := by
    intro w
    have hv' : v ∈ ⨅ w : ℂ, LinearMap.ker (qdet (subA E) w - cpol m w • (1 : Module.End ℂ V)) := hv
    have hw := (Submodule.mem_iInf _).mp hv' w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hw
    simpa using hw
  have hB := borderLast (Module.End ℂ V) n E hE (-m i)
  have hsum := sumBorder (yK E) (etaK E) (fun w x => qminor (subA E) (skip1 w) (skip1 x) (-m i)) Ψ
    (fun i' => ∏ j ∈ Finset.univ.erase i', (-m i + m j)) v h1 (fun i' x => h3 i' x (-m i))
  have hz := sumBorder_zero (yK E) Ψ (fun i' => ∏ j ∈ Finset.univ.erase i', (-m i + m j)) i hΨ
    (fun i' hi' => erase_zero m i i' hi')
  have hq' := hq (-m i) v
  rw [hB, LinearMap.sub_apply, hsum, hz, sub_zero, Module.End.mul_apply] at hq'
  have hc := (comm_last E hE (-m i - (n : ℂ)) (-m i)).eq
  have h0 : qdet (subA E) (-m i) (Tm E (-m i - (n : ℂ)) (Fin.last n) (Fin.last n) v) = 0 := by
    have e := congrArg (fun f : Module.End ℂ V => f v) hc
    simp only [Module.End.mul_apply] at e
    rw [← e, hmem, cpol_self, zero_smul, map_zero]
  rw [h0] at hq'
  have hcl : cpol l (-m i) = 0 := by
    rcases smul_eq_zero.mp hq'.symm with h | h
    · exact h
    · exact absurd h hv0
  unfold cpol at hcl
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hcl
  exact hi j (by linear_combination -hj)

theorem lowerNZ_of (hD : VecDown) : LowerNZ := by
  intro V _ _ n E l hE hq m hm hne i hi hbot
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hgl, -, hvec, -, hyc, -⟩ := subRel (Module.End ℂ V) n E hE
  obtain ⟨Φ, h1, h2, h3⟩ := hD V n (subA E) (yK E) hgl hvec hyc m hm v hv
  have hΦ : ∀ x, Φ i x = 0 := by
    intro x
    have hx := h2 i x
    rw [hbot] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have hmem : ∀ w, qdet (subA E) w v = cpol m w • v := by
    intro w
    have hv' : v ∈ ⨅ w : ℂ, LinearMap.ker (qdet (subA E) w - cpol m w • (1 : Module.End ℂ V)) := hv
    have hw := (Submodule.mem_iInf _).mp hv' w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hw
    simpa using hw
  have hB := borderFirst (Module.End ℂ V) n E hE (1 - m i)
  have h3' : ∀ i' x : Fin n, ∑ a : Fin n, ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) •
      qminor (subA E) (skip1 x) (skip1 a) (1 - m i - 2) (Φ i' a) =
      (∏ j ∈ Finset.univ.erase i', (-m i + m j)) • Φ i' x := by
    intro i' x
    have e := h3 i' x (-m i)
    have e2 : (-m i - 1 : ℂ) = 1 - m i - 2 := by ring
    rw [e2] at e
    rw [← e]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Nat.add_comm]
  have hswap : (∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) *
        (etaK E w * qminor (subA E) (skip1 w) (skip1 x) (1 - m i - 2) * yK E x)) =
      ∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : Module.End ℂ V) *
        (etaK E x * qminor (subA E) (skip1 x) (skip1 w) (1 - m i - 2) * yK E w) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun x _ => ?_))
    rw [Nat.add_comm]
  have hsum := sumBorder (etaK E) (yK E) (fun w x => qminor (subA E) (skip1 x) (skip1 w) (1 - m i - 2)) Φ
    (fun i' => ∏ j ∈ Finset.univ.erase i', (-m i + m j)) v h1 h3'
  have hz := sumBorder_zero (etaK E) Φ (fun i' => ∏ j ∈ Finset.univ.erase i', (-m i + m j)) i hΦ
    (fun i' hi' => erase_zero m i i' hi')
  have hq' := hq (1 - m i) v
  rw [hB, LinearMap.sub_apply, hswap, hsum, hz, sub_zero, Module.End.mul_apply] at hq'
  have e3 : (1 - m i - 1 : ℂ) = -m i := by ring
  rw [e3, hmem, cpol_self, zero_smul, map_zero] at hq'
  have hcl : cpol l (1 - m i) = 0 := by
    rcases smul_eq_zero.mp hq'.symm with h | h
    · exact h
    · exact absurd h hv0
  unfold cpol at hcl
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hcl
  exact hi j (by linear_combination -hj)

end Formalism.FourierDecayAlt.P.BorderedDeterminants

namespace Formalism.FourierDecayAlt.P

theorem submodule_relations : Qr.SubRel := BorderedDeterminants.subRel
theorem border_last : Qr.BorderLast := BorderedDeterminants.borderLast
theorem border_first : Qr.BorderFirst := BorderedDeterminants.borderFirst
theorem qr_raiseNZ_of : Qr.CovUp → Qr.RaiseNZ := BorderedDeterminants.raiseNZ_of
theorem qr_lowerNZ_of : Qr.VecDown → Qr.LowerNZ := BorderedDeterminants.lowerNZ_of

end Formalism.FourierDecayAlt.P
