import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralTensorSwapIffMemIdealSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorMulIntegralFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberIntegralFrameEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharIndicatorEqOneOfCongruentOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryLiftIdempotentPartStatement

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdExpand

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.StdRead.CharVal

variable {D : D7}

local notation "𝔸" => Formalism.MainNotions.StandardLatticesGL3.AE

def invM {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (𝔸 D) :=
  (((k : GL (Fin a) (𝔸 D))⁻¹ : GL (Fin a) (𝔸 D)) : Matrix (Fin a) (Fin a) (𝔸 D))

def valM {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (𝔸 D) :=
  ((k : GL (Fin a) (𝔸 D)) : Matrix (Fin a) (Fin a) (𝔸 D))

theorem invM_mul {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : invM k * valM k = 1 := Units.inv_mul _

theorem valM_mul {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : valM k * invM k = 1 := Units.mul_inv _

theorem int_of_hat {𝔪 : Ideal (𝓞 D.host.E)} {x : 𝔸 D} (hx : x ∈ hatId D 𝔪) : x ∈ OhE D :=
  (toE_int_iff x).1 ((GlobalTheory.T.memIdealIntegral_tensorSwap_iff_mem_idealSubgroup 𝔪 x).2 hx).1

theorem hat_mul_mat {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} {A B : Matrix (Fin a) (Fin a) (𝔸 D)} (hA : ∀ i j, A i j ∈ hatId D 𝔪)
    (hB : ∀ i j, B i j ∈ OhE D) (i j : Fin a) : (A * B) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId (hB l j) (hA i l)

theorem cong_iff {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} {N : Matrix (Fin a) (Fin a) (𝔸 D)} {r k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ intG D a) (h : ∀ i j, (N - invM k) i j ∈ hatId D 𝔪) :
    (∀ i j, (N - invM r) i j ∈ hatId D 𝔪) ↔ CongOne D 𝔪 (r⁻¹ * k) := by
  have hi := (GlobalTheory.NormSum.mem_intG k).1 hk
  change _ ↔ ∀ i j, (invM r * valM k - 1) i j ∈ hatId D 𝔪
  constructor
  · intro h' i j
    have e : invM r * valM k - 1 = ((N - invM k) - (N - invM r)) * valM k := by
      rw [sub_sub_sub_cancel_left, sub_mul, invM_mul]
    rw [e]
    exact hat_mul_mat (fun i j => sub_mem (h i j) (h' i j)) (fun i j => (hi i j).1) i j
  · intro h' i j
    have e : N - invM r = (N - invM k) - (invM r * valM k - 1) * invM k := by
      rw [sub_mul, mul_assoc, valM_mul, mul_one, one_mul, sub_sub, add_sub_cancel]
    rw [e]
    exact sub_mem (h i j) (hat_mul_mat h' (fun i j => (hi i j).2) i j)

theorem value {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hG : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hK : KillsCong ν 𝔪) {a : ℕ}
    {N : Matrix (Fin a) (Fin a) (𝔸 D)} {r : Formalism.MainNotions.StandardLatticesGL3.GA D a} (hr : r ∈ intG D a)
    (h : ∀ i j, (N - invM r) i j ∈ hatId D 𝔪) :
    (∃ x, IsUnitDet e (N.map (toE D)) x) ∧ starRingEnd ℂ (unitChar ν e (N.map (toE D))) = unitChar ν e (matE r) := by
  have hi := (GlobalTheory.NormSum.mem_intG r).1 hr
  have h1 := GlobalTheory.T.unitDetCharIndicator_eq_one_of_congruent_one e 𝔪 hG ν hK (N * valM r) fun i j => by
    rw [← invM_mul r, ← sub_mul]
    exact hat_mul_mat h (fun i j => (hi i j).1) i j
  obtain ⟨S, -, he, -⟩ := hG
  have h2 := GlobalTheory.T.unitDetCharIndicator_mul_integralFrame ν e (GlobalTheory.PlaceDatum.idemSum_mul_self he) (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he) (N.map (toE D))
    (Matrix.GeneralLinearGroup.map (toE D) (r : GL (Fin a) (𝔸 D))) (fun i j => (toE_int_iff _).2 (hi i j).1)
    (fun i j => (toE_int_iff _).2 (hi i j).2)
  rw [Matrix.map_mul] at h1
  have h3 : unitChar ν e (N.map (toE D)) * unitChar ν e (matE r) = 1 := h2.symm.trans h1
  have hx : ∃ x, IsUnitDet e (N.map (toE D)) x := by
    by_contra hx
    rw [unitChar, dif_neg hx, zero_mul] at h3
    exact zero_ne_one h3
  refine ⟨hx, ?_⟩
  obtain ⟨x, hx⟩ := hx
  rw [unitChar_eq ν e _ hx] at h3 ⊢
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]
  exact inv_eq_of_mul_eq_one_right h3

theorem unitBlock_mul {a d : ℕ} (M : Matrix (Fin a) (Fin a) (𝔸 D)) (i : Fin d) (j : Fin a) :
    (HMul.hMul ((unitBlock D 0 a d).map (inc D)) M : Matrix (Fin d) (Fin a) (𝔸 D)) i j =
      if h : i.1 < a then M ⟨i.1, h⟩ j else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.1, h⟩ (fun l _ hl => ?_) (fun hh => (hh (Finset.mem_univ _)).elim)]
    · simp [unitBlock]
    · have : i.1 ≠ l.1 := fun hh => hl (Fin.ext hh.symm)
      simp [unitBlock, this]
  · refine Finset.sum_eq_zero fun l _ => ?_
    have : i.1 ≠ l.1 := fun hh => h (hh ▸ l.2)
    simp [unitBlock, this]

theorem coset_iff {ε : 𝔸 D} {𝔪 : Ideal (𝓞 D.host.E)} (hε : 1 - ε ∈ hatId D 𝔪) {a d : ℕ} (had : a ≤ d)
    {r : Formalism.MainNotions.StandardLatticesGL3.GA D a} {z : Matrix (Fin d) (Fin a) D.host.E} (hz : IsIntE z) (ha : Approx 𝔪 0 r z)
    (W : Matrix (Fin d) (Fin a) (𝔸 D)) :
    (∀ i j, W i j - ε * inc D (z i j) ∈ hatId D 𝔪) ↔
      (∀ i j, (topL a W - invM r) i j ∈ hatId D 𝔪) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪 := by
  have h1 : ∀ i j, (W i j - if h : i.1 < a then invM r ⟨i.1, h⟩ j else 0) - (W i j - ε * inc D (z i j)) ∈ hatId D 𝔪 := by
    intro i j
    have h2 : inc D (z i j) - (if h : i.1 < a then invM r ⟨i.1, h⟩ j else 0) ∈ hatId D 𝔪 := by
      rw [← unitBlock_mul]
      exact ha i j
    obtain ⟨b, hb⟩ := hz i j
    have h3 := sub_mem h2 (GlobalTheory.FunObj.StdDatum.mul_mem_hatId (hb ▸ inc_int b : inc D (z i j) ∈ OhE D) hε)
    convert h3 using 1
    ring
  have h4 : ∀ (i : Fin a) j, (topL a W - invM r) i j = W ⟨i.1, i.2.trans_le had⟩ j - invM r i j := fun i j => by
    rw [Matrix.sub_apply, topL, dif_pos ⟨i.2.trans_le had, j.2⟩]
  constructor
  · intro h
    have h5 := fun i j => add_mem (h1 i j) (h i j)
    simp only [sub_add_cancel] at h5
    refine ⟨fun i j => ?_, fun i j hi => ?_⟩
    · have := h5 ⟨i.1, i.2.trans_le had⟩ j
      rwa [dif_pos i.2, ← h4] at this
    · have := h5 i j
      rwa [dif_neg (not_lt.2 hi), sub_zero] at this
  · rintro ⟨h, h'⟩ i j
    have h6 : (W i j - if h : i.1 < a then invM r ⟨i.1, h⟩ j else 0) ∈ hatId D 𝔪 := by
      split_ifs with hi
      · have := h ⟨i.1, hi⟩ j
        rwa [h4] at this
      · rw [sub_zero]
        exact h' i j (not_lt.1 hi)
    have := sub_mem h6 (h1 i j)
    rwa [sub_sub_cancel] at this

theorem sum_eq {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hG : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hK : KillsCong ν 𝔪) {a d : ℕ}
    (had : a ≤ d) {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)} (hR : ∀ r ∈ R, r ∈ intG D a)
    (hU : ∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) (W : Matrix (Fin d) (Fin a) (𝔸 D)) :
    ∑ r ∈ R, unitChar ν e (matE r) *
        (if (∀ i j, (topL a W - invM r) i j ∈ hatId D 𝔪) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪 then 1 else 0) =
      if (∀ i j, W i j ∈ OhE D) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪 then
        starRingEnd ℂ (unitChar ν e ((topL a W).map (toE D))) else 0 := by
  by_cases hc : ((∀ i j, W i j ∈ OhE D) ∧ ∀ i j, a ≤ i.1 → W i j ∈ hatId D 𝔪) ∧ ∃ x, IsUnitDet e ((topL a W).map (toE D)) x
  · obtain ⟨hc, x, hx⟩ := hc
    have hN : ∀ i j, topL a W i j ∈ OhE D := fun i j => by
      rw [topL, dif_pos ⟨i.2.trans_le had, j.2⟩]
      exact hc.1 _ _
    obtain ⟨S, -, he, -⟩ := id hG
    obtain ⟨k, hk, hkN⟩ := GlobalTheory.T.exists_integral_unitary_lift_idempotentPart e S he _ hN x hx
    have h1 : ∀ i j, (topL a W - invM k) i j ∈ hatId D 𝔪 := fun i j => by
      have := GlobalTheory.FunObj.StdDatum.mul_mem_hatId (sub_mem (hN i j) ((GlobalTheory.NormSum.mem_intG k).1 hk i j).2) (one_sub_eps_mod hG)
      convert this using 1
      rw [Matrix.sub_apply, invM]
      linear_combination -hkN i j
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hU k hk
    have h2 := (cong_iff hk h1).2 hrk
    rw [if_pos hc, Finset.sum_eq_single r (fun s hs hsr => ?_) (fun h => (h hr).elim), if_pos ⟨h2, hc.2⟩, mul_one,
      (value hG hK (hR r hr) h2).2]
    rw [if_neg fun h => hsr (hu s ⟨hs, (cong_iff hk h1).1 h.1⟩), mul_zero]
  · rw [Finset.sum_eq_zero fun r hr => ?_]
    · split_ifs with h
      · rw [unitChar, dif_neg fun hx => hc ⟨h, hx⟩, map_zero]
      · rfl
    · rw [if_neg fun h => hc ⟨⟨fun i j => ?_, h.2⟩, (value hG hK (hR r hr) h.1).1⟩, mul_zero]
      by_cases hi : i.1 < a
      · have := add_mem (int_of_hat (h.1 ⟨i.1, hi⟩ j)) ((GlobalTheory.NormSum.mem_intG r).1 (hR r hr) ⟨i.1, hi⟩ j).2
        rwa [Matrix.sub_apply, invM, sub_add_cancel, topL, dif_pos ⟨i.2, j.2⟩] at this
      · exact int_of_hat (h.2 i j (not_lt.1 hi))

theorem conj_stdFst_eq_sum : ∀ {D : D7} (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d), a ≤ d → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 → ∀ β : GL (Fin S.rank) (EAf D), IsIntM β.val → IsIntM (β⁻¹).val →
  ∀ R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
  ∀ z : Formalism.MainNotions.StandardLatticesGL3.GA D a → Matrix (Fin d) (Fin a) D.host.E, (∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r)) →
  (fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) =
    starRingEnd ℂ (unitChar ν e β.val) • ∑ r ∈ R, unitChar ν e (matE r) • cosInd e 𝔪 hS hT (z r) := by
  intro D S T a d hS hT had e 𝔪 hG ν hK β hβ hβ' R hR hU z hz
  subst hS hT
  funext t
  obtain ⟨SS, -, he, -⟩ := id hG
  let W : Matrix (Fin T.rank) (Fin S.rank) (𝔸 D) := Matrix.of fun i j => finQ D (t i j)
  have hW : ∀ i j, toEAf D (t i j) = toE D (W i j) := fun i j => (toE_finQ _).symm
  have hN : topL S.rank (Matrix.of fun i j => toEAf D (t i j)) = (topL S.rank W).map (toE D) := by
    ext i j
    rw [Matrix.map_apply, topL, topL, dif_pos ⟨i.2.trans_le had, j.2⟩, dif_pos ⟨i.2.trans_le had, j.2⟩]
    exact hW _ _
  have hc : ∀ r ∈ R, cosInd e 𝔪 rfl rfl (z r) t = if IsHalf e t then
      (if (∀ i j, (topL S.rank W - invM r) i j ∈ hatId D 𝔪) ∧ ∀ i j, S.rank ≤ i.1 → W i j ∈ hatId D 𝔪 then 1 else 0)
      else 0 := fun r hr => by
    rw [← ite_and, cosInd]
    refine if_congr (and_congr_right fun _ => ?_) rfl rfl
    rw [← coset_iff (one_sub_eps_mod hG) had (hz r hr).1 (hz r hr).2 W]
    refine forall₂_congr fun i j => ?_
    rw [← GlobalTheory.T.memIdealIntegral_tensorSwap_iff_mem_idealSubgroup, RingHom.map_sub, RingHom.map_mul, ← hW, toE_finQ, ← finQ_incA, toE_finQ]
    rfl
  rw [GlobalTheory.T.standardPairFirstMember_integralFrame_eq S T ν e 𝔪 β hβ hβ' t,
    GlobalTheory.T.unitDetCharIndicator_mul_integralFrame ν e (GlobalTheory.PlaceDatum.idemSum_mul_self he) (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he) _ β hβ hβ', hN]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun r hr => by rw [hc r hr]]
  by_cases ht : IsHalf e t
  · simp only [ht, true_and, if_true]
    rw [sum_eq hG hK had hR hU W]
    simp only [hW, toE_int_iff, GlobalTheory.T.memIdealIntegral_tensorSwap_iff_mem_idealSubgroup]
    split_ifs
    · rw [map_mul, mul_comm]
    · rw [map_zero, mul_zero]
  · simp [ht]

end GlobalTheory.StdExpand

end
