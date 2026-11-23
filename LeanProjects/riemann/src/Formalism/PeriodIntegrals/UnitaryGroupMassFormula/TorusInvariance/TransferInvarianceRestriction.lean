import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.Development
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma glev_mul' {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [mul_assoc], hgU, hhU]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]

theorem transfer_invariance_group_mul : StepGrp := fun _ _ _ _ hg _ hh => glev_mul' hg hh

lemma glev_unit {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := by
    simp only [Glev, UH, Set.mem_setOf_eq] at hg
    exact hg.1
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [mul_assoc], hU, hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  exact ⟨mul_eq_one_comm.mp hl, hl⟩

lemma inv_fix {g : Mx k r} (hu : g⁻¹ * g = 1) {v : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = v) :
    g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

lemma glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := glev_unit hg
  simp only [Glev, UH, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hF⟩ := hg
  refine ⟨?_, fun a ha => ⟨inv_fix hu.2 (hF a ha).1, inv_fix hu.2 (hF a ha).2⟩⟩
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [hu.1, conjTranspose_one, one_mul, mul_one]

lemma H_esI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (esI k r a) = w (eI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · have h1 : Hpk k r (esI k r a) (eI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (esI k r a) j = 0 := by
      simp only [Hpk, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma H_eI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (eI k r a) = w (esI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (esI k r a)]
  · have h1 : Hpk k r (eI k r a) (esI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (eI k r a) j = 0 := by
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma coord {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (c d : Fin (2 * r + k + 1))
    (hcd : ∀ w, (Hpk k r *ᵥ w) c = w d) (hfix : g *ᵥ bvec c = bvec c) (v : Fin (2 * r + k + 1) → ℂ) :
    (g *ᵥ v) d = v d := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hcol : ∀ l, g l c = bvec c l := fun l => by
    rw [← congrFun hfix l]
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  have hrow : ∀ j, (Hpk k r * g) c j = Hpk k r c j := by
    intro j
    have h1 := congrFun (congrFun hU c) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at h1
    rw [← h1, Finset.sum_eq_single c]
    · rw [conjTranspose_apply, hcol]
      simp [bvec]
    · intro l _ hl
      rw [conjTranspose_apply, hcol]
      simp [bvec, Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have key : (Hpk k r *ᵥ (g *ᵥ v)) c = (Hpk k r *ᵥ v) c := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hrow]
  calc (g *ᵥ v) d = (Hpk k r *ᵥ (g *ᵥ v)) c := (hcd _).symm
    _ = (Hpk k r *ᵥ v) c := key
    _ = v d := hcd v

lemma outer {i : Fin (r + 1)} (q : Fin (2 * r + k + 1)) (hq : ∀ c, q ≠ posL k r i c) :
    ∃ a : Fin r, a.val < i.val ∧ (q = eI k r a ∨ q = esI k r a) := by
  have hq' := q.isLt
  have hi := i.isLt
  by_cases h1 : q.val < i.val
  · exact ⟨⟨q.val, by omega⟩, h1, Or.inl (Fin.ext rfl)⟩
  · have h2 : 2 * r + k - i.val < q.val := by
      by_contra h3
      exact hq ⟨q.val - i.val, by unfold mdim; omega⟩ (Fin.ext (by simp only [posL]; omega))
    exact ⟨⟨2 * r + k - q.val, by omega⟩, by simp only; omega, Or.inr (Fin.ext (by simp only [esI]; omega))⟩

lemma glev_fix_outer {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g *ᵥ bvec q = bvec q := by
  obtain ⟨a, ha, hq'⟩ := outer q hq
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  rcases hq' with rfl | rfl
  · exact (hg'.2 a ha).1
  · exact (hg'.2 a ha).2

lemma glev_col {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (p q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g p q = bvec q p := by
  rw [← congrFun (glev_fix_outer hg q hq) p]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

lemma glev_row {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) (v : Fin (2 * r + k + 1) → ℂ) : (g *ᵥ v) q = v q := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  obtain ⟨a, ha, hq'⟩ := outer q hq
  rcases hq' with rfl | rfl
  · exact coord hg'.1 (esI k r a) (eI k r a) (H_esI a) (hg'.2 a ha).2 v
  · exact coord hg'.1 (eI k r a) (esI k r a) (H_eI a) (hg'.2 a ha).1 v

lemma glev_row' {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q p : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g q p = bvec p q := by
  rw [← glev_row hg q hq (bvec p)]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

lemma sum_posL {M : Type*} [AddCommMonoid M] {i : Fin (r + 1)} (F : Fin (2 * r + k + 1) → M)
    (hF : ∀ q, (∀ c, q ≠ posL k r i c) → F q = 0) :
    ∑ q, F q = ∑ c : Fin (mdim k r i), F (posL k r i c) := (Fintype.sum_of_injective (posL k r i) (fun _ _ h => posL_inj h) _ F
    (fun q hq => hF q (fun c hc => hq ⟨c, hc.symm⟩)) (fun _ => rfl)).symm

lemma bvec_posL_outer {i : Fin (r + 1)} (a : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 := ⟨by simp [bvec, Pi.single_apply, hq a, (hq a).symm], by simp [bvec, Pi.single_apply, hq a, (hq a).symm]⟩

lemma n_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} (hz : inWb k r z) {m : Mx k r}
    (hm : m ∈ Nlev k r i) : m *ᵥ fvec k r z i = fvec k r z i := by
  unfold Nlev at hm
  simp only [QuantumDeterminants.Nset, Set.mem_inter_iff, Set.mem_setOf_eq] at hm
  obtain ⟨⟨_, hcol, hmid⟩, hG⟩ := hm
  unfold inWb at hz
  unfold fvec
  split_ifs with hi
  · funext x
    rw [show (m *ᵥ bvec (eI k r ⟨i.val, hi⟩)) x = m x (eI k r ⟨i.val, hi⟩) by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]]
    by_cases hx : i.val ≤ x.val
    · rw [hcol ⟨i.val, hi⟩ x hx]
      simp [bvec, Pi.single_apply]
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      rw [glev_row' hG x (eI k r ⟨i.val, hi⟩) hout]
  · funext x
    by_cases hx : r ≤ x.val
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single x]
      · by_cases hxk : x.val ≤ r + k
        · rw [hmid x x hx hxk hx]
          simp
        · rw [hz x (Or.inr (by omega)), mul_zero]
      · intro j _ hj
        by_cases hjm : r ≤ j.val ∧ j.val ≤ r + k
        · rw [hmid x j hjm.1 hjm.2 hx, if_neg (Ne.symm hj), zero_mul]
        · rw [hz j (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      exact glev_row hG x hout z

lemma h_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {h : Mx k r} (hh : h ∈ UWset k r z) :
    h *ᵥ fvec k r z i = fvec k r z i := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  unfold fvec
  split_ifs with hi
  · exact (hh.2.1 _).1
  · exact hh.2.2

theorem transfer_invariance_smooth : StepS := by
  intro k r z i hz
  have hUW : ∀ h ∈ UWset k r z, h ∈ Glev k r i := by
    intro h hh
    simp only [UWset, Glev, Set.mem_setOf_eq] at hh ⊢
    exact ⟨hh.1, fun a _ => hh.2.1 a⟩
  simp only [Slev, Set.mem_setOf_eq]
  refine ⟨⟨1, ?_, 1, ?_, (mul_one 1).symm⟩, ?_⟩
  · simp [UWset, UH]
  · simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hmG : m ∈ Glev k r i := by
      unfold Nlev at hm
      exact hm.2
    refine ⟨glev_mul' (hUW h hh) hmG, ?_⟩
    rw [← Matrix.mulVec_mulVec, n_fix hz hm, h_fix hh]

lemma herm_uh {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (s *ᵥ v) (s *ᵥ w) = herm (Hpk k r) v w := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [← Matrix.mul_assoc, hs']

lemma herm_col (M : Mx k r) (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ bvec q) w = (star w ᵥ* Hpk k r ᵥ* M) q := by
  unfold herm
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  simp [bvec]

lemma herm_bv (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec q) w = (star w ᵥ* Hpk k r) q := by
  unfold herm
  rw [Matrix.dotProduct_mulVec]
  simp [bvec]

lemma uh_H_inv {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (hu : s * s⁻¹ = 1) :
    Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hs']
    _ = sᴴ * Hpk k r := by rw [mul_assoc (sᴴ * Hpk k r), hu, mul_one]

theorem transfer_invariance_vector : StepVec := by
  intro k r z z' i hz hz'
  have bo : ∀ (a : Fin (mdim k r i)) q, (∀ c, q ≠ posL k r i c) →
      bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 :=
    fun a q hq => bvec_posL_outer a q hq
  have blk_mul : ∀ s t : Mx k r, s ∈ Glev k r i → blk i (s * t) = blk i s * blk i t := by
    intro s t hs
    ext a b
    simp only [blk, Matrix.mul_apply]
    exact sum_posL (fun q => s (posL k r i a) q * t q (posL k r i b)) (fun q hq => by
      show s (posL k r i a) q * t q (posL k r i b) = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])
  have blk_one : blk i (1 : Mx k r) = 1 := by
    ext a b
    simp only [blk, Matrix.one_apply]
    by_cases h : a = b
    · simp [h]
    · rw [if_neg (fun e => h (posL_inj e)), if_neg h]
  have mv_blk : ∀ s ∈ Glev k r i, ∀ v : Fin (2 * r + k + 1) → ℂ,
      (blk i s *ᵥ fun j => v (posL k r i j)) = fun j => (s *ᵥ v) (posL k r i j) := by
    intro s hs v
    funext a
    simp only [blk, Matrix.mulVec, dotProduct]
    exact (sum_posL (fun q => s (posL k r i a) q * v q) (fun q hq => by
      show s (posL k r i a) q * v q = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])).symm
  have vm_blk : ∀ t ∈ Glev k r i, ∀ x : Fin (2 * r + k + 1) → ℂ,
      ((fun j => x (posL k r i j)) ᵥ* blk i t) = fun j => (x ᵥ* t) (posL k r i j) := by
    intro t ht x
    funext b
    simp only [blk, Matrix.vecMul, dotProduct]
    exact (sum_posL (fun q => x q * t q (posL k r i b)) (fun q hq => by
      show x q * t q (posL k r i b) = 0
      rw [glev_row' ht q (posL k r i b) hq, (bo b q hq).2, mul_zero])).symm
  have hS := transfer_invariance_smooth k r z i hz
  have hS' := transfer_invariance_smooth k r z' i hz'
  refine ⟨fun s hs g => ?_, fun s' hs' => ?_⟩
  · obtain ⟨hsG, hsf⟩ := hS.2 s hs
    have hu := glev_unit hsG
    have hsU : s ∈ UH (Hpk k r) := by
      simp only [Glev, Set.mem_setOf_eq] at hsG
      exact hsG.1
    have hinv : s⁻¹ *ᵥ fvec k r z i = fvec k r z i := inv_fix hu.2 hsf
    constructor
    · funext j
      simp only [yv]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    · funext j
      simp only [ybv]
      conv_lhs => rw [← hsf]
      rw [← Matrix.mulVec_mulVec, herm_uh hsU]
  · obtain ⟨hsG, hsf⟩ := hS'.2 s' hs'
    have hu := glev_unit hsG
    have hiG := glev_inv hsG
    have hsU : s' ∈ UH (Hpk k r) := by
      have h0 := hsG
      simp only [Glev, Set.mem_setOf_eq] at h0
      exact h0.1
    refine ⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩
    · rw [← blk_mul _ _ hsG, hu.1, blk_one]
    · rw [← blk_mul _ _ hiG, hu.2, blk_one]
    · unfold xv
      rw [mv_blk _ hsG, hsf]
    · unfold xbv
      simp only [herm_bv]
      rw [vm_blk _ hiG, Matrix.vecMul_vecMul, uh_H_inv hsU hu.1, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec, hsf]
    · unfold yv
      rw [mv_blk _ hsG]
      funext j
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_rev, ← Matrix.mul_assoc, hu.1, Matrix.one_mul]
    · unfold ybv
      simp only [herm_col]
      rw [vm_blk _ hiG]
      simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, hu.1, Matrix.mul_one]

theorem transfer_invariance_restriction : StepRSm := by
  intro E _ _ k r i D f s' hs' hD hf g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s') ⟨glev_mul' hg₀.1 hs', hD g₀ hg₀⟩
  let L : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ s')
  have hL : ∀ x, L x = x * s' := fun _ => rfl
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hgU,
    hF.comp L.contDiff.contDiffOn (fun _ hx => hx), fun x hx hxG => ?_⟩
  have hx' : x * s' ∈ U := by rw [← hL]; exact hx
  show f (x * s') = F (L x)
  rw [hL]
  exact hfF _ hx' (glev_mul' hxG hs')

end Formalism.FourierDecayAlt.Q.TInvW
