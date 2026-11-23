import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section nl

variable {k : ℕ}

def cL {j ρ : ℕ} (a : Fin j → ℂ) : Fin (2 * ρ + k + 1) → Fin j → ℂ :=
  fun v α => if v.val = 2 * ρ + k then a (Fin.rev α) else 0

theorem nL_apply {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) (p q : Fin (2 * (j + ρ) + k + 1)) :
    LevelPointCoordinates.nL k (j + ρ) j (by omega) a p q =
      (if p = q then 1 else 0) +
        (if h : p.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ q.val then a ⟨2 * (j + ρ) + k - q.val, by omega⟩ else 0) -
        (if h : p.val < j ∧ q.val = j then conj (a ⟨p.val, h.1⟩) else 0) := by
  have hS1 : (∑ c : Fin j, if esI k (j + ρ) ⟨j, by omega⟩ = p ∧ esI k (j + ρ) ⟨c.val, by omega⟩ = q then a c else 0) =
      (if h : p.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ q.val then a ⟨2 * (j + ρ) + k - q.val, by omega⟩ else 0) := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨2 * (j + ρ) + k - q.val, by omega⟩]
      · rw [if_pos]
        constructor <;> apply Fin.ext <;> simp [esI] <;> omega
      · intro b _ hb
        rw [if_neg]
        rintro ⟨_, h2⟩
        apply hb
        apply Fin.ext
        have := congrArg Fin.val h2
        simp [esI] at this
        simp
        omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply h
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp [esI] at e1 e2
      have := b.isLt
      omega
  have hS2 : (∑ c : Fin j, if eI k (j + ρ) ⟨c.val, by omega⟩ = p ∧ eI k (j + ρ) ⟨j, by omega⟩ = q then
      conj (a c) else 0) = (if h : p.val < j ∧ q.val = j then conj (a ⟨p.val, h.1⟩) else 0) := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨p.val, h.1⟩]
      · rw [if_pos]
        constructor <;> apply Fin.ext <;> simp [eI] <;> omega
      · intro b _ hb
        rw [if_neg]
        rintro ⟨h1, _⟩
        apply hb
        apply Fin.ext
        have := congrArg Fin.val h1
        simp [eI] at this
        simp
        omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply h
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp [eI] at e1 e2
      have := b.isLt
      omega
  unfold LevelPointCoordinates.nL
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [hS1, hS2]
  ring

theorem skewOf_zero {j : ℕ} : U.skewOf (0 : (G.UT j → ℂ) × (Fin j → ℝ)) = 0 := by
  ext a b
  simp [U.skewOf, G.strictUpper]

theorem hpk_last {ρ : ℕ} (hρ : 1 ≤ ρ) (v : Fin (2 * ρ + k + 1)) :
    Hpk k ρ ⟨2 * ρ + k, by omega⟩ v = if v.val = 0 then 1 else 0 := by
  unfold Hpk
  have hv := v.isLt
  simp only [Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem cL_last {j ρ : ℕ} (a : Fin j → ℂ) (v : Fin (2 * ρ + k + 1)) (α : Fin j) :
    (cL (k := k) (ρ := ρ) a) v α = if v.val = 2 * ρ + k then a (Fin.rev α) else 0 := rfl

theorem cHc_zero {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) :
    (Matrix.of (cL (k := k) (ρ := ρ) a))ᴴ * Hpk k ρ * Matrix.of (cL (k := k) (ρ := ρ) a) = 0 := by
  ext β γ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases hv : v.val = 2 * ρ + k
  · rw [if_pos hv, Finset.sum_eq_single v]
    · have h := hpk_last (k := k) hρ v
      rw [show (⟨2 * ρ + k, by omega⟩ : Fin (2 * ρ + k + 1)) = v from Fin.ext hv.symm] at h
      rw [h, if_neg (show ¬ (v.val = 0) by omega)]
      simp
    · intro u _ hu
      by_cases hu' : u.val = 2 * ρ + k
      · exact absurd (Fin.ext (hu'.trans hv.symm)) hu
      · simp [hu']
    · simp
  · simp [hv]

theorem wcH_apply {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) (α : Fin j) (v : Fin (2 * ρ + k + 1)) :
    (G.wMat j * (Matrix.of (cL (k := k) (ρ := ρ) a))ᴴ * Hpk k ρ) α v = if v.val = 0 then conj (a α) else 0 := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single α.rev]
  · rw [show G.wMat j α α.rev = 1 by simp [G.wMat], one_mul, Matrix.mul_apply,
      Finset.sum_eq_single ⟨2 * ρ + k, by omega⟩]
    · rw [hpk_last hρ, Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, if_pos rfl, Fin.rev_rev]
      split_ifs <;> simp
    · intro u _ hu
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, if_neg (fun h => hu (Fin.ext h))]
      simp
    · simp
  · intro β _ hβ
    rw [show G.wMat j α β = 0 by simp [G.wMat]; exact fun h => hβ h, zero_mul]
  · simp

theorem nL_eq {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) :
    LevelPointCoordinates.nL k (j + ρ) j (by omega) a = U.Rn k j ρ (cL a, 0) := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k j ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k j ρ).surjective q
  rw [nL_apply hρ, Ux3.rn_eq, Ux3.block3_apply]
  simp only [cHc_zero hρ, skewOf_zero, smul_zero, add_zero, Matrix.mul_zero]
  have v1 := @Ux3.block_index_first_val k j ρ
  have v2 := @Ux3.block_index_middle_val k j ρ
  have v3 := @Ux3.block_index_last_val k j ρ
  rcases x with ((α | u) | α) <;> rcases y with ((β | v) | β) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply,
      EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, v1, v2, v3]
  · have := α.isLt; have := β.isLt
    rw [dif_neg (by omega), dif_neg (by omega)]; ring
  · have := α.isLt; have := v.isLt
    rw [wcH_apply hρ, dif_neg (by omega)]
    by_cases hv : v.val = 0
    · rw [dif_pos ⟨α.isLt, by omega⟩, if_pos hv]; simp
    · rw [dif_neg (by omega), if_neg hv]; simp
  · have := α.isLt; have := β.isLt
    rw [dif_neg (by omega), dif_neg (by omega)]; ring
  · have := u.isLt; have := β.isLt
    rw [dif_neg (by omega), dif_neg (by omega)]; ring
  · have := u.isLt; have := v.isLt
    rw [dif_neg (by omega), dif_neg (by omega)]; ring
  · have := u.isLt; have := β.isLt
    rw [cL_last, dif_neg (show ¬(j + u.val < j ∧ j + (2 * ρ + k + 1) + β.val = j) by omega)]
    by_cases hu : u.val = 2 * ρ + k
    · rw [dif_pos (show j + u.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ j + (2 * ρ + k + 1) + β.val by omega),
        if_pos hu]
      have e : (⟨2 * (j + ρ) + k - (j + (2 * ρ + k + 1) + β.val), by omega⟩ : Fin j) = β.rev :=
        Fin.ext (by simp [Fin.rev]; omega)
      rw [e]; ring
    · rw [dif_neg (show ¬(j + u.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ j + (2 * ρ + k + 1) + β.val) by omega),
        if_neg hu]; ring
  · have := α.isLt; have := β.isLt
    rw [dif_neg (by omega), dif_neg (by omega)]; ring
  · have := α.isLt; have := v.isLt
    rw [dif_neg (by omega), dif_neg (by omega)]; ring
  · have := α.isLt; have := β.isLt
    rw [dif_neg (by omega), dif_neg (by omega)]; ring

end nl

section tower

variable {k : ℕ}

theorem nL_castM {r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) :
    LevelPointCoordinates.nL k r j hj a = D.castM (by omega : j + (r - j) = r) (U.Rn k j (r - j) (cL a, 0)) := by
  have key : ∀ (ρ r' : ℕ) (e : j + ρ = r') (hj' : j + 1 ≤ r'),
      LevelPointCoordinates.nL k r' j hj' a = D.castM e (U.Rn k j ρ (cL a, 0)) := by
    intro ρ r' e hj'
    subst e
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    exact nL_eq (by omega) a
  exact key (r - j) r (by omega) hj

theorem nL_mem {r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) : LevelPointCoordinates.nL k r j hj a ∈ Nset k r := by
  rw [nL_castM hj a]
  exact PBH.castM_N _ (LeftFubiniLemmas.rn_nset _)

theorem psi_castM {j ρ r : ℕ} (e : j + ρ = r) (zj : Fin (2 * ρ + k + 1) → ℂ) (z : Fin (2 * r + k + 1) → ℂ)
    (hz : D.castV e (liftVec k j ρ zj) = z) (c : ℂ) (M : B.Mat k (j + ρ)) :
    psi k r z c (D.castM e M) = psi k (j + ρ) (liftVec k j ρ zj) c M := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  subst hz
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem domP_sgs {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {pp : B.SS k r} (hp : Bs.inSS pp) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') : B.sgs pp g ∈ domP k r j Bs.z Bs.z' :=
  ⟨fun l h1 h2 => by rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]; exact hg.1 l h1 h2,
    by unfold Gf; rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]; exact hg.2⟩

theorem minorDomain_mul_unipotent {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') {m : Q.Mx k r} (hm : m ∈ Nset k r) : g * m ∈ domP k r j Bs.z Bs.z' := by
  have hp : Bs.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm m)) :=
    ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, hm⟩
  have hs : B.sgs ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm m)) g = g * m := by
    simp [B.sgs]
  rw [← hs]
  exact domP_sgs Bs j hp hg

theorem domP_N_mul {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') {m : Q.Mx k r} (hm : m ∈ Nset k r) : m * g ∈ domP k r j Bs.z Bs.z' := by
  have hmi : m⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hm
  have hp : Bs.inSS ((Matrix.of.symm 1, Matrix.of.symm m⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) :=
    ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, hmi, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one⟩
  have hu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hm.1
  have hs : B.sgs ((Matrix.of.symm 1, Matrix.of.symm m⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) g = m * g := by
    simp [B.sgs, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [← hs]
  exact domP_sgs Bs j hp hg

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end tower

end Formalism.FourierDecayAlt.P.PBQ
