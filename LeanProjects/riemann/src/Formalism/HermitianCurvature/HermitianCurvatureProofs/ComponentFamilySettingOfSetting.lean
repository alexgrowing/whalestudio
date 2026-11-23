import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.D Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.Dx1.SN
noncomputable section

theorem castM_castM {k a b c : ℕ} (h : a = b) (h' : b = c) (g : B.Mat k a) :
    castM h' (castM h g) = castM (h.trans h') g := by
  subst h h'
  simp [castM]

theorem Rn_zero (k j ρ : ℕ) (hj : j = 0) (x : U.RC k j ρ) : U.Rn k j ρ x = 1 := by
  subst hj
  ext i i'
  obtain ⟨a, rfl⟩ := (U.eB k 0 ρ).surjective i
  obtain ⟨b, rfl⟩ := (U.eB k 0 ρ).surjective i'
  rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b) <;>
    first | exact a.elim0 | exact b.elim0 | skip
  simp [U.Rn, U.blk3, Matrix.reindex_apply, Matrix.one_apply, (U.eB k 0 ρ).injective.eq_iff]

theorem eB_val (k ρ : ℕ) (a : Fin (2 * ρ + k + 1)) : ((U.eB k 0 ρ (Sum.inl (Sum.inr a))) : ℕ) = a.val := by
  simp [U.eB]

theorem mMap_zero (k j ρ : ℕ) (hj : j = 0) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) :
    U.mMap k j ρ Z γ = castM (by omega : ρ = j + ρ) γ := by
  subst hj
  ext i i'
  obtain ⟨a, rfl⟩ := (U.eB k 0 ρ).surjective i
  obtain ⟨b, rfl⟩ := (U.eB k 0 ρ).surjective i'
  rcases a with ((a | a) | a) <;> rcases b with ((b | b) | b) <;>
    first | exact a.elim0 | exact b.elim0 | skip
  simp only [U.mMap, U.blk3, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, castM]
  congr 1 <;> ext <;> simp [eB_val]

theorem psi_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have hell : ell k r z 1 = 0 := by
    unfold ell
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact hz _ (Or.inl (by simp [eI]))
  simp [psi, hell]

theorem psiH_zero (β : ℂ) (σ : Equiv.Perm (Fin 0)) (η : U.XiH 0 0 σ) : U.psiH β σ η = 1 := by
  simp [U.psiH, U.subS, U.supS, U.cornerA, U.cornerB, G.psi]

theorem muXi_univ (k ρ : ℕ) (σ : Equiv.Perm (Fin 0)) : (U.muXi k 0 0 ρ σ) Set.univ = 1 := by
  simp [U.muXi, U.muRC, U.muXiH, ← Set.univ_prod_univ, Measure.prod_prod, Measure.volume_eq_prod, volume_pi,
    Measure.pi_univ]

theorem phi_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (k : ℕ) {p : ℕ} (hp : p = 0) (ρ : ℕ)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (z z' : Fin (2 * (p + 0 + ρ) + k + 1) → ℂ)
    (hz : inWb k (p + 0 + ρ) z) (hz' : inWb k (p + 0 + ρ) z') (F₁ : B.Mat k (p + 0 + ρ) → E)
    (Z : G.Mat 0) (γ : B.Mat k ρ) :
    U.PhiFun k (p := p) (s := 0) ρ σ d z z' F₁ Z γ = F₁ (castM (by omega) γ) := by
  subst hp
  unfold U.PhiFun
  have hint : ∀ ξ : U.Xi k 0 0 ρ σ, U.psiStar k ρ σ z z' ξ • F₁ (U.gaXi k ρ σ d ξ Z γ) =
      F₁ (castM (by omega) γ) := by
    intro ξ
    have h1 : U.gaXi k ρ σ d ξ Z γ = castM (by omega) γ := by
      unfold U.gaXi
      rw [Rn_zero k (0 + 0) ρ rfl, Rn_zero k (0 + 0) ρ rfl, inv_one, one_mul, mul_one,
        mMap_zero k (0 + 0) ρ rfl]
    have h2 : U.psiStar k ρ σ z z' ξ = 1 := by
      unfold U.psiStar
      rw [Rn_zero k (0 + 0) ρ rfl, Rn_zero k (0 + 0) ρ rfl, psi_one _ _ _ hz, psi_one _ _ _ hz', psiH_zero]
      simp
    rw [h1, h2, one_smul]
  simp_rw [hint]
  rw [integral_const]
  simp [Measure.real, muXi_univ]

theorem castV_inWb {k a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) (hz : inWb k a z) :
    inWb k b (castV h z) := by
  subst h
  intro i hi
  exact hz _ (by simpa using hi)

theorem sliceAt_nil {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (F : B.Mat k r → E) (γ : B.Mat k r) :
    sliceAt k r z z' F [] γ = F γ := by
  unfold sliceAt
  split_ifs with hle
  swap
  · exact absurd (Nat.zero_le r) hle
  refine (phi_gen k (p := ptSize []) rfl (r - ptSize []) (ptPerm []) (ptDiag []) _ _ (castV_inWb _ _ hz)
    (castV_inWb _ _ hz') _ _ γ).trans ?_
  simp only [castF]
  congr 1

end
end Formalism.FourierDecayAlt.P.Dx1.SN

open Finset

namespace Formalism.FourierDecayAlt.P.Dx1.LZ
noncomputable section

section alg
variable {X : Type} [AddCommGroup X] [Module ℂ X]

def Z0 (f : Op X) : Prop := ap f 0 = 0

theorem op_ext {f g : Op X} (h : ∀ x, ap f x = ap g x) : f = g := by
  exact funext h

theorem ap_mul (f g : Op X) (x : X) : ap (f * g) x = ap f (ap g x) := rfl
theorem ap_add (f g : Op X) (x : X) : ap (f + g) x = ap f x + ap g x := rfl
theorem ap_zero (x : X) : ap (0 : Op X) x = 0 := rfl
theorem ap_one (x : X) : ap (1 : Op X) x = x := rfl
theorem ap_cOp (c : ℂ) (x : X) : ap (cOp c : Op X) x = c • x := rfl

theorem ap_sum {ι : Type*} (s : Finset ι) (f : ι → Op X) (x : X) :
    ap (∑ i ∈ s, f i) x = ∑ i ∈ s, ap (f i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, ap_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ap_add, ih]

theorem zero_mul' (f : Op X) : (0 : Op X) * f = 0 := by
  exact op_ext fun _ => rfl
theorem mul_zero' {f : Op X} (hf : Z0 f) : f * (0 : Op X) = 0 := by
  exact op_ext fun _ => hf
theorem cOp_zero_mul (f : Op X) : D.cOp 0 * f = 0 := by
  exact op_ext fun x => by rw [ap_mul, ap_cOp, zero_smul, ap_zero]
theorem cOp_one_mul (f : Op X) : D.cOp 1 * f = f := by
  exact op_ext fun x => by rw [ap_mul, ap_cOp, one_smul]
theorem mul_cOp_one (f : Op X) : f * D.cOp 1 = f := by
  exact op_ext fun x => by rw [ap_mul, ap_cOp, one_smul]
theorem mul_cOp_zero {f : Op X} (hf : Z0 f) : f * D.cOp 0 = 0 := by
  exact op_ext fun x => by rw [ap_mul, ap_cOp, zero_smul, ap_zero]; exact hf
theorem cOp_mul_zero (c : ℂ) : D.cOp c * (0 : Op X) = 0 := by
  exact op_ext fun x => by rw [ap_mul, ap_zero, ap_cOp, smul_zero]

theorem zero_operator_zero : Z0 (0 : Op X) := rfl
theorem z0_one : Z0 (1 : Op X) := rfl
theorem z0_cOp (c : ℂ) : Z0 (cOp c : Op X) := by
  unfold Z0
  rw [ap_cOp, smul_zero]
theorem z0_mul {f g : Op X} (hf : Z0 f) (hg : Z0 g) : Z0 (f * g) := by
  unfold Z0 at *
  rw [ap_mul, hg, hf]
theorem z0_sum {ι : Type*} (s : Finset ι) (f : ι → Op X) (h : ∀ i ∈ s, Z0 (f i)) : Z0 (∑ i ∈ s, f i) := by
  unfold Z0
  rw [ap_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi

variable {S : Type} [Fintype S] [DecidableEq S]

def Free (a : S) (M : Wd.SlopeTestRemainingChoices S (Op X)) : Prop := ∀ x y : Wd.Ix S, x a ≠ y a → M x y = 0

theorem eU_apply (a : S) (i j : Fin 2) (x y : Wd.Ix S) :
    (Wd.eU a i j : Wd.SlopeTestRemainingChoices S ℂ) x y = if x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b then 1 else 0 := rfl

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (a : S) : (Wd.e1 : Wd.Ix S) a = 0 := rfl

theorem eq_first_index_iff (u : Wd.Ix S) (b : S) : (u b = 0 ∧ ∀ c, c ≠ b → u c = (Wd.e1 : Wd.Ix S) c) ↔ u = Wd.e1 := by
  constructor
  · rintro ⟨h1, h2⟩
    funext c
    by_cases hc : c = b
    · subst hc
      exact h1
    · exact h2 c hc
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩

theorem unit_matrix_first_column (b : S) (m : Fin 2) (u : Wd.Ix S) :
    (Wd.eU b 0 m : Wd.SlopeTestRemainingChoices S ℂ) u Wd.e1 = if m = 0 ∧ u = Wd.e1 then 1 else 0 := by
  rw [eU_apply]
  have key : (u b = 0 ∧ (Wd.e1 : Wd.Ix S) b = m ∧ ∀ c, c ≠ b → u c = (Wd.e1 : Wd.Ix S) c) ↔ (m = 0 ∧ u = Wd.e1) := by
    rw [← eq_first_index_iff u b, orderedCechToCatCochainsOne_apply_valueAtSubset]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2.symm, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1.symm, h3⟩
  exact if_congr key rfl rfl

theorem identity_matrix_apply (m j : Fin 2) (u y : Wd.Ix S) :
    ((1 : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) m j) u y = if m = j ∧ u = y then 1 else 0 := by
  by_cases h : m = j <;> simp [h, Matrix.one_apply]

theorem residue_matrix_apply (b : S) (D : ℂ) (m j : Fin 2) (u y : Wd.Ix S) :
    (Wd.Rh0 b D : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) m j u y =
      (D - 1)⁻¹ * (D * (if m = j ∧ u = y then 1 else 0) - (Wd.eU b j m : Wd.SlopeTestRemainingChoices S ℂ) u y) := by
  simp only [Wd.Rh0, Wd.P0, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul, identity_matrix_apply]

theorem conj_residue_matrix_apply (b : S) (d : ℂ) (m j : Fin 2) (u y : Wd.Ix S) :
    (Wd.Rht0 b d : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) m j u y =
      (d - 1)⁻¹ * (d * (if m = j ∧ u = y then 1 else 0) - (Wd.eU b m j : Wd.SlopeTestRemainingChoices S ℂ) u y) := by
  simp only [Wd.Rht0, Wd.Q0, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul, identity_matrix_apply]

theorem residue_matrix_column (b : S) {D : ℂ} (hD : D ≠ 1) (m : Fin 2) (u : Wd.Ix S) :
    (Wd.Rh0 b D : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) m 0 u Wd.e1 = if m = 0 ∧ u = Wd.e1 then 1 else 0 := by
  rw [residue_matrix_apply, unit_matrix_first_column]
  by_cases h : m = 0 ∧ u = Wd.e1
  · rw [if_pos h, mul_one]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hD)
  · rw [if_neg h]
    simp

theorem rht0_zero_zero_apply_e1_eq_indicator (b : S) {d : ℂ} (hd : d ≠ 1) (x : Wd.Ix S) :
    (Wd.Rht0 b d : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) 0 0 x Wd.e1 = if x = Wd.e1 then 1 else 0 := by
  rw [conj_residue_matrix_apply, unit_matrix_first_column]
  by_cases hx : x = Wd.e1
  · rw [if_pos ⟨rfl, hx⟩, if_pos hx, mul_one]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hd)
  · rw [if_neg (fun h => hx h.2), if_neg hx]
    simp

theorem conj_residue_off_row (b : S) (d : ℂ) (x u : Wd.Ix S) (hu : u b ≠ 1) :
    (Wd.Rht0 b d : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) 0 1 x u = 0 := by
  rw [conj_residue_matrix_apply, eU_apply]
  simp [hu]

theorem residue_matrix_other_site {a b : S} (hab : a ≠ b) (D : ℂ) (m j : Fin 2) {u y : Wd.Ix S} (h : u a ≠ y a) :
    (Wd.Rh0 b D : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) m j u y = 0 := by
  rw [residue_matrix_apply, eU_apply]
  have h1 : ¬ (m = j ∧ u = y) := fun h' => h (by rw [h'.2])
  have h2 : ¬ (u b = j ∧ y b = m ∧ ∀ c, c ≠ b → u c = y c) := fun h' => h (h'.2.2 a hab)
  rw [if_neg h1, if_neg h2]
  simp

theorem conj_residue_other_site {a b : S} (hab : a ≠ b) (d : ℂ) (m j : Fin 2) {u y : Wd.Ix S} (h : u a ≠ y a) :
    (Wd.Rht0 b d : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) m j u y = 0 := by
  rw [conj_residue_matrix_apply, eU_apply]
  have h1 : ¬ (m = j ∧ u = y) := fun h' => h (by rw [h'.2])
  have h2 : ¬ (u b = m ∧ y b = j ∧ ∀ c, c ≠ b → u c = y c) := fun h' => h (h'.2.2 a hab)
  rw [if_neg h1, if_neg h2]
  simp

variable (QQ : ℂ → Wd.M2 (Op X))

theorem TTop_nil (Y : ℂ) (i j : Fin 2) (x y : Wd.Ix S) :
    TTop (S := S) QQ [] Y i j x y = if x = y then QQ Y i j else 0 := by
  simp only [TTop, Matrix.map_apply, Matrix.diagonal_apply]

theorem TTop_plus (l : Wd.Letter ℂ S) (w : List (Wd.Letter ℂ S)) (Y : ℂ) (hl : l.plus = true)
    (i j : Fin 2) (x y : Wd.Ix S) :
    TTop QQ (l :: w) Y i j x y =
      ∑ m, ∑ u, TTop QQ w Y i m x u * cOp ((Wd.Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) m j u y) := by
  simp only [TTop, hl, if_true, Matrix.mul_apply, Matrix.sum_apply, scal, Matrix.map_apply]

theorem TTop_minus (l : Wd.Letter ℂ S) (w : List (Wd.Letter ℂ S)) (Y : ℂ) (hl : l.plus = false)
    (i j : Fin 2) (x y : Wd.Ix S) :
    TTop QQ (l :: w) Y i j x y =
      ∑ m, ∑ u, cOp ((Wd.Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) i m x u) * TTop QQ w Y m j u y := by
  simp only [TTop, hl, Bool.false_eq_true, if_false, Matrix.mul_apply, Matrix.sum_apply, scal, Matrix.map_apply]

variable {QQ}

theorem z0_TTop (hQ : ∀ Y a b, Z0 (QQ Y a b)) :
    ∀ (w : List (Wd.Letter ℂ S)) (Y : ℂ) (i j : Fin 2) (x y : Wd.Ix S), Z0 (TTop QQ w Y i j x y)
  | [], Y, i, j, x, y => by
    rw [TTop_nil]; split_ifs
    · exact hQ _ _ _
    · exact zero_operator_zero
  | l :: w, Y, i, j, x, y => by
    cases hl : l.plus
    · rw [TTop_minus QQ l w Y hl]
      exact z0_sum _ _ fun m _ => z0_sum _ _ fun u _ => z0_mul (z0_cOp _) (z0_TTop hQ w Y _ _ _ _)
    · rw [TTop_plus QQ l w Y hl]
      exact z0_sum _ _ fun m _ => z0_sum _ _ fun u _ => z0_mul (z0_TTop hQ w Y _ _ _ _) (z0_cOp _)

theorem free_TTop (hQ : ∀ Y a b, Z0 (QQ Y a b)) :
    ∀ (w : List (Wd.Letter ℂ S)) (a : S), a ∉ w.map Wd.Letter.intersection_update_fsHerm_neg_one →
      ∀ (Y : ℂ) (i j : Fin 2), Free a (TTop QQ w Y i j)
  | [], a, _, Y, i, j => fun x y hxy => by
    have hne : x ≠ y := fun e => hxy (by rw [e])
    rw [TTop_nil, if_neg hne]
  | l :: w, a, ha, Y, i, j => fun x y hxy => by
    have ha1 : a ≠ l.intersection_update_fsHerm_neg_one := fun e => ha (by simp [e])
    have ha2 : a ∉ w.map Wd.Letter.intersection_update_fsHerm_neg_one := fun h => ha (List.mem_cons_of_mem _ h)
    cases hl : l.plus
    · rw [TTop_minus QQ l w Y hl]
      refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun u _ => ?_
      by_cases hxu : x a = u a
      · rw [free_TTop hQ w a ha2 Y m j u y (by rw [← hxu]; exact hxy), cOp_mul_zero]
      · rw [conj_residue_other_site ha1 _ _ _ hxu, cOp_zero_mul]
    · rw [TTop_plus QQ l w Y hl]
      refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun u _ => ?_
      by_cases hxu : x a = u a
      · rw [residue_matrix_other_site ha1 _ _ _ (by rw [← hxu]; exact hxy), mul_cOp_zero (z0_TTop hQ w Y _ _ _ _)]
      · rw [free_TTop hQ w a ha2 Y i m x u hxu, zero_mul']

end alg

section alg2
variable {X : Type} [AddCommGroup X] [Module ℂ X] {S : Type} [Fintype S] [DecidableEq S]
  {QQ : ℂ → Wd.M2 (Op X)}

theorem transfer_corner_column (hQ : ∀ Y a b, Z0 (QQ Y a b)) :
    ∀ (w : List (Wd.Letter ℂ S)) (Y : ℂ), (w.map Wd.Letter.intersection_update_fsHerm_neg_one).Nodup → (∀ l ∈ w, Wd.RegL l Y) →
      ∀ x : Wd.Ix S, TTop QQ w Y 0 0 x Wd.e1 = if x = Wd.e1 then QQ Y 0 0 else 0
  | [], Y, _, _, x => by rw [TTop_nil]
  | l :: w, Y, hN, hR, x => by
    rw [List.map_cons, List.nodup_cons] at hN
    have hR' : ∀ l' ∈ w, Wd.RegL l' Y := fun l' h => hR l' (List.mem_cons_of_mem _ h)
    have hl := hR l List.mem_cons_self
    have IH := transfer_corner_column hQ w Y hN.2 hR'
    cases hp : l.plus
    · have hd : l.pt - Y ≠ 1 := by simpa [Wd.RegL, hp] using hl
      rw [TTop_minus QQ l w Y hp, Fin.sum_univ_two]
      have h1 : ∑ u, D.cOp ((Wd.Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) 0 1 x u) * TTop QQ w Y 1 0 u Wd.e1
          = 0 := by
        refine Finset.sum_eq_zero fun u _ => ?_
        by_cases hu : u l.intersection_update_fsHerm_neg_one = 1
        · rw [free_TTop hQ w l.intersection_update_fsHerm_neg_one hN.1 Y 1 0 u Wd.e1 (by rw [hu, orderedCechToCatCochainsOne_apply_valueAtSubset]; decide), cOp_mul_zero]
        · rw [conj_residue_off_row _ _ _ _ hu, cOp_zero_mul]
      rw [h1, add_zero, Finset.sum_eq_single Wd.e1]
      · rw [rht0_zero_zero_apply_e1_eq_indicator _ hd, IH, if_pos rfl]
        split_ifs
        · exact cOp_one_mul _
        · exact cOp_zero_mul _
      · intro u _ hu
        rw [IH, if_neg hu, cOp_mul_zero]
      · simp
    · have hD : Y - l.pt ≠ 1 := by simpa [Wd.RegL, hp] using hl
      rw [TTop_plus QQ l w Y hp, Finset.sum_eq_single 0]
      · rw [Finset.sum_eq_single Wd.e1]
        · rw [residue_matrix_column _ hD, if_pos ⟨rfl, rfl⟩, mul_cOp_one, IH]
        · intro u _ hu
          rw [residue_matrix_column _ hD, if_neg (fun hh => hu hh.2), mul_cOp_zero (z0_TTop hQ w Y _ _ _ _)]
        · simp
      · intro m _ hm
        refine Finset.sum_eq_zero fun u _ => ?_
        rw [residue_matrix_column _ hD, if_neg (fun hh => hm hh.1), mul_cOp_zero (z0_TTop hQ w Y _ _ _ _)]
      · simp

theorem insOp_apply (a : S) (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))) (x y : Wd.Ix S) :
    insOp a M x y = ∑ i, ∑ j, ∑ u, D.cOp ((Wd.eU a i j : Wd.SlopeTestRemainingChoices S ℂ) x u) * M i j u y := by
  simp only [insOp, Matrix.sum_apply, Matrix.mul_apply, Matrix.map_apply]

theorem z0_insOp (a : S) (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))) (hM : ∀ i j x y, Z0 (M i j x y)) (x y : Wd.Ix S) :
    Z0 (insOp a M x y) := by
  rw [insOp_apply]
  exact z0_sum _ _ fun i _ => z0_sum _ _ fun j _ => z0_sum _ _ fun u _ => z0_mul (z0_cOp _) (hM i j u y)

theorem free_insOp {a b : S} (hab : a ≠ b) (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))) (hM : ∀ i j, Free a (M i j)) :
    Free a (insOp b M) := by
  intro x y hxy
  rw [insOp_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : x a = u a
  · rw [hM i j u y (by rwa [← hu]), cOp_mul_zero]
  · rw [eU_apply, if_neg (fun h => hu (h.2.2 a hab)), cOp_zero_mul]

theorem ins_col {a : S} (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))) (hM : ∀ i j, Free a (M i j)) {u : Wd.Ix S}
    (hu : u a = 0) : insOp a M u Wd.e1 = M 0 0 u Wd.e1 := by
  rw [insOp_apply, Fintype.sum_eq_single (0 : Fin 2), Fintype.sum_eq_single (0 : Fin 2), Fintype.sum_eq_single u]
  · rw [eU_apply, if_pos ⟨hu, hu, fun _ _ => rfl⟩, cOp_one_mul]
  · intro v hv
    rw [eU_apply, if_neg ?_, cOp_zero_mul]
    rintro ⟨_, h2, h3⟩
    apply hv
    funext c
    by_cases hc : c = a
    · subst hc
      rw [h2, hu]
    · exact (h3 c hc).symm
  · intro j hj
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v a = j
    · have hne : v a ≠ (Wd.e1 : Wd.Ix S) a := by rw [hv, orderedCechToCatCochainsOne_apply_valueAtSubset]; exact hj
      rw [hM 0 j v Wd.e1 hne, cOp_mul_zero]
    · rw [eU_apply, if_neg (fun h => hv h.2.1), cOp_zero_mul]
  · intro i hi
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun v _ => ?_
    rw [eU_apply, if_neg (fun h => hi (h.1.symm.trans hu)), cOp_zero_mul]

theorem RRop_nil (x y : Wd.Ix S) : RRop (S := S) QQ [] x y = if x = y then 1 else 0 := by
  simp only [RRop, Matrix.one_apply]

theorem RRop_cons (l : Wd.Letter ℂ S) (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S) :
    RRop QQ (l :: w) x y = ∑ u, RRop QQ w x u *
      insOp l.intersection_update_fsHerm_neg_one (if l.plus then TTop QQ w l.pt else (TTop QQ w l.pt).transpose) u y := by
  simp only [RRop, Matrix.mul_apply]

theorem z0_RRop (hQ : ∀ Y a b, Z0 (QQ Y a b)) :
    ∀ (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S), Z0 (RRop QQ w x y)
  | [], x, y => by rw [RRop_nil]; split_ifs; exact z0_one; exact zero_operator_zero
  | l :: w, x, y => by
    rw [RRop_cons]
    refine z0_sum _ _ fun u _ => z0_mul (z0_RRop hQ w _ _) (z0_insOp _ _ ?_ _ _)
    intro i j x y
    split_ifs
    · exact z0_TTop hQ _ _ _ _ _ _
    · exact z0_TTop hQ _ _ _ _ _ _

theorem free_RRop (hQ : ∀ Y a b, Z0 (QQ Y a b)) :
    ∀ (w : List (Wd.Letter ℂ S)) (a : S), a ∉ w.map Wd.Letter.intersection_update_fsHerm_neg_one → Free a (RRop QQ w)
  | [], a, _ => fun x y hxy => by
    have hne : x ≠ y := fun e => hxy (by rw [e])
    rw [RRop_nil, if_neg hne]
  | l :: w, a, ha => fun x y hxy => by
    have ha1 : a ≠ l.intersection_update_fsHerm_neg_one := fun e => ha (by simp [e])
    have ha2 : a ∉ w.map Wd.Letter.intersection_update_fsHerm_neg_one := fun h => ha (List.mem_cons_of_mem _ h)
    rw [RRop_cons]
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases hxu : x a = u a
    · have hF : ∀ i j, Free a ((if l.plus then TTop QQ w l.pt else (TTop QQ w l.pt).transpose) i j) := by
        intro i j
        split_ifs
        · exact free_TTop hQ w a ha2 _ _ _
        · exact free_TTop hQ w a ha2 _ _ _
      rw [free_insOp ha1 _ hF u y (by rw [← hxu]; exact hxy), mul_zero' (z0_RRop hQ w _ _)]
    · rw [free_RRop hQ w a ha2 x u hxu, zero_mul']

theorem RRop_step (hQ : ∀ Y a b, Z0 (QQ Y a b)) (l : Wd.Letter ℂ S) (w : List (Wd.Letter ℂ S))
    (hN : ((l :: w).map Wd.Letter.intersection_update_fsHerm_neg_one).Nodup) (hR : ∀ l' ∈ w, Wd.RegL l' l.pt) :
    RRop QQ (l :: w) Wd.e1 Wd.e1 = RRop QQ w Wd.e1 Wd.e1 * QQ l.pt 0 0 := by
  rw [List.map_cons, List.nodup_cons] at hN
  obtain ⟨hlw, hN'⟩ := hN
  have hF : ∀ i j, Free l.intersection_update_fsHerm_neg_one ((if l.plus then TTop QQ w l.pt else (TTop QQ w l.pt).transpose) i j) := by
    intro i j
    split_ifs
    · exact free_TTop hQ w _ hlw _ i j
    · exact free_TTop hQ w _ hlw _ j i
  have h00 : (if l.plus then TTop QQ w l.pt else (TTop QQ w l.pt).transpose) 0 0 = TTop QQ w l.pt 0 0 := by
    split_ifs <;> rfl
  rw [RRop_cons, Fintype.sum_eq_single Wd.e1]
  · rw [ins_col _ hF (orderedCechToCatCochainsOne_apply_valueAtSubset _), h00, transfer_corner_column hQ w l.pt hN' hR Wd.e1, if_pos rfl]
  · intro u hu
    by_cases hus : u l.intersection_update_fsHerm_neg_one = 0
    · rw [ins_col _ hF hus, h00, transfer_corner_column hQ w l.pt hN' hR u, if_neg hu, mul_zero' (z0_RRop hQ w Wd.e1 u)]
    · rw [free_RRop hQ w l.intersection_update_fsHerm_neg_one hlw Wd.e1 u (by rw [orderedCechToCatCochainsOne_apply_valueAtSubset]; exact Ne.symm hus), zero_mul']

theorem residue_operator_at_first (hQ : ∀ Y a b, Z0 (QQ Y a b)) :
    ∀ (w : List (Wd.Letter ℂ S)), Wd.Good w → ∀ F : X,
      ap (RRop QQ w Wd.e1 Wd.e1) F = w.reverse.foldr (fun l H => ap (QQ l.pt 0 0) H) F
  | [], _, F => by rw [RRop_nil, if_pos rfl]; rfl
  | l :: w, hG, F => by
    obtain ⟨hN, hS, hP⟩ := hG
    have hN' := hN
    rw [List.map_cons, List.nodup_cons] at hN'
    rw [List.pairwise_cons] at hP
    have hGw : Wd.Good w := ⟨hN'.2, fun l' h => hS l' (List.mem_cons_of_mem _ h), hP.2⟩
    rw [RRop_step hQ l w hN hP.1, ap_mul, residue_operator_at_first hQ w hGw]
    simp [List.reverse_cons, List.foldr_append]

end alg2

section lev0
open Formalism.FourierDecayAlt.Q

theorem aaop_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (hm : m ≤ r) (h0 : m = 0)
    (u : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) : C3.AAop k r m hm u f = f := by
  subst h0
  funext g
  simp [C3.AAop, qminorOp, Matrix.det_isEmpty]
  intro h
  exact (h fun a _ _ => a.elim0).elim

theorem aavop_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (hm : m ≤ r) (h0 : m = 0)
    (u : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) : C3.AAvop k r m hm u f = f := by
  subst h0
  funext g
  simp [C3.AAvop, qminorOp, Matrix.det_isEmpty]
  intro h
  exact (h fun a _ _ => a.elim0).elim

theorem dmin_zero (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (h : 0 < r + 2) : Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem vLet_00 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hj : 0 ≤ r) (l : C.Letter) (f : B.Mat k r → E) :
    vLet k r z z' 0 hj l 0 f = f := by
  funext g
  unfold vLet
  rw [if_neg (by simp)]
  split_ifs
  · rw [dmin_zero, inv_one, one_smul, aaop_zero _ _ _ _ (by simp)]
  · rw [dmin_zero, map_one, inv_one, one_smul, aavop_zero _ _ _ _ (by simp)]

theorem vLet_01 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hj : 0 ≤ r) (l : C.Letter) (f : B.Mat k r → E) :
    vLet k r z z' 0 hj l 1 f = 0 := by
  funext g
  unfold vLet
  rw [if_pos ⟨rfl, rfl⟩]
  rfl

theorem uwG_zero (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (hj : 0 ≤ r) :
    ∀ (w : List C.Letter) (a : Wd.Ix (Fin w.length)), uwG k r z z' F 0 hj w a = if a = Wd.e1 then F else 0
  | [], a => by
    rw [if_pos (funext fun i => i.elim0)]
    rfl
  | l :: w, a => by
    have IH := uwG_zero k r z z' F hj w (fun i => a i.succ)
    show vLet k r z z' 0 hj l (a 0) (uwG k r z z' F 0 hj w fun i => a i.succ) = _
    rcases Fin.exists_fin_two.1 ⟨a 0, rfl⟩ with h0 | h0
    · rw [h0, vLet_00, IH]
      have hiff : ((fun i : Fin w.length => a i.succ) = Wd.e1) ↔ a = Wd.e1 := by
        constructor
        · intro h
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact h0
          · exact congrFun h j
        · intro h
          funext i
          rw [h]
          rfl
      by_cases ha : a = Wd.e1
      · rw [if_pos (hiff.2 ha), if_pos ha]
      · rw [if_neg (fun h => ha (hiff.1 h)), if_neg ha]
    · rw [h0, vLet_01, if_neg]
      intro ha
      rw [ha, orderedCechToCatCochainsOne_apply_valueAtSubset] at h0
      exact absurd h0 (by decide)

end lev0

section analysis
open Formalism.FourierDecayAlt.Q

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smooth_of_ck {F : Mx k r → E} (hF : B.CkOn ⊤ (B.GV k r) F) : SmoothLev k r 0 Set.univ F := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hF g₀ hg₀.1.1
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => he g hg hgG.1⟩

theorem glev0 {g : Mx k r} (hg : g ∈ B.GV k r) : g ∈ Glev k r 0 ∩ Set.univ :=
  ⟨⟨hg, fun a ha => absurd ha (by simp)⟩, trivial⟩

def Tc (k r : ℕ) (s Y : ℂ) (f : Mx k r → E) : Mx k r → E := s • CV k r Y f

theorem good_CV (Y : ℂ) : Qx2.Good k r 0 Set.univ (fun f : Mx k r → E => CV k r Y f) :=
  Qx2.good_qminor (E := E) (i := 0) (D := Set.univ) isOpen_univ id id (uC k r 0 Y)

theorem good_Tc (s Y : ℂ) : Qx2.Good k r 0 Set.univ (Tc (E := E) k r s Y) :=
  (good_CV (k := k) (r := r) (E := E) Y).smul s

theorem good_smul_in {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r 0 Set.univ T) {f : Mx k r → E}
    (hf : SmoothLev k r 0 Set.univ f) (c : ℂ) {x : Mx k r} (hx : x ∈ Glev k r 0 ∩ Set.univ) :
    T (fun y => c • f y) x = c • T f x := by
  have h := hT.lin (fun _ => 0) f c Qx2.smooth_zero hf x hx
  simp only [zero_add] at h
  rw [h, hT.map_zero hx, zero_add]

theorem comm_Tc (s Y Y' : ℂ) {f : Mx k r → E} (hf : SmoothLev k r 0 Set.univ f) {g : Mx k r}
    (hg : g ∈ Glev k r 0 ∩ Set.univ) : Tc k r s Y (Tc k r s Y' f) g = Tc k r s Y' (Tc k r s Y f) g := by
  have h1 : CV k r Y (Tc k r s Y' f) g = s • CV k r Y (CV k r Y' f) g :=
    good_smul_in (good_CV Y) ((good_CV Y').sm f hf) s hg
  have h2 : CV k r Y' (Tc k r s Y f) g = s • CV k r Y' (CV k r Y f) g :=
    good_smul_in (good_CV Y') ((good_CV Y).sm f hf) s hg
  have hc := Formalism.FourierDecayAlt.P.capelli_commutation E k r 0 Set.univ f isOpen_univ hf g hg (uC k r 0 Y) (uC k r 0 Y')
  show s • CV k r Y (Tc k r s Y' f) g = s • CV k r Y' (Tc k r s Y f) g
  rw [h1, h2]
  unfold CV
  rw [hc]

def foldT (k r : ℕ) (s : ℂ) (L : List C.Letter) (f : Mx k r → E) : Mx k r → E :=
  L.foldr (fun a H => Tc k r s (a.2 : ℂ) H) f

theorem smooth_foldT (s : ℂ) : ∀ (L : List C.Letter) {f : Mx k r → E}, SmoothLev k r 0 Set.univ f →
    SmoothLev k r 0 Set.univ (foldT k r s L f)
  | [], _, hf => hf
  | a :: L, _, hf => (good_Tc s (a.2 : ℂ)).sm _ (smooth_foldT s L hf)

theorem foldT_comm (s : ℂ) (a : C.Letter) : ∀ (L : List C.Letter) {f : Mx k r → E},
    SmoothLev k r 0 Set.univ f → ∀ g ∈ Glev k r 0 ∩ Set.univ,
      foldT k r s L (Tc k r s (a.2 : ℂ) f) g = Tc k r s (a.2 : ℂ) (foldT k r s L f) g
  | [], _, _, _, _ => rfl
  | b :: L, f, hf, g, hg => by
    show Tc k r s (b.2 : ℂ) (foldT k r s L (Tc k r s (a.2 : ℂ) f)) g =
      Tc k r s (a.2 : ℂ) (Tc k r s (b.2 : ℂ) (foldT k r s L f)) g
    rw [(good_Tc s (b.2 : ℂ)).loc _ _ (foldT_comm s a L hf) g hg]
    exact comm_Tc s _ _ (smooth_foldT s L hf) hg

theorem foldT_rev (s : ℂ) : ∀ (L : List C.Letter) {f : Mx k r → E},
    SmoothLev k r 0 Set.univ f → ∀ g ∈ Glev k r 0 ∩ Set.univ, foldT k r s L.reverse f g = foldT k r s L f g
  | [], _, _, _, _ => rfl
  | a :: L, f, hf, g, hg => by
    have e : foldT k r s (a :: L).reverse f = foldT k r s L.reverse (Tc k r s (a.2 : ℂ) f) := by
      simp [foldT, List.reverse_cons, List.foldr_append]
    rw [e, foldT_rev s L ((good_Tc s (a.2 : ℂ)).sm f hf) g hg, foldT_comm s a L hf g hg]
    rfl

end analysis

section betaC
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congr_left (D : B.RealPlaceData k r Wp Wq) {H₁ H₂ F' : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k r, H₁ g = H₂ g) : B.beta D H₁ F' = B.beta D H₂ F' := by
  unfold B.beta betaBig
  apply integral_congr_ae
  filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with hq | hq
  · have hg := Formalism.FourierDecayAlt.P.B7.gq_mem D hq
    have e := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := H₁) (F' := H₂) (a := 1)
      (fun g hg => by rw [h g hg, one_smul]) hg
    rw [one_smul] at e
    unfold B.gq at e
    rw [e]
  · simp [hq]

theorem beta_zero_right (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.beta D F' 0 = 0 := by
  have h : ∀ g, B.hsVec (B.JF D 0 g) = 0 := by
    intro g
    have : B.JF D 0 g = 0 := by simp [B.JF, besselJ]
    rw [this]; ext i; simp [B.hsVec]
  simp [B.beta, betaBig, h]

end betaC

section tl
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eab_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    EabH H a b (0 : Matrix (Fin n) (Fin n) ℂ → E) = 0 := by
  funext g; simp [EabH, RdV]

theorem qminor_zero {n t : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin t → Fin n) (u : ℂ) :
    qminorOp (EabH H) a b u (0 : Matrix (Fin n) (Fin n) ℂ → E) = 0 := by
  unfold qminorOp
  apply Finset.sum_eq_zero
  intro σ _
  have : ∀ L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)), (∀ T ∈ L, T 0 = 0) →
      L.foldr (fun T h => T h) 0 = 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons T L ih =>
      simp only [List.foldr_cons]
      rw [ih (fun T' h => hL T' (List.mem_cons_of_mem _ h))]
      exact hL T (by simp)
  rw [this, smul_zero]
  intro T hT
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  unfold Formalism.QuantumDeterminants.Top
  funext g
  simp [eab_zero]

theorem tL_zero (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) (a b : Fin 2) :
    Q.tL k r z z' i Y a b (0 : Q.Mx k r → E) = 0 := by
  fin_cases a <;> fin_cases b
  · exact qminor_zero _ _ _ _
  all_goals (funext g; simp [Q.tL, Q.chatL, Q.chat2L, qminor_zero])

end tl

section main
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem z0_QQlev (T : LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (Y : ℂ) (a b : Fin 2) :
    Z0 (QQlev T s j Y a b) := by
  show s • Q.tL k (r - j) (T.bs j).z (T.bs j).z' 0 Y a b 0 = 0
  rw [tL_zero, smul_zero]

theorem formLev_delta (T : LevTower k r Wp Wq) (s : ℂ) (h0 : 0 < r + 1) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k (r - ((⟨0, h0⟩ : Fin (r + 1)) : ℕ)) → (Wq →L[ℂ] Wp))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ a, x a = if a = Wd.e1 then F else 0) :
    formLev T s ⟨0, h0⟩ w x x = B.beta T.base (ap (RRlev T s ⟨0, h0⟩ w Wd.e1 Wd.e1) F) F := by
  unfold formLev
  rw [Finset.sum_eq_single Wd.e1]
  · have hact : actOp (RRlev T s ⟨0, h0⟩ w) x Wd.e1 = ap (RRlev T s ⟨0, h0⟩ w Wd.e1 Wd.e1) F := by
      unfold actOp
      rw [Finset.sum_eq_single Wd.e1]
      · rw [hx, if_pos rfl]
      · intro b _ hb
        rw [hx, if_neg hb]
        exact z0_RRop (fun Y a b => z0_QQlev T s _ Y a b) _ _ _
      · simp
    rw [hact, hx, if_pos rfl]
    rfl
  · intro a _ ha
    rw [hx a, if_neg ha]
    exact beta_zero_right _ _
  · simp

theorem foldr_positioned {X : Type} (G : ℂ → X → X) (w : List C.Letter) (F : X) :
    (positionted w).reverse.foldr (fun l H => G l.pt H) F = w.reverse.foldr (fun a H => G (a.2 : ℂ) H) F := by
  have e : (positionted w).map (fun l => l.pt) = w.map (fun a => (a.2 : ℂ)) := by
    simp only [positionted, List.map_ofFn]
    apply List.ext_getElem <;> simp
  have h1 : ∀ L : List (Wd.Letter ℂ (Fin w.length)),
      L.reverse.foldr (fun l H => G l.pt H) F = (L.map (fun l => l.pt)).reverse.foldr G F := by
    intro L
    simp [List.foldl_map]
  have h2 : w.reverse.foldr (fun a H => G (a.2 : ℂ) H) F = (w.map (fun a => (a.2 : ℂ))).reverse.foldr G F := by
    simp [List.foldl_map]
  rw [h1, h2, e]

end main

theorem levelZero_of (hSN : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' → ∀ (F : B.Mat k r → E) (γ : B.Mat k r),
      sliceAt k r z z' F [] γ = F γ) : LevelZero := by
  intro k r Wp Wq _ _ _ _ _ _ T s ν' m₀ top F w hF hG
  have h0 : 0 < r + 1 := Nat.succ_pos r
  have hloc : IsLocPt ([] : C.LPt) 0 := ⟨by simp, rfl⟩
  unfold RRplace
  rw [dif_pos ⟨hloc, hloc⟩, dif_pos (Nat.zero_le r)]
  refine (formLev_delta T s h0 w _ F ?_).trans ?_
  · intro a
    funext γ
    show sliceAt k r T.base.z T.base.z' (uwG k r T.base.z T.base.z' F 0 (Nat.zero_le r) w a) [] (castM _ γ) =
      (if a = Wd.e1 then F else 0) γ
    refine (hSN _ k r _ _ T.base.z_mem T.base.z'_mem _ _).trans ?_
    rw [uwG_zero]
    split_ifs <;> rfl
  · unfold RRlev
    rw [residue_operator_at_first (fun Y a b => z0_QQlev T s ⟨0, h0⟩ Y a b) (positionted w) hG F]
    have e : (positionted w).reverse.foldr (fun l H => ap (QQlev T s ⟨0, h0⟩ l.pt 0 0) H) F = foldT k r s w.reverse F := by
      rw [foldr_positioned (fun Y H => ap (QQlev T s ⟨0, h0⟩ Y 0 0) H)]
      rfl
    rw [e]
    unfold C7.principalHermitianLattice
    apply beta_congr_left
    intro g hg
    exact foldT_rev s w (smooth_of_ck hF) g (glev0 hg)

theorem levelZero : LevelZero := by
  exact levelZero_of fun E _ _ _ k r z z' hz hz' F γ => SN.sliceAt_nil (E := E) k r z z' hz hz' F γ

end
end Formalism.FourierDecayAlt.P.Dx1.LZ

end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.D Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Finset NumberField
open scoped ComplexConjugate Matrix ComplexOrder

namespace Formalism.FourierDecayAlt.P.Dx1
noncomputable section
open Classical

theorem orbJOfData : OrbJOfData := by
  intro k r Wp Wq _ _ _ _ _ D γ O F h
  unfold orbJ
  rw [dif_pos h]
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h.choose_spec
  exact (O.weil F _ h1 h2 h3 h4).symm

theorem orbDataOfParts : OrbDataOfParts := by
  intro hH hI k r Wp Wq _ _ _ _ _ D γ w d hrel hd hZ
  have haar := hH k r Wp Wq D γ w d hrel.1 hd hZ
  refine ⟨⟨muR D γ w, haar, orbJ D γ (muR D γ w), ?_⟩, rfl, fun F _ => rfl⟩
  intro F θ h1 h2 h3 h4
  have h : ∃ θ, IsNormCut D γ (muR D γ w) θ ∧ Integrable (fun p => θ p • orbIntegrand D γ F p) D.μSS :=
    ⟨θ, ⟨h1, h2, h3⟩, h4⟩
  unfold orbJ
  rw [dif_pos h]
  exact hI k r Wp Wq D γ _ hrel haar F θ _ ⟨h1, h2, h3⟩ h.choose_spec.1 h4 h.choose_spec.2

theorem thmPPosOfForms : ThmPPosOfForms := by
  intro E _ _ _ Wp Wq _ _ _ _ S h v ε hε i hi w Y
  have h1 := h v ε hε i hi w Y
  unfold TB.PSDOn at *
  let d : Y → ℂ := fun x => ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G x) : ℝ) : ℂ)
  have h2 := h1.conjTranspose_mul_mul_same (Matrix.diagonal d)
  convert h2 using 1
  ext x y
  simp [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, d, C.HidaSetting.gramLoc]
  ring

theorem ptGSpec : PtGSpec := by
  intro k r z z' p γ _ hZ
  unfold ptG Gf Dmin
  rw [hZ]
  rfl

theorem ptSize_cons (s : ℕ) (t : ℂ) (rest : C.LPt) : ptSize ((s, t) :: rest) = s + ptSize rest := by
  simp only [ptSize, List.map_cons, List.sum_cons]

theorem pp_lt {s a : ℕ} {t : ℂ} {rest : C.LPt} (h : a < s) : ptPartner ((s, t) :: rest) a = s - 1 - a := by
  simp [ptPartner, h]

theorem pp_ge {s a : ℕ} {t : ℂ} {rest : C.LPt} (h : ¬ a < s) :
    ptPartner ((s, t) :: rest) a = s + ptPartner rest (a - s) := by
  simp [ptPartner, h]

theorem partner_spec : ∀ (p : C.LPt) (a : ℕ), a < ptSize p →
    ptPartner p a < ptSize p ∧ ptPartner p (ptPartner p a) = a := by
  intro p
  induction p with
  | nil =>
    intro a ha
    simp [ptSize] at ha
  | cons b rest ih =>
    obtain ⟨s, t⟩ := b
    intro a ha
    rw [ptSize_cons] at ha
    by_cases h : a < s
    · rw [pp_lt h, ptSize_cons]
      refine ⟨by omega, ?_⟩
      rw [pp_lt (by omega)]
      omega
    · rw [pp_ge h, ptSize_cons]
      obtain ⟨h1, h2⟩ := ih (a - s) (by omega)
      refine ⟨by omega, ?_⟩
      rw [pp_ge (by omega), Nat.add_sub_cancel_left, h2]
      omega

private theorem hasDerivAt_exp_smul_apply_zero : ∀ (p : C.LPt) (i a : ℕ), a < ptSize p →
    ptEntry p i a = if i = ptPartner p a then ptScal p a else 0 := by
  intro p
  induction p with
  | nil =>
    intro i a ha
    simp [ptSize] at ha
  | cons b rest ih =>
    obtain ⟨s, t⟩ := b
    intro i a ha
    rw [ptSize_cons] at ha
    by_cases has : a < s
    · rw [pp_lt has]
      simp only [ptEntry, ptScal, if_pos has]
      by_cases his : i < s
      · rw [if_pos ⟨his, has⟩]
        by_cases he : i + a + 1 = s
        · rw [if_pos he, if_pos (by omega)]
        · rw [if_neg he, if_neg (by omega)]
      · rw [if_neg (fun h => his h.1), if_neg (fun h => by omega), if_neg (by omega)]
    · rw [pp_ge has]
      simp only [ptEntry, ptScal, if_neg has]
      by_cases his : i < s
      · rw [if_neg (fun h => has h.2), if_neg (fun h => by omega), if_neg (by omega)]
      · rw [if_neg (fun h => his h.1), if_pos ⟨by omega, by omega⟩, ih (i - s) (a - s) (by omega)]
        by_cases he : i - s = ptPartner rest (a - s)
        · rw [if_pos he, if_pos (by omega)]
        · rw [if_neg he, if_neg (by omega)]

theorem entry_spec : ∀ (p : C.LPt) (i a : ℕ), i < ptSize p → a < ptSize p →
    ptEntry p i a = if i = ptPartner p a then ptScal p a else 0 := by
  exact fun p i a _ ha => hasDerivAt_exp_smul_apply_zero p i a ha

theorem partnerF_invol (p : C.LPt) : Function.Involutive (ptPartnerF p) := by
  intro a
  have h1 := partner_spec p a a.2
  have e1 : ptPartnerF p a = ⟨ptPartner p a, h1.1⟩ := by simp [ptPartnerF, h1.1]
  rw [e1]
  have h2 := partner_spec p (ptPartner p a) h1.1
  apply Fin.ext
  simp [ptPartnerF, h2.1, h1.2]

theorem ptPerm_apply (p : C.LPt) (a : Fin (ptSize p)) : ptPerm p a = ptPartnerF p a := by
  rw [ptPerm, dif_pos (partnerF_invol p).bijective]
  rfl

theorem ptPerm_val (p : C.LPt) (a : Fin (ptSize p)) : ((ptPerm p a : Fin (ptSize p)) : ℕ) = ptPartner p a := by
  rw [ptPerm_apply]
  simp [ptPartnerF, (partner_spec p a a.2).1]

theorem ptPerm_invol (p : C.LPt) (a : Fin (ptSize p)) : ptPerm p (ptPerm p a) = a := by
  rw [ptPerm_apply, ptPerm_apply]
  exact partnerF_invol p a

theorem ptMat_monoP (p : C.LPt) : ptMat p = C2.monoP (ptPerm p) (ptDiag p) := by
  ext i a
  simp only [ptMat, ptMatN, C2.monoP, Matrix.of_apply, ptDiag]
  rw [entry_spec p i a i.2 a.2]
  by_cases h : i = ptPerm p a
  · rw [if_pos h, if_pos (by rw [h, ptPerm_val])]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by rw [h', ptPerm_val])))]

theorem monomialMatrix_eq_hMat {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hσ : ∀ a, σ (σ a) = a) :
    C2.monoP σ d = U.hMat σ d := by
  ext i a
  simp only [C2.monoP, U.hMat, U.wP, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases h : i = σ a
  · rw [if_pos h, if_pos (by rw [h, hσ]), one_mul]
  · rw [if_neg h, if_neg (fun h' => h (by rw [← h', hσ])), zero_mul]

theorem d_ptPermSpec : PtPermSpec := by
  intro p i _
  exact ⟨ptPerm_val p, ptMat_monoP p, by rw [ptMat_monoP, monomialMatrix_eq_hMat _ _ (ptPerm_invol p)]⟩

theorem d_goodOfAdm : GoodOfAdm := by
  intro E _ _ _ Wp Wq _ _ _ _ S w v
  have hA := w.2.1.2 v
  refine ⟨?_, ?_, ?_⟩
  · simp only [positionted, List.map_ofFn]
    rw [List.nodup_ofFn]
    intro a b h
    simpa using h
  · intro l hl
    rw [positionted, List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    simp [Complex.conj_ofReal]
  · rw [positionted, List.pairwise_ofFn]
    intro i j hij
    have h0 := hA i j i.isLt j.isLt (Fin.val_ne_of_ne (ne_of_lt hij)) 0 (by norm_num) (by norm_num)
    have h1 := hA j i j.isLt i.isLt (Fin.val_ne_of_ne (ne_of_lt hij).symm) 0 (by norm_num) (by norm_num)
    simp only [Int.cast_zero, add_zero] at h0 h1
    unfold Wd.RegL
    split_ifs
    · intro h
      have h' : ((w.1 v).get i).2 - ((w.1 v).get j).2 = 1 := by
        have := h
        simp only at this
        exact_mod_cast this
      simp only [List.get_eq_getElem] at h'
      rw [h'] at h0
      norm_num at h0
    · intro h
      have h' : ((w.1 v).get j).2 - ((w.1 v).get i).2 = 1 := by
        have := h
        simp only at this
        exact_mod_cast this
      simp only [List.get_eq_getElem] at h'
      rw [h'] at h1
      norm_num at h1

theorem d_lemmaEOfRR0 : LemmaEOfRR0 := by
  intro hLZ hGood E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ jv hB hU hL w v
  have hpd := (hB.2 v).1
  set Γ := GamLev S.G.k S.G.r (kapG S.g (S6.rd E)) (deG S.g (S6.rd E)) 0 with hΓ
  have key := (hL w v).const_mul (((1 / Γ : ℝ)) : ℂ)
  have hval : (((1 / Γ : ℝ)) : ℂ) * ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ) =
      ((S.sizeAt v (w.1 v) * (jv v / Γ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hpd]
  simp only [componentFamilySetting_ofSetting, bSt, toStd, List.map_nil, List.prod_nil]
  rw [hLZ _ _ _ _ _ _ _ _ _ _ _ (hU v ε hε) (hGood _ _ _ S w v)]
  push_cast
  ring

section modwd

variable {X : Type} [AddCommGroup X] [Module ℂ X] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
  {A : Type} [Ring A] [Algebra ℂ A]
  (K : Submodule ℂ X) (res : X →ₗ[ℂ] Y) (φ : A →ₐ[ℂ] Module.End ℂ Y)

def Corr (f : Op X) (a : A) : Prop := ∀ x ∈ K, ap f x ∈ K ∧ res (ap f x) = φ a (res x)

theorem corr_zero : Corr K res φ (0 : Op X) (0 : A) := by
  intro x _
  refine ⟨?_, ?_⟩
  · rw [LZ.ap_zero]
    exact K.zero_mem
  · rw [LZ.ap_zero, map_zero, map_zero, LinearMap.zero_apply]

theorem corr_add {f g : Op X} {a b : A} (hf : Corr K res φ f a) (hg : Corr K res φ g b) :
    Corr K res φ (f + g) (a + b) := by
  intro x hx
  obtain ⟨f1, f2⟩ := hf x hx
  obtain ⟨g1, g2⟩ := hg x hx
  refine ⟨?_, ?_⟩
  · rw [LZ.ap_add]
    exact K.add_mem f1 g1
  · rw [LZ.ap_add, map_add, f2, g2, map_add, LinearMap.add_apply]

theorem corr_sum {ι : Type} (s : Finset ι) (f : ι → Op X) (a : ι → A)
    (h : ∀ i ∈ s, Corr K res φ (f i) (a i)) : Corr K res φ (∑ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, Finset.sum_empty]
    exact corr_zero K res φ
  · intro i s hi ih h
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact corr_add K res φ (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem corr_mul {f g : Op X} {a b : A} (hf : Corr K res φ f a) (hg : Corr K res φ g b) :
    Corr K res φ (f * g) (a * b) := by
  intro x hx
  obtain ⟨g1, g2⟩ := hg x hx
  obtain ⟨f1, f2⟩ := hf _ g1
  refine ⟨?_, ?_⟩
  · rw [LZ.ap_mul]
    exact f1
  · rw [LZ.ap_mul, f2, g2, map_mul]
    rfl

theorem corr_one : Corr K res φ (1 : Op X) (1 : A) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [LZ.ap_one]
    exact hx
  · rw [LZ.ap_one, map_one]
    rfl

theorem corr_c (c : ℂ) : Corr K res φ (cOp c : Op X) (algebraMap ℂ A c) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [LZ.ap_cOp]
    exact K.smul_mem c hx
  · rw [LZ.ap_cOp, map_smul, AlgHom.commutes, Module.algebraMap_end_apply]

def CorrA {ι : Type} (M : Matrix ι ι (Op X)) (N : Matrix ι ι A) : Prop :=
  ∀ x y, Corr K res φ (M x y) (N x y)

theorem corrA_mul {ι : Type} [Fintype ι] {M M' : Matrix ι ι (Op X)} {N N' : Matrix ι ι A}
    (h : CorrA K res φ M N) (h' : CorrA K res φ M' N') : CorrA K res φ (M * M') (N * N') := by
  intro x y
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact corr_sum K res φ _ _ _ fun z _ => corr_mul K res φ (h x z) (h' z y)

theorem corrA_sum {ι κ : Type} (s : Finset κ) (M : κ → Matrix ι ι (Op X)) (N : κ → Matrix ι ι A)
    (h : ∀ i ∈ s, CorrA K res φ (M i) (N i)) : CorrA K res φ (∑ i ∈ s, M i) (∑ i ∈ s, N i) := by
  intro x y
  rw [Matrix.sum_apply, Matrix.sum_apply]
  exact corr_sum K res φ s _ _ fun i hi => h i hi x y

theorem corrA_one {ι : Type} [DecidableEq ι] : CorrA K res φ (1 : Matrix ι ι (Op X)) (1 : Matrix ι ι A) := by
  intro x y
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact corr_one K res φ
  · exact corr_zero K res φ

theorem corrA_map {ι : Type} (M : Matrix ι ι ℂ) :
    CorrA K res φ (M.map (cOp : ℂ → Op X)) (M.map (algebraMap ℂ A)) := by
  intro x y
  exact corr_c K res φ (M x y)

variable {S : Type} [Fintype S] [DecidableEq S]

def CorrM (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))) (N : Wd.M2 (Wd.SlopeTestRemainingChoices S A)) : Prop :=
  ∀ i j, CorrA K res φ (M i j) (N i j)

theorem corrM_mul {M M' : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))} {N N' : Wd.M2 (Wd.SlopeTestRemainingChoices S A)}
    (h : CorrM K res φ M N) (h' : CorrM K res φ M' N') : CorrM K res φ (M * M') (N * N') := by
  intro i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact corrA_sum K res φ _ _ _ fun l _ => corrA_mul K res φ (h i l) (h' l j)

theorem corrM_scal (M : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) :
    CorrM K res φ (scal M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))) (M.map fun B => B.map (algebraMap ℂ A)) := by
  intro i j
  exact corrA_map K res φ (M i j)

variable [StarRing A]

theorem eU_map (a : S) (i j : Fin 2) :
    (Wd.eU a i j : Wd.SlopeTestRemainingChoices S A) = (Wd.eU a i j : Wd.SlopeTestRemainingChoices S ℂ).map (algebraMap ℂ A) := by
  ext x y
  simp only [Wd.eU, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem Rh0_map (a : S) (D : ℂ) :
    (Wd.Rh0 a D : Wd.M2 (Wd.SlopeTestRemainingChoices S A)) = (Wd.Rh0 a D : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)).map fun B => B.map (algebraMap ℂ A) := by
  ext i j x y
  rw [Matrix.map_apply, Matrix.map_apply, LZ.residue_matrix_apply]
  simp only [Wd.Rh0, Wd.P0, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply]
  rw [eU_map, Matrix.map_apply]
  by_cases h1 : i = j <;> by_cases h2 : x = y <;> simp [h1, h2, Matrix.one_apply, Algebra.smul_def, map_mul, map_sub]

theorem Rht0_map (a : S) (D : ℂ) :
    (Wd.Rht0 a D : Wd.M2 (Wd.SlopeTestRemainingChoices S A)) = (Wd.Rht0 a D : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)).map fun B => B.map (algebraMap ℂ A) := by
  ext i j x y
  rw [Matrix.map_apply, Matrix.map_apply, LZ.conj_residue_matrix_apply]
  simp only [Wd.Rht0, Wd.Q0, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply]
  rw [eU_map, Matrix.map_apply]
  by_cases h1 : i = j <;> by_cases h2 : x = y <;> simp [h1, h2, Matrix.one_apply, Algebra.smul_def, map_mul, map_sub]

theorem corr_TT (Qop : ℂ → Wd.M2 (Op X)) (QQ : ℂ → Wd.M2 A)
    (hQ : ∀ y a b, Corr K res φ (Qop y a b) (QQ y a b)) :
    ∀ (w : List (Wd.Letter ℂ S)) (Y : ℂ), CorrM K res φ (TTop Qop w Y) (Wd.TTw QQ w Y) := by
  intro w
  induction w with
  | nil =>
    intro Y i j x y
    simp only [TTop, Wd.TTw, Wd.lift0, Wd.io, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hQ Y i j
    · exact corr_zero K res φ
  | cons l w ih =>
    intro Y
    cases hl : l.plus
    · simp only [TTop, Wd.TTw, hl, Bool.false_eq_true, if_false]
      rw [Rht0_map (A := A)]
      exact corrM_mul K res φ (corrM_scal K res φ _) (ih Y)
    · simp only [TTop, Wd.TTw, hl, if_true]
      rw [Rh0_map (A := A)]
      exact corrM_mul K res φ (ih Y) (corrM_scal K res φ _)

theorem corr_ins (a : S) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))} {N : Wd.M2 (Wd.SlopeTestRemainingChoices S A)} (h : CorrM K res φ M N) :
    CorrA K res φ (insOp a M) (Wd.ins a N) := by
  simp only [insOp, Wd.ins]
  refine corrA_sum K res φ _ _ _ fun i _ => corrA_sum K res φ _ _ _ fun j _ => ?_
  rw [eU_map (A := A)]
  exact corrA_mul K res φ (corrA_map K res φ _) (h i j)

theorem corr_RR (Qop : ℂ → Wd.M2 (Op X)) (QQ : ℂ → Wd.M2 A)
    (hQ : ∀ y a b, Corr K res φ (Qop y a b) (QQ y a b)) :
    ∀ w : List (Wd.Letter ℂ S), CorrA K res φ (RRop Qop w) (Wd.RRw QQ w) := by
  intro w
  induction w with
  | nil =>
    simp only [RRop, Wd.RRw]
    exact corrA_one K res φ
  | cons l w ih =>
    simp only [RRop, Wd.RRw]
    refine corrA_mul K res φ ih (corr_ins K res φ l.intersection_update_fsHerm_neg_one ?_)
    split_ifs
    · exact corr_TT K res φ Qop QQ hQ w l.pt
    · intro i j
      exact corr_TT K res φ Qop QQ hQ w l.pt j i

end modwd

theorem d_moduleOfWdOn : ModuleOfWdOn := by
  unfold ModuleOfWdOn
  intro X _ _ K Y _ _ res A _ _ _ S _ _ φ Qop QQ hQ w x hx a
  have hC := corr_RR K res φ Qop QQ hQ w
  refine ⟨K.sum_mem fun b _ => (hC a b (x b) (hx b)).1, ?_⟩
  simp only [actOp, map_sum]
  exact Finset.sum_congr rfl fun b _ => (hC a b (x b) (hx b)).2

section pos

theorem psd_scale {α : Type} (Z : Finset α) (K : α → α → ℂ) (hK : TB.PSDOn Z K) (c : α → ℝ) :
    TB.PSDOn Z (fun p q => ((c p * c q : ℝ) : ℂ) * K p q) := by
  unfold TB.PSDOn at hK ⊢
  have h := hK.conjTranspose_mul_mul_same (Matrix.diagonal fun p : Z => ((c p : ℝ) : ℂ))
  have e : (Matrix.of fun p q : Z => ((c p * c q : ℝ) : ℂ) * K p q) =
      (Matrix.diagonal fun p : Z => ((c p : ℝ) : ℂ))ᴴ * (Matrix.of fun x y : Z => K x y) *
        Matrix.diagonal fun p : Z => ((c p : ℝ) : ℂ) := by
    ext p q
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [e]
  exact h

theorem psd_pull {α β : Type} [DecidableEq β] (Z : Finset α) (φ : α → β) (R : β → β → ℂ)
    (hR : TB.PSDOn (Z.image φ) R) : TB.PSDOn Z (fun p q => R (φ p) (φ q)) := by
  exact hR.submatrix (fun p : Z => (⟨φ p, Finset.mem_image_of_mem φ p.2⟩ : Z.image φ))

theorem sesq_zero_left {V : Type*} [AddCommGroup V] [Module ℂ V] {U : Submodule ℂ V} {β : V → V → ℂ}
    (hS : P5.SesqOn U β) {y : V} (hy : y ∈ U) : β 0 y = 0 := by
  have h := (hS 0 U.zero_mem 0 U.zero_mem y hy 1).1
  simp only [one_smul, add_zero, zero_add, one_mul] at h
  linear_combination -h

theorem sesq_zero_right {V : Type*} [AddCommGroup V] [Module ℂ V] {U : Submodule ℂ V} {β : V → V → ℂ}
    (hS : P5.SesqOn U β) {y : V} (hy : y ∈ U) : β y 0 = 0 := by
  have h := (hS 0 U.zero_mem 0 U.zero_mem y hy 1).2
  simp only [one_smul, add_zero, zero_add, one_mul, map_one] at h
  linear_combination -h

theorem sesq_sum_left {V : Type*} [AddCommGroup V] [Module ℂ V] {U : Submodule ℂ V} {β : V → V → ℂ}
    (hS : P5.SesqOn U β) {ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → V) (hx : ∀ i, x i ∈ U)
    {y : V} (hy : y ∈ U) : β (∑ i ∈ s, a i • x i) y = ∑ i ∈ s, a i * β (x i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact sesq_zero_left hS hy
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_comm (a i • x i),
      (hS _ (U.sum_mem fun j _ => U.smul_mem (a j) (hx j)) _ (hx i) y hy (a i)).1, ih]
    ring

theorem sesq_sum_right {V : Type*} [AddCommGroup V] [Module ℂ V] {U : Submodule ℂ V} {β : V → V → ℂ}
    (hS : P5.SesqOn U β) {ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → V) (hx : ∀ i, x i ∈ U)
    {y : V} (hy : y ∈ U) : β y (∑ i ∈ s, a i • x i) = ∑ i ∈ s, conj (a i) * β y (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact sesq_zero_right hS hy
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_comm (a i • x i),
      (hS _ (U.sum_mem fun j _ => U.smul_mem (a j) (hx j)) _ (hx i) y hy (a i)).2, ih]
    ring

theorem sesq_herm {V : Type*} [AddCommGroup V] [Module ℂ V] {U : Submodule ℂ V} {β : V → V → ℂ}
    (hS : P5.SesqOn U β) (hN : P5.NonnegOn U β) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    β y x = conj (β x y) := by
  have key : ∀ c : ℂ, β (x + c • y) (x + c • y) = β x x + conj c * β x y + c * (β y x + conj c * β y y) := by
    intro c
    have hxc : x + c • y ∈ U := U.add_mem hx (U.smul_mem c hy)
    rw [(hS x hx y hy _ hxc c).1, (hS x hx y hy x hx c).2, (hS x hx y hy y hy c).2]
  have hz : ∀ z ∈ U, (β z z).im = 0 := fun z hz => by
    have h := (Complex.le_def.mp (hN z hz)).2
    simpa using h.symm
  have h1 := hz _ (U.add_mem hx (U.smul_mem 1 hy))
  have h2 := hz _ (U.add_mem hx (U.smul_mem Complex.I hy))
  have hX := hz x hx
  have hY := hz y hy
  rw [key] at h1 h2
  simp [Complex.conj_I, Complex.mul_im, Complex.mul_re] at h1 h2
  apply Complex.ext <;> simp <;> linarith

theorem gram_of_sesq {V : Type*} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V) (β : V → V → ℂ)
    (hS : P5.SesqOn U β) (hN : P5.NonnegOn U β) {α : Type} (v : α → V) (hv : ∀ p, v p ∈ U) (Z : Finset α) :
    TB.PSDOn Z (fun p q => β (v p) (v q)) := by
  refine ⟨Matrix.IsHermitian.ext fun p q => ?_, fun c => ?_⟩
  · simp only [Matrix.of_apply]
    rw [sesq_herm hS hN (hv q) (hv p)]
    rfl
  · have hw : ∑ i : Z, (starRingEnd ℂ) (c i) • v i ∈ U := U.sum_mem fun i _ => U.smul_mem _ (hv i)
    have h := hN _ hw
    rw [sesq_sum_left hS Finset.univ (fun i : Z => (starRingEnd ℂ) (c i)) (fun i : Z => v i) (fun i => hv i) hw] at h
    simp only [sesq_sum_right hS Finset.univ (fun i : Z => (starRingEnd ℂ) (c i)) (fun i : Z => v i) (fun i => hv i) (hv _),
      RCLike.conj_conj, Complex.conj_conj] at h
    convert h using 1
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (by simp), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply, RCLike.star_def]
    ring

end pos

theorem d_thmPPosOfModule : ThmPPosOfModule := by
  intro E _ _ _ Wp Wq _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hMod hTop v ε hε i hi w Y
  obtain ⟨KK, hPM, hSC⟩ := hMod v
  have hpd := (hB.2 v).1
  set κ := kapG (S.g : ℝ) (S6.rd E) with hκdef
  set Γ := GamLev S.G.k S.G.r κ (deG (S.g : ℝ) (S6.rd E)) i with hΓdef
  have hrd : 0 ≤ S6.rd E := Real.rpow_nonneg (by positivity) _
  have hκ : 0 ≤ κ := div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) hrd)
  have hde : 0 ≤ deG (S.g : ℝ) (S6.rd E) := div_nonneg (by norm_num) (mul_nonneg hrd (by positivity))
  have hΓ : 0 ≤ Γ := Finset.prod_nonneg fun l _ => div_nonneg (zpow_nonneg hκ _) hde
  set F := cutF (T v).base χ (f v) ε with hF
  set s := M.sgn (parOf S v) (S.l + 1) with hsdef
  set R := RRplace (T v) s (ν' v) (m₀ v) (top v) F i (w.1 v) with hRdef
  have hadm : AdmAt S v (w.1 v) := ⟨w, rfl⟩
  have core : ∀ Z : Finset C.LPt, TB.PSDOn Z R := by
    intro Z
    by_cases hir : i ≤ S.G.r
    · let j : Fin (S.G.r + 1) := ⟨i, by omega⟩
      let U := Submodule.pi Set.univ fun _ : Wd.Ix (Fin (w.1 v).length) => KK j
      let vec : C.LPt → (Wd.Ix (Fin (w.1 v).length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) := fun p =>
        if h : IsLocPt p i then (fun a => castF (by simp [j, h.2]) (sliceAt S.G.k S.G.r (T v).base.z (T v).base.z'
          (uwG S.G.k S.G.r (T v).base.z (T v).base.z' F i hir (w.1 v) a) p)) else 0
      have hvec : ∀ p, vec p ∈ U := by
        intro p
        simp only [vec]
        split_ifs with h
        · rw [Submodule.mem_pi]
          intro a _
          exact hSC ε hε i hir (w.1 v) hadm p h a
        · exact U.zero_mem
      obtain ⟨hS, hN⟩ := hPM j (w.1 v) hadm
      have hR : R = fun p q => formLev (T v) s j (w.1 v) (vec p) (vec q) := by
        funext p q
        simp only [hRdef, RRplace]
        by_cases hp : IsLocPt p i <;> by_cases hq : IsLocPt q i
        · rw [dif_pos ⟨hp, hq⟩, dif_pos hir]
          simp only [vec, dif_pos hp, dif_pos hq]
          rfl
        · rw [dif_neg (fun h => hq h.2)]
          have : vec q = 0 := by simp only [vec, dif_neg hq]
          rw [this]
          exact (sesq_zero_right hS (hvec p)).symm
        · rw [dif_neg (fun h => hp h.1)]
          have : vec p = 0 := by simp only [vec, dif_neg hp]
          rw [this]
          exact (sesq_zero_left hS (hvec q)).symm
        · rw [dif_neg (fun h => hp h.1)]
          have : vec p = 0 := by simp only [vec, dif_neg hp]
          rw [this]
          exact (sesq_zero_left hS (hvec q)).symm
      rw [hR]
      exact gram_of_sesq U _ hS hN vec hvec Z
    · have hir1 : i = S.G.r + 1 := by omega
      let ind : C.LPt → ℝ := fun p => if IsLocPt p i then 1 else 0
      let K : C.LPt → C.LPt → ℂ := fun p q => if w.1 v = [] then
        B.hsInner (vecV (T v).base (ν' v) (m₀ v) F p) (vecV (T v).base (ν' v) (m₀ v) F q)
        else top v F (w.1 v) p q
      have hR : R = fun p q => ((ind p * ind q : ℝ) : ℂ) * K p q := by
        funext p q
        simp only [hRdef, RRplace, ind, K]
        by_cases hp : IsLocPt p i <;> by_cases hq : IsLocPt q i
        · rw [dif_pos ⟨hp, hq⟩, dif_neg hir, if_pos hir1, if_pos hp, if_pos hq]
          simp [LevTower.base]
        · rw [dif_neg (fun h => hq h.2), if_neg hq]
          simp
        · rw [dif_neg (fun h => hp h.1), if_neg hp]
          simp
        · rw [dif_neg (fun h => hp h.1), if_neg hp]
          simp
      rw [hR]
      refine psd_scale Z K ?_ ind
      by_cases hw : w.1 v = []
      · have hK : K = fun p q => B.hsInner (vecV (T v).base (ν' v) (m₀ v) F p)
            (vecV (T v).base (ν' v) (m₀ v) F q) := by
          funext p q
          simp [K, hw]
        rw [hK]
        unfold TB.PSDOn
        have hg := (Matrix.posSemidef_gram ℂ (fun p : Z => B.hsVec (vecV (T v).base (ν' v) (m₀ v) F p))).transpose
        convert hg using 1
        all_goals rfl
      · have hK : K = top v F (w.1 v) := by
          funext p q
          simp [K, hw]
        rw [hK]
        exact hTop v ε hε (w.1 v) hadm hw Z
  let c : C.LPt → ℝ := fun p => √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * (bSt κ p)⁻¹ * √(Γ⁻¹)
  have hs : √(Γ⁻¹) * √(Γ⁻¹) = Γ⁻¹ := Real.mul_self_sqrt (inv_nonneg.2 hΓ)
  have hRR : ∀ p q, (S.pd v).RR ε i (w.1 v) p q = (((1 : ℝ) ^ 2 / (bSt κ p * bSt κ q * Γ) : ℝ) : ℂ) *
      R (toStd S.G.r (S.g : ℝ) 1 p) (toStd S.G.r (S.g : ℝ) 1 q) := by
    intro p q
    rw [hpd]
    rfl
  have hfun : S.gramLoc v ε i (w.1 v) = fun p q => ((c p * c q : ℝ) : ℂ) *
      R (toStd S.G.r (S.g : ℝ) 1 p) (toStd S.G.r (S.g : ℝ) 1 q) := by
    funext p q
    unfold C.HidaSetting.gramLoc
    rw [hRR]
    have e : ((1 : ℝ) ^ 2 / (bSt κ p * bSt κ q * Γ)) = (bSt κ p)⁻¹ * (bSt κ q)⁻¹ * Γ⁻¹ := by
      rw [one_pow, one_div, mul_inv, mul_inv]
    have hr : √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G q) *
        ((1 : ℝ) ^ 2 / (bSt κ p * bSt κ q * Γ)) = c p * c q := by
      rw [e]
      simp only [c]
      linear_combination (-(√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G q) *
        (bSt κ p)⁻¹ * (bSt κ q)⁻¹)) * hs
    rw [← hr]
    push_cast
    ring
  rw [hfun]
  exact psd_scale Y _ (psd_pull Y _ R (core _)) c

end
end Formalism.FourierDecayAlt.P.Dx1

end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.D Formalism.REAL Formalism.QuantumDeterminants Finset
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.Dx1.Rel
noncomputable section
open Classical

theorem ptSize_cons (s : ℕ) (t : ℂ) (rest : C.LPt) : ptSize ((s, t) :: rest) = s + ptSize rest := by
  simp only [ptSize, List.map_cons, List.sum_cons]

theorem partner_spec : ∀ (p : C.LPt) (a : ℕ), a < ptSize p →
    ptPartner p a < ptSize p ∧ ptPartner p (ptPartner p a) = a ∧
    ∀ i, ptEntry p i a = if i = ptPartner p a then ptScal p a else 0
  | [], a, h => by simp [ptSize] at h
  | (s, t) :: rest, a, h => by
    rw [ptSize_cons] at h ⊢
    by_cases ha : a < s
    · have hp : ptPartner ((s, t) :: rest) a = s - 1 - a := by simp [ptPartner, ha]
      rw [hp]
      refine ⟨by omega, ?_, ?_⟩
      · simp only [ptPartner, show s - 1 - a < s by omega, if_true]; omega
      · intro i
        by_cases hi : i < s
        · simp only [ptEntry, ptScal, ha, hi, and_self, if_true]
          split_ifs <;> first | rfl | (exfalso; omega)
        · simp only [ptEntry, ptScal, ha, hi, false_and, and_true, if_false, if_true]
          split_ifs <;> first | rfl | (exfalso; omega)
    · have ih := partner_spec rest (a - s) (by omega)
      have hp : ptPartner ((s, t) :: rest) a = s + ptPartner rest (a - s) := by simp [ptPartner, ha]
      rw [hp]
      refine ⟨by omega, ?_, ?_⟩
      · simp only [ptPartner, show ¬ (s + ptPartner rest (a - s) < s) by omega, if_false]
        rw [show s + ptPartner rest (a - s) - s = ptPartner rest (a - s) by omega, ih.2.1]; omega
      · intro i
        by_cases hi : s ≤ i
        · simp only [ptEntry, ptScal, ha, show ¬ i < s by omega, false_and, and_false, if_false,
            show s ≤ a by omega, hi, and_self, if_true]
          rw [ih.2.2 (i - s)]
          split_ifs <;> first | rfl | (exfalso; omega)
        · simp only [ptEntry, ptScal, ha, show i < s by omega, and_false, hi, false_and, if_false]
          split_ifs <;> first | rfl | (exfalso; omega)

theorem scal_ne : ∀ (p : C.LPt), (∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0) → ∀ a, a < ptSize p → ptScal p a ≠ 0
  | [], _, a, h => by simp [ptSize] at h
  | (s, t) :: rest, hb, a, h => by
    rw [ptSize_cons] at h
    by_cases ha : a < s
    · simp only [ptScal, ha, if_true]; exact (hb (s, t) (by simp)).2
    · simp only [ptScal, ha, if_false]
      exact scal_ne rest (fun b hb' => hb b (by simp [hb'])) (a - s) (by omega)

theorem block : ∀ (p : C.LPt) (a : ℕ), a + 1 < ptSize p →
    (ptPartner p (a + 1) + 1 = ptPartner p a ∧ ptScal p (a + 1) = ptScal p a) ∨
      ptPartner p a < ptPartner p (a + 1)
  | [], a, h => by simp [ptSize] at h
  | (s, t) :: rest, a, h => by
    rw [ptSize_cons] at h
    by_cases ha : a + 1 < s
    · left
      simp only [ptPartner, ptScal, ha, show a < s by omega, if_true, and_true]
      omega
    · by_cases ha' : a < s
      · right
        simp only [ptPartner, ha', ha, if_true, if_false]
        omega
      · have ih := block rest (a - s) (by omega)
        simp only [ptPartner, ptScal, ha, ha', if_false]
        rw [show a + 1 - s = a - s + 1 by omega]
        rcases ih with ⟨h1, h2⟩ | h1
        · left; exact ⟨by omega, h2⟩
        · right; omega

theorem core (r : ℕ) (P : Fin (r + 1) → Fin (r + 1)) (hP : ∀ a, P (P a) = a) (t : Fin (r + 1) → ℂ)
    (ht : ∀ a, t a ≠ 0)
    (hblk : ∀ b : Fin r, ((P b.succ).val + 1 = (P b.castSucc).val ∧ t b.succ = t b.castSucc) ∨
      P b.castSucc < P b.succ)
    (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hAu : ∀ i j, j < i → A i j = 0) (hAd : ∀ i, A i i = 1)
    (hBu : ∀ i j, j < i → B i j = 0)
    (h : Bᴴ * Matrix.of (fun i a => if i = P a then t a else 0) * A =
      Matrix.of (fun i a => if i = P a then t a else 0)) :
    ∑ b : Fin r, A b.castSucc b.succ = -conj (∑ a : Fin r, B a.castSucc a.succ) := by
  set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of (fun i a => if i = P a then t a else 0) with hZ
  have hAt : A.IsUpperTriangular := fun i j hij => hAu i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAt]
    simp [hAd]
  have hU : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hAA' : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hU
  have hA'A : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hU
  haveI := Matrix.invertibleOfIsUnitDet A hU
  have hA'u : ∀ i j, j < i → A⁻¹ i j = 0 := fun i j hij =>
    Matrix.blockTriangular_inv_of_blockTriangular hAt hij
  have hA'd : ∀ i, A⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun hA'A i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at this
    · rwa [hAd, mul_one] at this
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc | hc
      · rw [hA'u i c hc, zero_mul]
      · rw [hAu c i hc, mul_zero]
    · simp
  have hsup : ∀ b : Fin r, A⁻¹ b.castSucc b.succ = -A b.castSucc b.succ := by
    intro b
    have hne : b.castSucc ≠ b.succ := by simp [Fin.ext_iff]
    have := congrFun (congrFun hA'A b.castSucc) b.succ
    rw [Matrix.mul_apply, Matrix.one_apply_ne hne, Finset.sum_eq_add b.castSucc b.succ hne] at this
    · rw [hA'd, hAd, one_mul, mul_one] at this
      linear_combination this
    · intro c _ hc
      have h1 : c.val ≠ b.val := fun e => hc.1 (Fin.ext (by simp [e]))
      have h2 : c.val ≠ b.val + 1 := fun e => hc.2 (Fin.ext (by simp [e]))
      rcases Nat.lt_or_gt_of_ne h1 with h3 | h3
      · rw [hA'u _ _ (by rw [Fin.lt_def]; simpa using h3), zero_mul]
      · rw [hAu _ _ (by rw [Fin.lt_def]; simp; omega), mul_zero]
    · simp
    · simp
  have hloc : Bᴴ * Z = Z * A⁻¹ := by
    calc Bᴴ * Z = Bᴴ * Z * (A * A⁻¹) := by rw [hAA', Matrix.mul_one]
      _ = (Bᴴ * Z * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Z * A⁻¹ := by rw [h]
  have E : ∀ a c, star (B (P c) a) * t c = t (P a) * A⁻¹ (P a) c := by
    intro a c
    have := congrFun (congrFun hloc a) c
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (P c), Finset.sum_eq_single (P a)] at this
    · simpa [Z, Matrix.conjTranspose_apply, hP] using this
    · intro j _ hj
      simp only [Z, Matrix.of_apply]
      rw [if_neg (fun e => hj (by rw [e, hP]))]; simp
    · simp
    · intro j _ hj
      simp [Z, hj]
    · simp
  have hA : ∀ b : Fin r, A b.castSucc b.succ =
      if (P b.succ).val + 1 = (P b.castSucc).val then -star (B (P b.succ) (P b.castSucc)) else 0 := by
    intro b
    have e := E (P b.castSucc) b.succ
    rw [hP, hsup] at e
    rcases hblk b with ⟨h1, h2⟩ | h1
    · rw [if_pos h1]
      rw [h2] at e
      have := mul_right_cancel₀ (ht b.castSucc) (by rw [e]; ring : star (B (P b.succ) (P b.castSucc)) * t b.castSucc = (-A b.castSucc b.succ) * t b.castSucc)
      rw [this]; ring
    · rw [if_neg (by rw [Fin.lt_def] at h1; omega)]
      rw [hBu _ _ h1, star_zero, zero_mul] at e
      have := (mul_eq_zero.mp e.symm).resolve_left (ht _)
      linear_combination -this
  have hB : ∀ a : Fin r, B a.castSucc a.succ =
      if (P a.succ).val + 1 = (P a.castSucc).val then B a.castSucc a.succ else 0 := by
    intro a
    split_ifs with h1
    · rfl
    · have e := E a.succ (P a.castSucc)
      rw [hP] at e
      rcases hblk a with ⟨h2, _⟩ | h2
      · exact absurd h2 h1
      · rw [hA'u _ _ h2, mul_zero] at e
        have := (mul_eq_zero.mp e).resolve_right (ht _)
        simpa using this
  set WB := (univ : Finset (Fin r)).filter (fun b => (P b.succ).val + 1 = (P b.castSucc).val) with hWB
  have s1 : ∑ b : Fin r, A b.castSucc b.succ = ∑ b ∈ WB, -star (B (P b.succ) (P b.castSucc)) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun b _ => hA b
  have s2 : ∑ a : Fin r, B a.castSucc a.succ = ∑ a ∈ WB, B a.castSucc a.succ := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun a _ => hB a
  let φ : Fin r → Fin r := fun b => if hb : (P b.succ).val < r then ⟨(P b.succ).val, hb⟩ else b
  have hφlt : ∀ b ∈ WB, (P b.succ).val < r := by
    intro b hb
    rw [hWB, Finset.mem_filter] at hb
    have := (P b.castSucc).isLt; omega
  have hφc : ∀ b ∈ WB, (φ b).castSucc = P b.succ := by
    intro b hb; simp only [φ, dif_pos (hφlt b hb)]; ext; simp
  have hφs : ∀ b ∈ WB, (φ b).succ = P b.castSucc := by
    intro b hb
    have hb' := hb
    rw [hWB, Finset.mem_filter] at hb'
    simp only [φ, dif_pos (hφlt b hb)]; ext; simp [hb'.2]
  have hφmem : ∀ b ∈ WB, φ b ∈ WB := by
    intro b hb
    rw [hWB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hφc b hb, hφs b hb, hP, hP]; simp
  have hφφ : ∀ b ∈ WB, φ (φ b) = b := by
    intro b hb
    have h1 : (P (φ b).succ).val < r := hφlt _ (hφmem b hb)
    have h2 := hφs b hb
    simp only [φ] at h1 h2 ⊢
    rw [dif_pos h1]
    ext
    simp [h2, hP]
  have s3 : ∑ b ∈ WB, star (B (P b.succ) (P b.castSucc)) = ∑ a ∈ WB, star (B a.castSucc a.succ) := by
    refine Finset.sum_nbij' φ φ hφmem hφmem hφφ hφφ ?_
    intro b hb
    rw [hφc b hb, hφs b hb]
  rw [s1, s2, Finset.sum_neg_distrib, s3, map_sum]
  rfl

section geo
variable {k r : ℕ}

theorem mulVec_bvec (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (e x : Fin (2 * r + k + 1)) :
    (M *ᵥ bvec e) x = M x e := by
  simp [bvec]

def Fm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r z a i

def Bm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => if h : i.val < r then (ρ *ᵥ fvec k r z a) ⟨i.val, by omega⟩ else if a.val = r then 1 else 0

theorem fvec_lt (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (h : a.val < r) :
    fvec k r z a = bvec (eI k r ⟨a.val, h⟩) := by
  rw [fvec, dif_pos h]

theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (h : ¬ a.val < r) :
    fvec k r z a = z := by
  rw [fvec, dif_neg h]

theorem mulVec_apply_eq_of_mem_Nset_of_inWb_of_le (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hρ : ρ ∈ Nset k r)
    (j : Fin (2 * r + k + 1)) (hj : r ≤ j.val) : (ρ *ᵥ z) j = z j := by
  obtain ⟨-, hN2, hN3⟩ := hρ
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · by_cases hjk : j.val ≤ r + k
    · rw [hN3 j j hj hjk hj, if_pos rfl, one_mul]
    · rw [hz j (Or.inr (by omega)), mul_zero]
  · intro i _ hij
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hz i hi, mul_zero]
    · push_neg at hi
      rw [hN3 j i hi.1 hi.2 hj, if_neg (Ne.symm hij), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem expandAt (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hρ : ρ ∈ Nset k r)
    (j : Fin (2 * r + k + 1)) (c : Fin (r + 1)) :
    (ρ *ᵥ fvec k r z c) j = ∑ i, fvec k r z i j * Bm k r z ρ i c := by
  obtain ⟨hN1, hN2, hN3⟩ := hρ
  by_cases hj : j.val < r
  · rw [Finset.sum_eq_single (⟨j.val, by omega⟩ : Fin (r + 1))]
    · rw [fvec_lt z (⟨j.val, by omega⟩ : Fin (r + 1)) hj]
      have hb : bvec (eI k r ⟨j.val, hj⟩) j = 1 := by
        simp [bvec, Pi.single_apply, eI, Fin.ext_iff]
      rw [hb, one_mul]
      simp only [Bm, Matrix.of_apply]
      rw [dif_pos hj]
    · intro i _ hi
      by_cases hir : i.val < r
      · rw [fvec_lt z i hir]
        have hb : bvec (eI k r ⟨i.val, hir⟩) j = 0 := by
          simp only [bvec, Pi.single_apply]
          rw [if_neg]
          intro h
          apply hi
          have h2 := congrArg Fin.val h
          simp [eI] at h2
          exact Fin.ext (by simp; omega)
        rw [hb, zero_mul]
      · rw [fvec_last z i hir, hz j (Or.inl hj), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · push_neg at hj
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [fvec_last z (Fin.last r) (by simp)]
      simp only [Bm, Matrix.of_apply]
      rw [dif_neg (by simp)]
      by_cases hc : c.val < r
      · rw [fvec_lt z c hc, mulVec_bvec, hN2 ⟨c.val, hc⟩ j (by show c.val ≤ j.val; omega),
          if_neg (fun h => by have h2 := congrArg Fin.val h; simp [eI] at h2; omega), if_neg (by omega)]
        simp
      · rw [fvec_last z c hc, mulVec_apply_eq_of_mem_Nset_of_inWb_of_le z hz ρ ⟨hN1, hN2, hN3⟩ j hj]
        rw [if_pos (by simp at hc ⊢; omega), mul_one]
    · intro i _ hi
      have hir : i.val < r := by
        have h1 := i.isLt
        have h2 : i.val ≠ r := fun h => hi (Fin.ext (by simp [h]))
        omega
      rw [fvec_lt z i hir]
      have hb : bvec (eI k r ⟨i.val, hir⟩) j = 0 := by
        simp only [bvec, Pi.single_apply]
        rw [if_neg]
        intro h
        have h2 := congrArg Fin.val h
        simp [eI] at h2
        omega
      rw [hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem expand (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hρ : ρ ∈ Nset k r) :
    ρ * Fm k r z = Fm k r z * Bm k r z ρ := by
  ext j c
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fm, Matrix.of_apply]
  exact expandAt z hz ρ hρ j c

theorem Bm_upper (z : Fin (2 * r + k + 1) → ℂ)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hρ : ρ ∈ Nset k r)
    (i a : Fin (r + 1)) (h : a < i) : Bm k r z ρ i a = 0 := by
  have h' : a.val < i.val := h
  obtain ⟨-, hN2, hN3⟩ := hρ
  simp only [Bm, Matrix.of_apply]
  split_ifs with h1 h2
  · have ha : a.val < r := by omega
    rw [fvec_lt z a ha, mulVec_bvec, hN2 ⟨a.val, ha⟩ ⟨i.val, by omega⟩ (by show a.val ≤ i.val; omega)]
    rw [if_neg]
    intro h3
    have h4 := congrArg Fin.val h3
    simp [eI] at h4
    omega
  · exfalso
    omega
  · rfl

theorem Bm_diag (z : Fin (2 * r + k + 1) → ℂ)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hρ : ρ ∈ Nset k r)
    (i : Fin (r + 1)) : Bm k r z ρ i i = 1 := by
  obtain ⟨-, hN2, hN3⟩ := hρ
  simp only [Bm, Matrix.of_apply]
  split_ifs with h h2
  · rw [fvec_lt z i h, mulVec_bvec]
    have e := hN2 ⟨i.val, h⟩ ⟨i.val, by omega⟩ (le_refl _)
    rw [e]
    simp [eI]
  · rfl
  · exact absurd (by omega) h2

theorem zhat_eq (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' γ = (Fm k r z)ᴴ * Hpk k r * γ * Fm k r z' := by
  ext a b
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Zhat, herm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fm, Matrix.conjTranspose_apply,
    Matrix.of_apply, Pi.star_apply]

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z ρ = ∑ a : Fin r, Bm k r z ρ a.castSucc a.succ := by
  simp only [ell, Bm, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (by simp : ((Fin.castSucc a : Fin (r + 1)) : ℕ) < r)]
  by_cases h : a.val + 1 < r
  · rw [dif_pos h, fvec_lt z a.succ (by simpa using h), mulVec_bvec]
    rfl
  · rw [dif_neg h, fvec_last z a.succ (by simpa using h)]
    rfl

end geo

theorem ptRelevant : PtRelevant := by
  intro k r Wp Wq _ _ _ _ D p γ hp hγ hZ
  refine ⟨hγ, ?_⟩
  rintro ρ ⟨hρN, hρ'N⟩
  have hU : IsUnit γ.det := by
    by_contra hn
    have h0 : γ⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit γ hn
    have := hρ'N.2.2 ⟨r, by omega⟩ ⟨r, by omega⟩ le_rfl (by simp) le_rfl
    rw [h0] at this; simp at this
  have hcomm : γ * (γ⁻¹ * ρ * γ) = ρ * γ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv γ hU, Matrix.one_mul]
  set ρ' := γ⁻¹ * ρ * γ with hρ'
  set B := Bm k r D.z ρ with hBdef
  set A := Bm k r D.z' ρ' with hAdef
  have hB := expand D.z D.z_mem ρ hρN
  have hA := expand D.z' D.z'_mem ρ' hρ'N
  have hunit : ρᴴ * Hpk k r * ρ = Hpk k r := hρN.1
  have key : Bᴴ * Zhat k r D.z D.z' γ * A = Zhat k r D.z D.z' γ := by
    rw [zhat_eq]
    set F := Fm k r D.z
    set F' := Fm k r D.z'
    calc Bᴴ * (Fᴴ * Hpk k r * γ * F') * A = (F * B)ᴴ * (Hpk k r * (γ * (F' * A))) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (ρ * F)ᴴ * (Hpk k r * (γ * (ρ' * F'))) := by rw [hB, hA]
      _ = Fᴴ * ((ρᴴ * Hpk k r * ρ) * (γ * F')) := by
          rw [← Matrix.mul_assoc γ ρ' F', hcomm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Fᴴ * Hpk k r * γ * F' := by rw [hunit]; simp only [Matrix.mul_assoc]
  have hsz : ptSize p = r + 1 := hp.2
  have hPlt : ∀ a : Fin (r + 1), ptPartner p a.val < r + 1 := fun a => by
    have := (partner_spec p a.val (by omega)).1; omega
  let P : Fin (r + 1) → Fin (r + 1) := fun a => ⟨ptPartner p a.val, hPlt a⟩
  let t : Fin (r + 1) → ℂ := fun a => ptScal p a.val
  have hP : ∀ a, P (P a) = a := fun a => Fin.ext (partner_spec p a.val (by omega)).2.1
  have ht : ∀ a, t a ≠ 0 := fun a => scal_ne p hp.1 a.val (by omega)
  have hblk : ∀ b : Fin r, ((P b.succ).val + 1 = (P b.castSucc).val ∧ t b.succ = t b.castSucc) ∨
      P b.castSucc < P b.succ := by
    intro b
    rcases block p b.val (by omega) with h | h
    · left; exact h
    · right; exact h
  have hZP : ptMatN p (r + 1) = Matrix.of fun i a => if i = P a then t a else 0 := by
    ext i a
    simp only [ptMatN, Matrix.of_apply]
    rw [(partner_spec p a.val (by omega)).2.2 i.val]
    simp only [P, t, Fin.ext_iff]
  have hcore := core r P hP t ht hblk A B (Bm_upper D.z' ρ' hρ'N) (Bm_diag D.z' ρ' hρ'N)
    (Bm_upper D.z ρ hρN) (by rw [← hZP, ← hZ]; exact key)
  unfold psi
  rw [ell_eq, ell_eq, ← hBdef, ← hAdef, hcore]
  congr 3
  simp [cStd, Complex.mul_re, Complex.conj_re, Complex.conj_im]

end
end Formalism.FourierDecayAlt.P.Dx1.Rel

end

namespace Formalism.FourierDecayAlt.P

theorem ptPerm_spec : Formalism.FourierDecayAlt.D.PtPermSpec := by
  exact Dx1.d_ptPermSpec
theorem ptG_spec : Formalism.FourierDecayAlt.D.PtGSpec := by
  exact Dx1.ptGSpec
theorem orbital_transfer_of_data : Formalism.FourierDecayAlt.D.OrbJOfData := by
  exact Dx1.orbJOfData
theorem orbital_data_of_parts : Formalism.FourierDecayAlt.D.OrbDataOfParts := by
  exact Dx1.orbDataOfParts
theorem positivity_of_forms : Formalism.FourierDecayAlt.D.ThmPPosOfForms := by
  exact Dx1.thmPPosOfForms
theorem relevant_points_holds : Formalism.FourierDecayAlt.D.PtRelevant := by
  exact Dx1.Rel.ptRelevant
theorem good_of_admissible : Formalism.FourierDecayAlt.D.GoodOfAdm := by
  exact Dx1.d_goodOfAdm
theorem level_zero_holds : Formalism.FourierDecayAlt.D.LevelZero := by
  exact Dx1.LZ.levelZero
theorem lemma_E_of_residue : Formalism.FourierDecayAlt.D.LemmaEOfRR0 := by
  exact Dx1.d_lemmaEOfRR0
theorem positivity_of_module : Formalism.FourierDecayAlt.D.ThmPPosOfModule := by
  exact Dx1.d_thmPPosOfModule
theorem module_of_words : Formalism.FourierDecayAlt.D.ModuleOfWdOn := by
  exact Dx1.d_moduleOfWdOn

end Formalism.FourierDecayAlt.P
