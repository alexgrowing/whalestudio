import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.HfSelfProj

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)

theorem sum_mulVec' {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι K) (x : ι → K) :
    (∑ c ∈ s, A c) *ᵥ x = ∑ c ∈ s, A c *ᵥ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, add_mulVec, ih]

theorem vecMul_sum' {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι K) (x : ι → K) :
    x ᵥ* (∑ c ∈ s, A c) = ∑ c ∈ s, x ᵥ* A c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, vecMul_add, ih]

section Drop

variable {m : ℕ} (i : Fin (m + 1))

def ins (x : Fin m → K) : Fin (m + 1) → K := Fin.insertNth i 0 x

omit S in
theorem ins_same (x : Fin m → K) : ins i x i = 0 := Fin.insertNth_apply_same _ _ _

omit S in
theorem ins_succAbove (x : Fin m → K) (s : Fin m) : ins i x (i.succAbove s) = x s :=
  Fin.insertNth_apply_succAbove _ _ _ _

omit S in
theorem mulVec_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x : Fin m → K) (s : Fin m) :
    (G *ᵥ ins i x) (i.succAbove s) = (G.submatrix i.succAbove i.succAbove *ᵥ x) s := by
  simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, ins_same, ins_succAbove, mul_zero, zero_add,
    submatrix_apply]

omit S in
theorem vecMul_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x : Fin m → K) (s : Fin m) :
    (ins i x ᵥ* G) (i.succAbove s) = (x ᵥ* G.submatrix i.succAbove i.succAbove) s := by
  simp only [vecMul, dotProduct, Fin.sum_univ_succAbove _ i, ins_same, ins_succAbove, zero_mul, zero_add,
    submatrix_apply]

theorem cv_ins (x : Fin m → K) : S.cv (ins i x) = ins i (S.cv x) := by
  funext r
  rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
  · simp [cv, ins_same]
  · simp [cv, ins_succAbove]

theorem hf_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x y : Fin m → K) :
    S.hf G (ins i x) (ins i y) = S.hf (G.submatrix i.succAbove i.succAbove) x y := by
  rw [hf, hf, S.cv_ins, dotProduct, dotProduct, Fin.sum_univ_succAbove _ i]
  simp only [ins_same, ins_succAbove, zero_mul, zero_add, mulVec_ins]

theorem IntV_ins {x : Fin m → K} (hx : S.IntV x) : S.IntV (ins i x) := by
  intro r
  rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
  · rw [ins_same]; exact S.O.zero_mem
  · rw [ins_succAbove]; exact hx s

theorem ext_drop {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) K} {a : Fin (m + 1) → K} (ha : a i ≠ 0)
    (hσa : S.σ (a i) ≠ 0) (hM : M *ᵥ a = 0) (hN : N *ᵥ a = 0) (hM' : S.cv a ᵥ* M = 0)
    (hN' : S.cv a ᵥ* N = 0)
    (h : ∀ s t, M (i.succAbove s) (i.succAbove t) = N (i.succAbove s) (i.succAbove t)) : M = N := by
  have hcol : ∀ s, M (i.succAbove s) i = N (i.succAbove s) i := by
    intro s
    have e1 := congrFun hM (i.succAbove s)
    have e2 := congrFun hN (i.succAbove s)
    simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, Pi.zero_apply] at e1 e2
    simp only [h] at e1
    have : (M (i.succAbove s) i - N (i.succAbove s) i) * a i = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' ha
  have hrow : ∀ s j, M (i.succAbove s) j = N (i.succAbove s) j := by
    intro s j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨t, rfl⟩
    · exact hcol s
    · exact h s t
  ext r j
  rcases Fin.eq_self_or_eq_succAbove i r with hr | ⟨s, rfl⟩
  · rw [hr]
    have e1 := congrFun hM' j
    have e2 := congrFun hN' j
    simp only [vecMul, dotProduct, Fin.sum_univ_succAbove _ i, Pi.zero_apply, cv] at e1 e2
    simp only [hrow] at e1
    have : S.σ (a i) * (M i j - N i j) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hσa
    · exact sub_eq_zero.mp h'
  · exact hrow s j

theorem UM_drop {G : Matrix (Fin (m + 1)) (Fin (m + 1)) K} {a : Fin (m + 1) → K} (hU : S.UM G)
    (ha : S.IntV a) (hai : ¬ S.NU (a i)) (hGa : G *ᵥ a = 0) (haG : S.cv a ᵥ* G = 0) :
    S.UM (G.submatrix i.succAbove i.succAbove) := by
  intro x hx hNU
  have hall : ∀ s, S.NU ((G *ᵥ ins i x) (i.succAbove s)) := fun s => by rw [mulVec_ins]; exact hNU s
  have hσO := S.hσO _ (ha i)
  have hσn := S.not_NU_σ (ha i) hai
  have hne : S.σ (a i) ≠ 0 := S.ne_zero_of_not_NU hσn
  have hNU' : ∀ r, S.NU ((G *ᵥ ins i x) r) := by
    intro r
    rcases Fin.eq_self_or_eq_succAbove i r with hr | ⟨s, rfl⟩
    · rw [hr]
      have e := congrArg (fun v => v ⬝ᵥ ins i x) haG
      simp only [zero_dotProduct] at e
      rw [← dotProduct_mulVec, dotProduct, Fin.sum_univ_succAbove _ i] at e
      have e' : S.σ (a i) * (G *ᵥ ins i x) i
          = -(∑ s, S.cv a (i.succAbove s) * (G *ᵥ ins i x) (i.succAbove s)) := by
        simp only [cv] at e ⊢; linear_combination e
      have hv : (G *ᵥ ins i x) i
          = (S.σ (a i))⁻¹ * -(∑ s, S.cv a (i.succAbove s) * (G *ᵥ ins i x) (i.succAbove s)) := by
        rw [← e', ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      rw [hv]
      exact S.NU_mul (S.hinv _ hσO hσn) (S.NU_neg (S.NU_sum _ _ fun s _ =>
        S.NU_mul (S.IntV_cv ha _) (hall s)))
    · exact hall s
  obtain ⟨x', hx', hxx⟩ := hU (ins i x) (S.IntV_ins i hx) hNU'
  have hai0 : a i ≠ 0 := S.ne_zero_of_not_NU hai
  set y := x' - (x' i * (a i)⁻¹) • a with hy_def
  have hyI : S.IntV y := S.IntV_sub hx' (S.IntV_smul (S.O.mul_mem (hx' i) (S.hinv _ (ha i) hai)) ha)
  have hyi : y i = 0 := by
    simp only [hy_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp; ring
  have hGy : G *ᵥ y = G *ᵥ x' := by
    rw [hy_def, mulVec_sub, mulVec_smul, hGa, smul_zero, sub_zero]
  have hins : ins i (fun s => y (i.succAbove s)) = y := by
    funext r
    rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
    · rw [ins_same, hyi]
    · rw [ins_succAbove]
  refine ⟨fun s => y (i.succAbove s), fun s => hyI _, ?_⟩
  funext s
  rw [← mulVec_ins, hxx, Pi.smul_apply, Pi.smul_apply, ← mulVec_ins, hins, hGy]

end Drop

theorem jac_fin : ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) K), S.IntM Γ → S.Herm Γ → S.UM Γ →
    ∃ (k : ℕ) (v : Fin k → Fin m → K), (∀ c, S.IntV (v c)) ∧
      (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
      ∑ c, vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ
  | 0, Γ, _, _, _ => ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by ext i; exact i.elim0⟩
  | m + 1, Γ, hΓ, hH, hU => by
    by_cases h0 : Γ = 0
    · exact ⟨0, Fin.elim0, fun c => c.elim0, fun c => c.elim0, by simp [h0]⟩
    obtain ⟨a, i, ha, hai, haa⟩ := S.exists_unit_vec hΓ hH hU h0
    have hG := S.IntM_Γp hΓ ha
    have hHG := S.Herm_Γp hΓ hH ha
    have hUG := S.UM_Γp hΓ hH hU ha haa
    have hGa := S.Γp_mulVec_self (Γ := Γ) haa
    have haG := S.vecMul_Γp_self (Γ := Γ) haa
    set G := S.Γp Γ a with hG_def
    obtain ⟨k, v'', hvI, hvo, hvs⟩ := jac_fin m (G.submatrix i.succAbove i.succAbove)
      (fun s t => hG _ _) (fun s t => hHG _ _) (S.UM_drop i hUG ha hai hGa haG)
    have hai0 : a i ≠ 0 := S.ne_zero_of_not_NU hai
    have hσa : S.σ (a i) ≠ 0 := S.ne_zero_of_not_NU (S.not_NU_σ (ha i) hai)
    set v' : Fin k → Fin (m + 1) → K := fun c => ins i (v'' c) with hv'_def
    have hv'I : ∀ c, S.IntV (v' c) := fun c => S.IntV_ins i (hvI c)
    have hv'o : ∀ c c', S.hf G (v' c) (v' c') = if c = c' then 1 else 0 := fun c c' => by
      rw [hv'_def, S.hf_ins, hvo]
    have hv's : ∑ c, vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) = G := by
      apply S.ext_drop i hai0 hσa _ hGa _ haG
      · intro s t
        rw [Matrix.sum_apply]
        conv_rhs => rw [← submatrix_apply G i.succAbove i.succAbove s t, ← hvs, Matrix.sum_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [vecMulVec_apply, hv'_def, S.cv_ins, mulVec_ins, vecMul_ins]
      · rw [sum_mulVec']
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [vecMulVec_mulVec, ← dotProduct_mulVec, hGa, dotProduct_zero, op_smul_eq_smul, zero_smul]
      · rw [vecMul_sum']
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [vecMul_vecMulVec, dotProduct_mulVec, haG, zero_dotProduct, zero_smul]
    refine ⟨k + 1, Fin.cons a (fun c => S.proj Γ a (v' c)), ?_, ?_, ?_⟩
    · intro c
      refine Fin.cases ?_ (fun c => ?_) c
      · simpa using ha
      · simpa using S.IntV_proj hΓ ha (hv'I c)
    · intro c c'
      refine Fin.cases ?_ (fun c => ?_) c <;> refine Fin.cases ?_ (fun c' => ?_) c'
      · simpa using haa
      · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_self_proj haa]
        rw [if_neg (Fin.succ_ne_zero c').symm]
      · simp only [Fin.cons_zero, Fin.cons_succ, S.hf_proj_self hΓ hH ha haa (hv'I c)]
        rw [if_neg (Fin.succ_ne_zero c)]
      · simp only [Fin.cons_succ, S.hf_proj_proj haa, Fin.succ_inj]
        exact hv'o c c'
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have : ∀ c, vecMulVec (Γ *ᵥ S.proj Γ a (v' c)) (S.cv (S.proj Γ a (v' c)) ᵥ* Γ)
          = vecMulVec (G *ᵥ v' c) (S.cv (v' c) ᵥ* G) := fun c => by
        rw [S.mulVec_proj, S.vecMul_proj hΓ hH ha (hv'I c)]
      rw [Finset.sum_congr rfl (fun c _ => this c), hv's, hG_def, Γp]
      abel

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
