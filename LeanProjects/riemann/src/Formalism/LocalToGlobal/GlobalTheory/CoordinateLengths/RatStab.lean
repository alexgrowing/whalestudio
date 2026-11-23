import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.IntSpanLeRat
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Formalism.LocalToGlobal.GlobalTheory.GL6.WeylLengthDiagonalUnitUniformiser
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

theorem ratInC_holds (D : D7) (u : D.what₂.Word) : RatInC D u := by
  intro P hP
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, fun τ => Formalism.L2.G.Model.sw_weyl_map (Int.castRingHom ℂ) le_rfl _ _ (hf τ), rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

def ratO (D : D7) : Subring ℂ := D.what₂.embLL.range

section Diag

variable (D : D7) {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν)
include hν

theorem rat_diag_step (j : Fin N) (t : ℂ) (ht : t ∈ ratO D) (ht0 : t ≠ 0) (q : MvPolynomial (Fin N × Fin N) ℂ)
    (hq : q ∈ bwA_span (ratO D) le_rfl ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal (Function.update 1 j t)) q ∈ bwA_span (ratO D) le_rfl ν := by
  obtain ⟨x, rfl⟩ := RingHom.mem_range.1 ht
  have hp : (D.what₂.embLL x)⁻¹ ∈ ratO D := ⟨x⁻¹, map_inv₀ _ _⟩
  have h := bwA_span_diag (ratO D) le_rfl ν hν j.pos j (D.what₂.embLL x)⁻¹ hp (inv_ne_zero ht0) q hq
  rw [inv_inv] at h
  have e : Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal (Function.update 1 j (D.what₂.embLL x))) q =
      (⟨D.what₂.embLL x ^ ν ⟨0, j.pos⟩, pow_mem ht _⟩ : ratO D) •
        ((D.what₂.embLL x)⁻¹ ^ ν ⟨0, j.pos⟩ • Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal (Function.update 1 j (D.what₂.embLL x))) q) := by
    show _ = (D.what₂.embLL x ^ ν ⟨0, j.pos⟩ : ℂ) • ((D.what₂.embLL x)⁻¹ ^ ν ⟨0, j.pos⟩ •
      Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal (Function.update 1 j (D.what₂.embLL x))) q)
    rw [smul_smul, ← mul_pow, mul_inv_cancel₀ ht0, one_pow, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ h

theorem rat_diag (e : Fin N → ℂ) (he : ∀ j, e j ∈ ratO D) (he0 : ∀ j, e j ≠ 0) (q : MvPolynomial (Fin N × Fin N) ℂ)
    (hq : q ∈ bwA_span (ratO D) le_rfl ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal e) q ∈ bwA_span (ratO D) le_rfl ν := by
  classical
  have key : ∀ S : Finset (Fin N), ∀ q, q ∈ bwA_span (ratO D) le_rfl ν →
      Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun j => if j ∈ S then e j else 1) q ∈ bwA_span (ratO D) le_rfl ν := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro q hq
      have h1 : (Matrix.diagonal fun j : Fin N => if j ∈ (∅ : Finset (Fin N)) then e j else 1) = 1 := by
        simp
      rw [h1, bwA_rowAct_one]
      exact hq
    · intro i S hi ih q hq
      have h2 : (Matrix.diagonal fun j : Fin N => if j ∈ insert i S then e j else 1) =
          Matrix.diagonal (Function.update 1 i (e i)) * Matrix.diagonal fun j => if j ∈ S then e j else 1 := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · simp [hj, Function.update_of_ne hj]
      rw [h2, Formalism.UG.P.wact_rowAct_mul, AlgHom.comp_apply]
      exact ih _ (rat_diag_step D ν hν i (e i) (he i) (he0 i) q hq)
  have h3 : (Matrix.diagonal fun j : Fin N => if j ∈ (Finset.univ : Finset (Fin N)) then e j else 1) = Matrix.diagonal e := by
    simp
  rw [← h3]
  exact key Finset.univ q hq

theorem rat_sandwich (K₁ K₂ : Matrix (Fin N) (Fin N) ℂ)
    (h₁ : K₁ ∈ Submonoid.closure {g : Matrix (Fin N) (Fin N) ℂ | ∃ (a b : Fin N) (c : ℂ), c ∈ ratO D ∧ g = 1 + Matrix.single b a c})
    (h₂ : K₂ ∈ Submonoid.closure {g : Matrix (Fin N) (Fin N) ℂ | ∃ (a b : Fin N) (c : ℂ), c ∈ ratO D ∧ g = 1 + Matrix.single b a c})
    (e : Fin N → ℂ) (he : ∀ j, e j ∈ ratO D) (he0 : ∀ j, e j ≠ 0) (q : MvPolynomial (Fin N × Fin N) ℂ)
    (hq : q ∈ bwA_span (ratO D) le_rfl ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (K₁ * Matrix.diagonal e * K₂) q ∈ bwA_span (ratO D) le_rfl ν := by
  have e1 := Formalism.GradedWeylDivisibility.rowActMul ℂ N N K₂ (K₁ * Matrix.diagonal e)
  have e2 := Formalism.GradedWeylDivisibility.rowActMul ℂ N N (Matrix.diagonal e) K₁
  rw [← e1, AlgHom.comp_apply, ← e2, AlgHom.comp_apply]
  exact bwA_span_closure (ratO D) le_rfl ν K₂ h₂ _
    (rat_diag D ν hν e he he0 _ (bwA_span_closure (ratO D) le_rfl ν K₁ h₁ q hq))

theorem rat_rowAct_mem (M : Matrix (Fin N) (Fin N) D.what₂.LL) (hM : M.det ≠ 0) (q : MvPolynomial (Fin N × Fin N) ℂ)
    (hq : q ∈ bwA_span (ratO D) le_rfl ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (M.map D.what₂.embLL) q ∈ bwA_span (ratO D) le_rfl ν := by
  classical
  obtain ⟨L, L', d, hMd⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hdetL : ∀ L : List (Matrix.TransvectionStruct (Fin N) D.what₂.LL),
      (L.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
    intro L
    induction L with
    | nil => simp
    | cons t L ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih, Matrix.TransvectionStruct.det, one_mul]
  have hd : ∀ j, d j ≠ 0 := by
    have h := congrArg Matrix.det hMd
    rw [Matrix.det_mul, Matrix.det_mul, hdetL, hdetL, Matrix.det_diagonal, one_mul, mul_one] at h
    intro j hj
    exact hM (h.trans (Finset.prod_eq_zero (Finset.mem_univ j) hj))
  have hcl : ∀ L : List (Matrix.TransvectionStruct (Fin N) D.what₂.LL),
      (L.map Matrix.TransvectionStruct.toMatrix).prod.map D.what₂.embLL ∈
        Submonoid.closure {g : Matrix (Fin N) (Fin N) ℂ | ∃ (a b : Fin N) (c : ℂ), c ∈ ratO D ∧ g = 1 + Matrix.single b a c} := by
    intro L
    induction L with
    | nil =>
      rw [List.map_nil, List.prod_nil, Matrix.map_one _ (map_zero _) (map_one _)]
      exact Submonoid.one_mem _
    | cons t L ih =>
      rw [List.map_cons, List.prod_cons, Matrix.map_mul]
      refine Submonoid.mul_mem _ (Submonoid.subset_closure ⟨t.j, t.i, D.what₂.embLL t.c, ⟨t.c, rfl⟩, ?_⟩) ih
      ext a b
      simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.map_apply, Matrix.add_apply,
        Matrix.one_apply, Matrix.single_apply]
      split_ifs <;> simp_all
  rw [hMd, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
  exact rat_sandwich D ν hν _ _ (hcl L) (hcl L') _ (fun j => ⟨d j, rfl⟩)
    (fun j => (map_ne_zero D.what₂.embLL).2 (hd j)) q hq

end Diag

theorem rat_ten (D : D7) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (s : Finset D.what₂.Tau) :
    ∀ (g : D.what₂.Tau → MvPolynomial (Fin N × Fin N) ℂ),
      (∀ τ ∈ s, g τ ∈ bwA_span (ratO D) le_rfl (lam τ).natW) →
      (∀ τ ∉ s, ∃ f ∈ delSq ℤ N (lam τ), g τ = MvPolynomial.map (Int.castRingHom ℂ) f) →
      ∀ r : D.what₂.LL, D.what₂.embLL r • Formalism.L2.Forms.ten g ∈ RatSpan D lam := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro g _ h2 r
    choose f hf hg using fun τ => h2 τ (by simp)
    apply AddSubgroup.subset_closure
    exact ⟨r, f, hf, by rw [show g = fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ) from funext hg]⟩
  · intro τv s hτv ih g h1 h2
    have key : ∀ q ∈ bwA_span (ratO D) le_rfl (lam τv).natW, ∀ r : D.what₂.LL,
        D.what₂.embLL r • Formalism.L2.Forms.ten (Function.update g τv q) ∈ RatSpan D lam := by
      intro q hq
      induction hq using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f0, hf0, rfl⟩ := hx
        apply ih
        · intro τ hτ
          have hne : τ ≠ τv := fun h => hτv (h ▸ hτ)
          rw [Function.update_of_ne hne]
          exact h1 τ (Finset.mem_insert_of_mem hτ)
        · intro τ hτ
          by_cases h : τ = τv
          · subst h
            exact ⟨f0, hf0, by rw [Function.update_self]⟩
          · rw [Function.update_of_ne h]
            exact h2 τ (by simp [Finset.mem_insert, h, hτ])
      | zero =>
        intro r
        rw [bwA_ten_update]
        simp
      | add x y _ _ hx hy =>
        intro r
        have e : Formalism.L2.Forms.ten (Function.update g τv (x + y)) = Formalism.L2.Forms.ten (Function.update g τv x) + Formalism.L2.Forms.ten (Function.update g τv y) := by
          rw [bwA_ten_update, bwA_ten_update, bwA_ten_update, map_add, add_mul]
        rw [e, smul_add]
        exact add_mem (hx r) (hy r)
      | smul o x _ hx =>
        intro r
        obtain ⟨r', ho⟩ := RingHom.mem_range.1 o.2
        have e : Formalism.L2.Forms.ten (Function.update g τv (o • x)) = (o : ℂ) • Formalism.L2.Forms.ten (Function.update g τv x) := by
          rw [bwA_ten_update, bwA_ten_update]
          show MvPolynomial.rename _ ((o : ℂ) • x) * _ = _
          rw [map_smul, smul_mul_assoc]
        rw [e, smul_smul, ← ho, ← map_mul]
        exact hx (r * r')
    intro r
    have := key (g τv) (h1 τv (Finset.mem_insert_self _ _)) r
    rwa [Function.update_eq_self] at this

theorem ratGL_holds (D : D7) (u : D.what₂.Word) : RatGL D u := by
  classical
  intro γ P hP
  let o : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    atInf (embT D) ((γ τ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ
  let M : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL := fun τ =>
    ((γ τ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map
      (fun a => D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) a))
  have hoM : ∀ τ, o τ = (M τ).map D.what₂.embLL := fun τ => by
    ext a b
    exact bwA_embT_eq D τ _
  have hMdet : ∀ τ, (M τ).det ≠ 0 := by
    intro τ h
    have hu := Formalism.MainNotions.Ext.Lw.isUnit_atInf (embT D) (γ τ) τ
    apply hu.ne_zero
    show (o τ).det = 0
    rw [hoM τ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  have hc : (∏ τ, (o τ).det ^ shiftOf (lamT u 0) τ) =
      D.what₂.embLL (∏ τ, (M τ).det ^ shiftOf (lamT u 0) τ) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, hoM τ]
  show MvPolynomial.C (∏ τ, (o τ).det ^ shiftOf (lamT u 0) τ) * subP o P ∈ RatSpan D ((D.fm u).lam 0)
  rw [hc, MvPolynomial.C_mul']
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    rw [map_smul, substitution_tensor, smul_smul, ← map_mul]
    apply rat_ten D _ Finset.univ
    · intro τ _
      rw [hoM τ]
      exact rat_rowAct_mem D _ (dominant_natWeight_antitone _) (M τ) (hMdet τ) _ (Submodule.subset_span ⟨f τ, hf τ, rfl⟩)
    · intro τ hτ
      exact absurd (Finset.mem_univ τ) hτ
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end Formalism.L2.GlobalTheoryTheory.LemB

end
