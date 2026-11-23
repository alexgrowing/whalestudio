import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
import Formalism.GradedWeylDivisibility.FinalD
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqCharA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

def sq_ssEquiv (k : ℕ) (ν : Fin k → ℕ) :
    ↥(Formalism.GradedWeylDivisibility.ssIdx k k ν) ≃ sq_SSZ k (fun t => (ν t : ℤ)) :=
  Equiv.subtypeEquiv (Finsupp.equivFunOnFinite.trans (Equiv.curry (Fin k) (Fin k) ℕ)) (by
    intro m
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · have := h1 l j hlj a
        rw [zero_add] at this
        exact this
      · exact congrArg Nat.cast (h2 t)
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · rw [zero_add]
        exact h1 l j hlj a
      · exact Nat.cast_injective (R := ℤ) (h2 t))

theorem sq_wsum_add {n : ℕ} (lam : Fin n → ℤ) (c : ℤ) :
    wsum (fun i => lam i + c) = wsum lam + n * c := by
  simp [wsum, Finset.sum_add_distrib]

def sq_shiftEmb {n : ℕ} (c : ℤ) : (Fin n → ℤ) ↪ (Fin n → ℤ) :=
  ⟨fun mu i => mu i + c, fun x y h => funext fun i => by simpa using congrFun h i⟩

theorem sq_shiftEmb_apply {n : ℕ} (c : ℤ) (mu : Fin n → ℤ) : sq_shiftEmb c mu = fun i => mu i + c := rfl

theorem sq_gt_shift {K : Type*} [Field K] : ∀ (n : ℕ) (lam : Fin n → ℤ) (c : ℤ) (t : Fin n → K),
    (∀ i, t i ≠ 0) → gtChar n (fun i => lam i + c) t = (∏ i, t i) ^ c * gtChar n lam t := by
  intro n
  induction n with
  | zero => intro lam c t _; simp [gtChar]
  | succ n ih =>
    intro lam c t ht
    have himg : interl (fun i => lam i + c) = (interl lam).map (sq_shiftEmb c) := by
      ext mu
      simp only [mem_map, sq_mem_interl, sq_shiftEmb_apply]
      constructor
      · intro h
        refine ⟨fun i => mu i - c, fun i => ⟨by linarith [(h i).1], by linarith [(h i).2]⟩, ?_⟩
        funext i
        ring
      · rintro ⟨a, ha, rfl⟩ i
        exact ⟨by linarith [(ha i).1], by linarith [(ha i).2]⟩
    rw [gtChar, gtChar, himg, sum_map, mul_sum]
    refine sum_congr rfl fun mu _ => ?_
    rw [sq_shiftEmb_apply, ih mu c _ (fun i => ht _), sq_wsum_add, sq_wsum_add, Fin.prod_univ_castSucc, mul_zpow]
    have e : wsum lam + ((n + 1 : ℕ) : ℤ) * c - (wsum mu + (n : ℤ) * c) = (wsum lam - wsum mu) + c := by
      push_cast; ring
    rw [e, zpow_add₀ (ht _)]
    ring

theorem sq_ss_sum {K : Type*} [Field K] (N : ℕ) (ν : Fin N → ℕ) [Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν)]
    (t : Fin N → K) :
    ∑ m : ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν), ∏ a, t a ^ Formalism.GradedWeylDivisibility.rowWt m.1 a = gtChar N (fun i => (ν i : ℤ)) t := by
  have : Fintype (sq_SSZ N (fun i => (ν i : ℤ))) := @Fintype.ofFinite _ (sq_SSZ_finite N _)
  refine (Fintype.sum_equiv (sq_ssEquiv N ν) _ (fun g => sq_mono t g.1) (fun m => rfl)).trans ?_
  exact sq_gt_sum N _ (fun s => Int.natCast_nonneg _) t

theorem sqChar : SqCharStatement := by
  intro N lam g t hg
  classical
  have hdet : (g : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have ht : ∀ a, t a ≠ 0 := by
    intro a h
    rw [hg, Matrix.det_diagonal] at hdet
    exact hdet (Finset.prod_eq_zero (mem_univ a) h)
  obtain ⟨b, ⟨hli, hspan, hhom⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ N N lam.natW
  have : Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N lam.natW).fintype
  let B : Module.Basis ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) ℂ (Formalism.BasicNotions.nablaSq ℂ N lam) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hB : ∀ m, (B m : MvPolynomial (Fin N × Fin N) ℂ) = b m := by
    intro m
    simp only [B, Module.Basis.map_apply, Module.Basis.span_apply]
    rfl
  let c : ℂ := Formalism.BasicNotions.detPow ℂ N g lam.detShift
  let w : ↥(Formalism.GradedWeylDivisibility.ssIdx N N lam.natW) → ℂ := fun m => ∏ a, t a ^ Formalism.GradedWeylDivisibility.rowWt m.1 a
  let f : Formalism.BasicNotions.nablaSq ℂ N lam →ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam := B.constr ℂ (fun m => (c * w m) • B m)
  have hact : ∀ x : MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.BasicNotions.sqAct ℂ N lam g x = c • Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) x := by
    intro x
    simp only [Formalism.BasicNotions.sqAct, hg, Matrix.diagonal_transpose, c]
  refine ⟨f, ?_, ?_⟩
  · have hL : (Formalism.BasicNotions.nablaSq ℂ N lam).subtype ∘ₗ f =
        (c • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal t)).toLinearMap) ∘ₗ
          (Formalism.BasicNotions.nablaSq ℂ N lam).subtype := by
      refine B.ext fun m => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, f, Module.Basis.constr_basis,
        LinearMap.smul_apply, AlgHom.toLinearMap_apply, hB]
      rw [Submodule.coe_smul, hB, Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t (Formalism.GradedWeylDivisibility.rowWt m.1) (b m) (hhom m),
        smul_smul]
    intro x
    rw [hact]
    exact LinearMap.congr_fun hL x
  · rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace]
    have hdiag : ∀ m, Matrix.diag (LinearMap.toMatrix B B f) m = c * w m := by
      intro m
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.constr_basis, map_smul,
        Module.Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    simp only [hdiag, ← Finset.mul_sum]
    rw [sq_ss_sum N lam.natW t]
    have hw : lam.w = fun i => ((lam.natW i : ℕ) : ℤ) + lam.detShift := by
      funext i
      have hle : lam.detShift ≤ lam.w i := by
        have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
        unfold Formalism.BasicNotions.DomWeight.detShift
        rw [dif_pos hN]
        exact lam.anti (by rw [Fin.le_iff_val_le_val]; dsimp only; omega)
      simp only [Formalism.BasicNotions.DomWeight.natW]
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    rw [hw, sq_gt_shift N _ _ t ht]
    congr 1
    simp only [c, Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
      hg, Matrix.det_diagonal]

end ReciprocityTheory.ChartRestriction.TR.Weyl
