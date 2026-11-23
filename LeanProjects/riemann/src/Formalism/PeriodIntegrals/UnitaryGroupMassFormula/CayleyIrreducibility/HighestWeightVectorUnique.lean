import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivClosedOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLine
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas

noncomputable section

namespace Formalism.L2.SG.Pf.ColDictValCPf

open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial

section Common

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem natW_anti_v (lam : DomWeight n) : Antitone lam.natW := by
  unfold DomWeight.natW
  intro a b hab
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.2 hab) _)

theorem delSq_le_dual (lam : DomWeight n) : delSq ℂ n lam ≤ dualWeyl ℂ n n lam.natW :=
  weylLeDual_of highestWeightVectorMem dualWeylModuleRowDividedPowerStable ℂ n n le_rfl _ (natW_anti_v lam)

theorem eval_tenV (x : ι × Fin n × Fin n → ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    eval x (tenV f) = ∏ τ, eval (fun p => x (τ, p)) (f τ) := by
  simp only [tenV, map_prod, MvPolynomial.eval_rename, Function.comp_def]

theorem eval_hw_id (ν : Fin n → ℕ) : eval (idPoint ℂ n n) (hw ℂ (le_refl n) ν) = 1 := by
  simp only [hw, map_prod, map_pow, eval_idPoint_lpMinor, one_pow, Finset.prod_const_one]

def sl (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun v => if v.1 = τ₀ then X v.2 else C (x v)

theorem eval_sl (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) (y : Fin n × Fin n → ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval y (sl τ₀ x P) = eval (fun v => if v.1 = τ₀ then y v.2 else x v) P := by
  have h : (MvPolynomial.aeval y).comp (sl τ₀ x) =
      MvPolynomial.aeval (fun v => if v.1 = τ₀ then y v.2 else x v) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [sl, AlgHom.comp_apply, MvPolynomial.aeval_X]
    split_ifs <;> simp
  have h2 := DFunLike.congr_fun h P
  simp only [AlgHom.comp_apply] at h2
  exact h2

theorem sl_rename_self (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    sl τ₀ x (rename (Prod.mk τ₀) p) = p := by
  have h : (sl τ₀ x).comp (rename (Prod.mk τ₀)) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [sl]
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun h p

theorem sl_rename_ne (τ₀ σ : ι) (h : σ ≠ τ₀) (x : ι × Fin n × Fin n → ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) :
    sl τ₀ x (rename (Prod.mk σ) p) = C (eval (fun q => x (σ, q)) p) := by
  have h : (sl τ₀ x).comp (rename (Prod.mk σ)) =
      (Algebra.ofId ℂ (MvPolynomial (Fin n × Fin n) ℂ)).comp (MvPolynomial.aeval fun q => x (σ, q)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [sl, h, MvPolynomial.algebraMap_eq]
  have h2 := DFunLike.congr_fun h p
  simp only [AlgHom.comp_apply, Algebra.ofId_apply, MvPolynomial.algebraMap_eq] at h2
  exact h2

theorem sl_tenV (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    sl τ₀ x (tenV f) = C (∏ σ ∈ Finset.univ.erase τ₀, eval (fun q => x (σ, q)) (f σ)) * f τ₀ := by
  rw [tenV, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀), sl_rename_self, mul_comm,
    map_prod]
  congr 1
  refine Finset.prod_congr rfl fun σ hσ => ?_
  exact sl_rename_ne τ₀ σ (Finset.ne_of_mem_erase hσ) x (f σ)

theorem sl_mem (lam : ι → DomWeight n) (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ)
    {Q : MvPolynomial (ι × Fin n × Fin n) ℂ} (hQ : Q ∈ CSpanV lam) :
    sl τ₀ x Q ∈ delSq ℂ n (lam τ₀) := by
  simp only [CSpanV, delSq] at hQ ⊢
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    rw [sl_tenV, MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (hf τ₀)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P R _ _ hP hR => rw [map_add]; exact Submodule.add_mem _ hP hR
  | smul c P _ hP => rw [map_smul]; exact Submodule.smul_mem _ c hP

theorem rowGen_sl (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) (a b : Fin n) :
    (rowGen ℂ a b).comp (sl τ₀ x) = (Polynomial.mapAlgHom (sl τ₀ x)).comp (bigGen τ₀ a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  obtain ⟨σ, r, c⟩ := v
  by_cases hσ : σ = τ₀
  · subst hσ
    by_cases hb : r = b <;> simp [rowGen, bigGen, sl, hb]
  · simp [rowGen, bigGen, sl, hσ, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem rowDiv_sl (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ) (a b : Fin n) (k : ℕ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    rowDiv ℂ a b k (sl τ₀ x P) = sl τ₀ x (bigDiv τ₀ a b k P) := by
  simp only [rowDiv, bigDiv]
  have h := DFunLike.congr_fun (rowGen_sl τ₀ x a b) P
  simp only [AlgHom.comp_apply] at h
  rw [h]
  exact Polynomial.coeff_map _ _

end Common

section UniqPf

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem uniq_block (lam : ι → DomWeight n) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : Q ∈ CSpanV lam)
    (hk : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0) (τ₀ : ι)
    (x : ι × Fin n × Fin n → ℂ) :
    eval x Q = eval (fun p => x (τ₀, p)) (extremal ℂ n (lam τ₀)) *
      eval (fun v => if v.1 = τ₀ then idPoint ℂ n n v.2 else x v) Q := by
  obtain ⟨c, hc⟩ := highest_weight_line ℂ n n le_rfl (lam τ₀).natW (natW_anti_v _) (sl τ₀ x Q)
    (delSq_le_dual _ (sl_mem lam τ₀ x hQ))
    (fun a b hab k hk1 => by rw [rowDiv_sl, hk τ₀ a b hab k hk1, map_zero])
  have h1 := congrArg (eval (fun p => x (τ₀, p))) hc
  have h2 := congrArg (eval (idPoint ℂ n n)) hc
  rw [eval_sl, smul_eval] at h1 h2
  rw [eval_hw_id, mul_one] at h2
  have hx : (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then x (τ₀, v.2) else x v) = x := by
    funext v
    split_ifs with h
    · rw [← h]
    · rfl
  rw [hx] at h1
  rw [h1, ← h2, mul_comm]
  rfl

theorem uniq_iter (lam : ι → DomWeight n) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : Q ∈ CSpanV lam)
    (hk : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0) (s : Finset ι) :
    ∀ x : ι × Fin n × Fin n → ℂ, eval x Q =
      (∏ τ ∈ s, eval (fun p => x (τ, p)) (extremal ℂ n (lam τ))) *
        eval (fun v => if v.1 ∈ s then idPoint ℂ n n v.2 else x v) Q := by
  induction s using Finset.induction_on with
  | empty => intro x; simp
  | @insert τ s hτ ih =>
    intro x
    have hb : eval (fun v : ι × Fin n × Fin n => if v.1 ∈ s then idPoint ℂ n n v.2 else x v) Q =
        eval (fun p => x (τ, p)) (extremal ℂ n (lam τ)) *
          eval (fun v : ι × Fin n × Fin n => if v.1 ∈ insert τ s then idPoint ℂ n n v.2 else x v) Q := by
      convert (uniq_block lam Q hQ hk τ (fun v => if v.1 ∈ s then idPoint ℂ n n v.2 else x v)) using 4
      · funext p; simp [hτ]
      · funext v; by_cases h1 : v.1 = τ <;> simp [h1]
    rw [ih x, hb, Finset.prod_insert hτ]
    ring

theorem highest_weight_vector_unique : Uniq := by
  unfold Uniq
  intro ι _ _ n lam Q hQ hk
  refine ⟨eval (fun v : ι × Fin n × Fin n => idPoint ℂ n n v.2) Q, ?_⟩
  apply MvPolynomial.funext
  intro x
  rw [uniq_iter lam Q hQ hk Finset.univ x, MvPolynomial.smul_eval]
  simp only [tenHW, eval_tenV, Finset.mem_univ, if_true]
  ring

end UniqPf

section GenPf

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem tenV_update (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ : ι)
    (p : MvPolynomial (Fin n × Fin n) ℂ) :
    tenV (Function.update f τ p) =
      rename (Prod.mk τ) p * ∏ σ ∈ Finset.univ.erase τ, rename (Prod.mk σ) (f σ) := by
  rw [tenV, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun σ hσ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]

theorem bigGen_rename_self (τ : ι) (a b : Fin n) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    bigGen τ a b (rename (Prod.mk τ) p) = Polynomial.map (rename (R := ℂ) (Prod.mk τ)).toRingHom (rowGen ℂ a b p) := by
  have h' : (bigGen τ a b).comp (rename (Prod.mk τ)) =
      (Polynomial.mapAlgHom (rename (R := ℂ) (Prod.mk τ))).comp (rowGen ℂ a b) := by
    apply MvPolynomial.algHom_ext
    intro q
    by_cases hb : q.1 = b <;> simp [bigGen, rowGen, hb]
  have h2 := DFunLike.congr_fun h' p
  simp only [AlgHom.comp_apply] at h2
  exact h2

theorem bigGen_rename_ne (τ σ : ι) (h : σ ≠ τ) (a b : Fin n) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    bigGen τ a b (rename (Prod.mk σ) p) = Polynomial.C (rename (Prod.mk σ) p) := by
  have h' : (bigGen τ a b).comp (rename (Prod.mk σ)) = Polynomial.CAlgHom.comp (rename (R := ℂ) (Prod.mk σ)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [bigGen, h]
  have h2 := DFunLike.congr_fun h' p
  simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply] at h2
  exact h2

theorem bigDiv_tenV_update (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ : ι) (a b : Fin n) (k : ℕ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) :
    bigDiv τ a b k (tenV (Function.update f τ p)) =
      tenV (Function.update f τ (rowDiv ℂ a b k p)) := by
  simp only [bigDiv, rowDiv]
  rw [tenV_update, tenV_update, map_mul, map_prod, bigGen_rename_self,
    Finset.prod_congr rfl (fun σ hσ => bigGen_rename_ne τ σ (Finset.ne_of_mem_erase hσ) a b (f σ)),
    ← map_prod Polynomial.C, Polynomial.coeff_mul_C, Polynomial.coeff_map]
  rfl

theorem generation_holds : Gen := by
  intro ι _ _ n lam M hM hT
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have key : ∀ s : Finset ι, ∀ f : ι → MvPolynomial (Fin n × Fin n) ℂ,
      (∀ τ ∈ s, f τ ∈ delSq ℂ n (lam τ)) → (∀ τ ∉ s, f τ = extremal ℂ n (lam τ)) → tenV f ∈ M := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro f _ h0
      have : f = fun τ => extremal ℂ n (lam τ) := funext fun τ => h0 τ (Finset.notMem_empty τ)
      rw [this]
      exact hT
    · intro τ₀ s hτ ih f h1 h0
      have hword : ∀ wd : List (Fin n × Fin n × ℕ),
          tenV (Function.update f τ₀ (applyWord ℂ wd (hw ℂ le_rfl (lam τ₀).natW))) ∈ M := by
        intro wd
        induction wd with
        | nil =>
          apply ih
          · intro τ hτs
            rw [Function.update_of_ne (fun e => hτ (by rw [← e]; exact hτs))]
            exact h1 τ (Finset.mem_insert_of_mem hτs)
          · intro τ hτs
            by_cases e : τ = τ₀
            · rw [e, Function.update_self]
              rfl
            · rw [Function.update_of_ne e]
              exact h0 τ (by simp [e, hτs])
        | cons y wd ihw =>
          show tenV (Function.update f τ₀ (rowDiv ℂ y.1 y.2.1 y.2.2 (applyWord ℂ wd _))) ∈ M
          rw [← bigDiv_tenV_update]
          exact hM τ₀ _ _ _ _ ihw
      have hspan : f τ₀ ∈ Submodule.span ℂ
          (Set.range fun wd : List (Fin n × Fin n × ℕ) => applyWord ℂ wd (hw ℂ le_rfl (lam τ₀).natW)) :=
        h1 τ₀ (Finset.mem_insert_self _ _)
      have hmem : tenV (Function.update f τ₀ (f τ₀)) ∈ M := by
        refine Submodule.span_induction (p := fun p _ => tenV (Function.update f τ₀ p) ∈ M)
          ?_ ?_ ?_ ?_ hspan
        · rintro _ ⟨wd, rfl⟩
          exact hword wd
        · rw [tenV_update, map_zero, zero_mul]
          exact M.zero_mem
        · intro p q _ _ hp hq
          rw [tenV_update] at hp hq ⊢
          rw [map_add, add_mul]
          exact M.add_mem hp hq
        · intro c p _ hp
          rw [tenV_update] at hp ⊢
          rw [map_smul, smul_mul_assoc]
          exact M.smul_mem c hp
      rwa [Function.update_eq_self] at hmem
  exact key Finset.univ f (fun τ _ => hf τ) (fun τ h => absurd (Finset.mem_univ τ) h)

end GenPf

end Formalism.L2.SG.Pf.ColDictValCPf
