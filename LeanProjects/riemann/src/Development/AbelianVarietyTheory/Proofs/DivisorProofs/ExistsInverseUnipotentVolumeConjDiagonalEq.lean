import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLColumnCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLRowCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.DiagVol

section Main
variable {K₀ : Type} [Field K₀] {ι : Type} [Fintype ι] [DecidableEq ι]

def unipSub (ℓ : ι → ℕ) : Subgroup (GL ι K₀) where
  carrier := {g | ∀ r s, ℓ s ≤ ℓ r → g.val r s = (1 : Matrix ι ι K₀) r s}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    have tri : b.val.BlockTriangular ℓ := fun i j h => by
      rw [hb i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * b.val) r s = ((1 : Matrix ι ι K₀) * b.val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.val_mul, this, Matrix.one_mul, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have tri : (a⁻¹).val.BlockTriangular ℓ := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular fun i j h => by
        rw [ha i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * (a⁻¹).val) r s = ((1 : Matrix ι ι K₀) * (a⁻¹).val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.mul_inv, Matrix.one_mul] at this
    exact this.symm
end Main

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem symN_le_unipSub {F : Type} [Field F] : symN F n c ≤ unipSub (ordL c) := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [Model.mem_N_iff] at hx <;>
    intro r s hrs <;> refine hx r s ?_ <;>
    rcases r with r | r <;> rcases s with s | s <;> simp only [ordL, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

theorem conj_diag_mem {F : Type} [Field F] (d : n ⊕ Fin c → Fˣ) {x : GL (n ⊕ Fin c) F} (hx : x ∈ symN F n c) :
    diagGL d * x * (diagGL d)⁻¹ ∈ symN F n c := by
  have key : ∀ p, ∀ y ∈ N F n c p, diagGL d * y * (diagGL d)⁻¹ ∈ N F n c p := by
    intro p y hy
    rw [Model.mem_N_iff] at hy ⊢
    intro r s h
    have e : ((diagGL d)⁻¹).val = Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F) := rfl
    rw [Units.val_mul, Units.val_mul, e, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul, hy r s h]
    by_cases hrs : r = s
    · subst hrs; simp
    · simp [Matrix.one_apply_ne hrs]
  have h : symN F n c ≤ (symN F n c).comap (MulAut.conj (diagGL d)).toMonoidHom :=
    sup_le (fun v hv => Subgroup.mem_sup_left (by simpa using key _ v hv))
      fun v hv => Subgroup.mem_sup_right (by simpa using key _ v hv)
  simpa using h hx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem invVol_diag_one (ϖ : kˣ) (hϖ : IsUnif ϖ) (t : n ⊕ Fin c) :
    ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) =
      (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by
  set g := diagGL (Pi.mulSingle t ϖ) with hg
  set K := KO k (n ⊕ Fin c)
  set C := K.map (MulAut.conj g).toMonoidHom with hC
  set Sout := Finset.univ.filter (fun s : n ⊕ Fin c => ordL c t < ordL c s)
  set Sin := Finset.univ.filter (fun r : n ⊕ Fin c => ordL c r < ordL c t)
  have hU : ∀ x ∈ symN k n c ⊓ K, ∀ r s, ordL c s ≤ ordL c r → x.val r s = (1 : Matrix _ _ k) r s :=
    fun x hx => symN_le_unipSub (Subgroup.mem_inf.1 hx).1

  have hnum : C.relIndex (symN k n c ⊓ K) = resCard k ^ Sout.card := by
    refine GlobalTheory.T.relIndex_conj_integralGL_row_congruence ϖ hϖ t Sout (by simp [Sout]) _ inf_le_right (fun x hx s hs => ?_) (fun y hy h0 => ?_)
    · exact hU x hx t s (by simpa [Sout] using hs)
    · exact GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL t y hy fun s hs => h0 s (by simpa [Sout] using hs)

  have hden : K.relIndex (symN k n c ⊓ C) = resCard k ^ Sin.card := by
    set φ := (MulAut.conj g⁻¹).toMonoidHom
    have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective
    have hCφ : C.map φ = K := by
      rw [hC, Subgroup.map_map]
      conv_rhs => rw [← Subgroup.map_id K]
      congr 1
      ext x; simp [φ, mul_assoc]
    have hNφ : (symN k n c).map φ = symN k n c := by
      have hgi : g⁻¹ = diagGL (Pi.mulSingle t ϖ)⁻¹ := Units.ext rfl
      refine le_antisymm ?_ fun x hx => ?_
      · rintro _ ⟨x, hx, rfl⟩
        simpa [φ, hgi] using conj_diag_mem (Pi.mulSingle t ϖ)⁻¹ hx
      · refine ⟨g * x * g⁻¹, conj_diag_mem _ hx, ?_⟩
        simp [φ, mul_assoc]
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.map_inf_eq _ _ _ hφ, hNφ, hCφ]
    refine GlobalTheory.T.relIndex_conj_integralGL_column_congruence ϖ hϖ t Sin (by simp [Sin]) _ inf_le_right (fun x hx r hr => ?_) (fun y hy h0 => ?_)
    · exact hU x hx r t (by simpa [Sin] using hr)
    · exact GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL t y hy fun r hr => h0 r (by simpa [Sin] using hr)
  have hq : (0 : ℚ) < resCard k := by
    have : 1 < resCard k := Finite.one_lt_card
    exact_mod_cast this.trans' one_pos
  refine ⟨(Sout.card : ℤ) - Sin.card, ?_, ?_⟩
  · rw [invVol, hnum, hden, zpow_sub₀ hq.ne']
    push_cast; rfl
  · have h1 : Sout.card ≤ Fintype.card (n ⊕ Fin c) := Finset.card_le_univ _
    have h2 : Sin.card ≤ Fintype.card (n ⊕ Fin c) := Finset.card_le_univ _
    rw [abs_le]; constructor <;> omega

end GlobalTheory.DiagVol
