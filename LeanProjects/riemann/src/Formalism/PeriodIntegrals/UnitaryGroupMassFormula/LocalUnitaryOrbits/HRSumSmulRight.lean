import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem oEv_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at *
  rw [SetLike.mem_coe] at *
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨e, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨f, -, rfl⟩ := hb
      rw [← map_mul]
      exact Submodule.subset_span ⟨e * f, Set.mem_univ _, by simp⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add b c _ _ hb hc =>
      rw [mul_add]
      exact Submodule.add_mem _ hb hc
    | smul r b _ hb =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hb
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add a c _ _ ha hc =>
    rw [add_mul]
    exact Submodule.add_mem _ ha hc
  | smul r a _ ha =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r ha

theorem oEv_sum {ι : Type} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ i ∈ s, f i ∈ OEv (E := E) v) :
    ∑ i ∈ s, f i ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.sum_mem _ h

theorem hR_sum_smul_right {a : ℕ} (x : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (y : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ k, c k • y k) = ∑ k, c k * hR (Fv F v) σ J x (y k) := by
  have := map_sum (PI.VolStabSW.hLin (Fv F v) σ J x) (fun k => c k • y k) Finset.univ
  simp only [map_smul, smul_eq_mul] at this
  exact this

theorem hR_smul_left' (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_smul_left {a : ℕ} (y : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (x : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (∑ k, c k • x k) y = ∑ k, sigR (Fv F v) σ (c k) * hR (Fv F v) σ J (x k) y := by
  have := map_sum (AddMonoidHom.mk' (fun z => hR (Fv F v) σ J z y) (fun z z' => hR_add_left σ J z z' y))
    (fun k => c k • x k) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun k _ => hR_smul_left' σ J v (c k) (x k) y

section Onto

variable (Λ : Set (Fin n → E)) (ψ : AddChar (AF F) ℂ)

def GramInvO (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ y ∈ LamT v Λ a,
    (∀ i j, gramR (Fv F v) σ J y i j - gramR (Fv F v) σ J Y i j ∈ PO (E := E) v ϖ) →
    ∃ Ginv : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), (∀ i j, Ginv i j ∈ OEv (E := E) v) ∧
      gramR (Fv F v) σ J y * Ginv = 1

def TrOnto : Prop :=
  UnramAt (E := E) v → ∀ s ∈ OEv (E := E) v, sigR (Fv F v) σ s = s →
    ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = s

theorem hensOnto_of (a : ℕ) (Y : TupV (E := E) v n a) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v) :
    HensOnto σ J v Λ ψ a Y := by
  classical
  intro hGood ϖ hϖ y hy hyT S hS
  obtain ⟨Ginv, hGi, hGG⟩ := hGI hGood ϖ hϖ y hy hyT
  obtain ⟨L, -, hLΛ⟩ := hGood.2.1
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hGood.1.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hGood.1.2.1.1
  have hdiag : ∀ i, ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = (S : Matrix (Fin a) (Fin a) _) i i :=
    fun i => hTr hGood.2.2.2.1 _ (hS i i) (S.2 i i)
  choose x hx hxs using hdiag
  set A : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then (S : Matrix (Fin a) (Fin a) _) i j else if i = j then x i else 0 with hAdef
  have hA : ∀ i j, A i j ∈ OEv (E := E) v := by
    intro i j
    simp only [hAdef]
    split_ifs
    · exact hS i j
    · exact hx i
    · exact oEv_zero v
  have hAS : ∀ i j, A i j + sigR (Fv F v) σ (A j i) = (S : Matrix (Fin a) (Fin a) _) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hAdef, h, not_lt.2 h.le, h.ne']
    · simp [hAdef, hxs]
    · simp only [hAdef, h, not_lt.2 h.le, h.ne, h.ne', if_false, if_true, zero_add]
      exact S.2 i j
  set C := Ginv * A with hCdef
  have hC : ∀ i j, C i j ∈ OEv (E := E) v := fun i j => by
    rw [hCdef, Matrix.mul_apply]
    exact oEv_sum v _ _ fun k _ => oEv_mul v (hGi i k) (hA k j)
  have hGm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ y
  subst hLΛ
  refine ⟨fun j => ∑ k, C k j • y k, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => oEv_smul_mem v L (hC k j) (hy k)
  · funext i j
    simp only [crossM]
    rw [hR_sum_smul_right, hR_sum_smul_left]
    have e1 : ∑ k, C k j * hR (Fv F v) σ J (y i) (y k) = A i j := by
      have : (gramR (Fv F v) σ J y * C) i j = A i j := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      rw [← this, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have e2 : ∑ k, sigR (Fv F v) σ (C k i) * hR (Fv F v) σ J (y k) (y j) = sigR (Fv F v) σ (A j i) := by
      have : (gramR (Fv F v) σ J y * C) j i = A j i := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      rw [← this, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, mul_comm]
      congr 1
      exact (hGm k j).symm
    rw [e1, e2, hAS]

end Onto

end PI.OmLocU
