import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor

noncomputable section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRat

theorem exists_proj (K' : Subfield ℂ) : ∃ φ : ℂ →ₗ[K'] ℂ, (∀ x : K', φ x = x) ∧ ∀ x, φ x ∈ K' := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K' ℂ)
    (LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K' ℂ))
  refine ⟨(Algebra.linearMap K' ℂ).comp g, fun x => ?_, fun x => (g x).2⟩
  have h := congrArg (fun f => f x) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  show algebraMap K' ℂ (g (Algebra.linearMap K' ℂ x)) = algebraMap K' ℂ x
  rw [h]

theorem val_eq_sum_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (v : VV ℂ lam) :
    v.1 = ∑ a, (bVV ℂ lam).repr v a • bVVfun ℂ lam a := by
  conv_lhs => rw [← (bVV ℂ lam).sum_repr v]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, bVV_coe]

theorem coeff_mem_of_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ a, (bVV ℂ lam).repr v a ∈ Set.range κ) (m : ι × Fin n × Fin n →₀ ℕ) :
    coeff m v.1 ∈ Set.range κ := by
  rw [val_eq_sum_repr, coeff_sum, ← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun a _ => ?_
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
  rw [coeff_smul, hP, coeff_map, smul_eq_mul]
  obtain ⟨x, hx⟩ := h a
  exact ⟨x * P.coeff m, by simp [hx]⟩

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem repr_mem_of_coeff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ m, coeff m v.1 ∈ Set.range κ) (a : VVIdx lam) :
    (bVV ℂ lam).repr v a ∈ Set.range κ := by
  set K' := κ.fieldRange
  obtain ⟨φ, hφ1, hφ2⟩ := exists_proj K'
  set c := fun a => (bVV ℂ lam).repr v a
  have hK : ∀ a m, coeff m (bVVfun ℂ lam a) ∈ K' := fun a m => by
    obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
    rw [hP, coeff_map]
    exact ⟨((coeff m P : ℤ) : L), by simp⟩
  have key : ∑ b, (c b - φ (c b)) • bVVfun ℂ lam b = 0 := by
    ext m
    have e1 : coeff m v.1 = ∑ b, c b * coeff m (bVVfun ℂ lam b) := by
      rw [val_eq_sum_repr, coeff_sum]; simp [c]
    have e2 : φ (coeff m v.1) = coeff m v.1 := hφ1 ⟨_, RingHom.mem_fieldRange.2 (h m)⟩
    have e3 : φ (coeff m v.1) = ∑ b, φ (c b) * coeff m (bVVfun ℂ lam b) := by
      rw [e1, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : c b * coeff m (bVVfun ℂ lam b) = (⟨_, hK b m⟩ : K') • c b := by
        rw [Subfield.smul_def, smul_eq_mul, mul_comm]
      rw [this, map_smul, Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [coeff_sum, coeff_zero]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e3, e2, sub_self]
  have hz := Fintype.linearIndependent_iff.1 (bVVfun_spec ℂ lam).1 _ key a
  rw [sub_eq_zero] at hz
  have hc : c a ∈ K' := by rw [hz]; exact hφ2 _
  exact RingHom.mem_fieldRange.1 hc

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem coeff_map_mem {ι : Type} [Fintype ι] {n n' : ℕ} {σ : ι → Formalism.BasicNotions.DomWeight n} {σ' : ι → Formalism.BasicNotions.DomWeight n'} {L : Type} [Field L] (κ : L →+* ℂ)
    (f : VV ℂ σ →ₗ[ℂ] VV ℂ σ') (hf : ∀ a b, (bVV ℂ σ').repr (f (bVV ℂ σ b)) a ∈ Set.range κ) (v : VV ℂ σ)
    (hv : ∀ m, coeff m v.1 ∈ Set.range κ) (m : ι × Fin n' × Fin n' →₀ ℕ) : coeff m (f v).1 ∈ Set.range κ := by
  refine coeff_mem_of_repr σ' κ _ (fun a => ?_) m
  have e : f v = ∑ b, (bVV ℂ σ).repr v b • f (bVV ℂ σ b) := by
    conv_lhs => rw [← (bVV ℂ σ).sum_repr v]
    simp only [map_sum, map_smul]
  rw [e]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun b _ => ?_
  exact Subfield.mul_mem _ (RingHom.mem_fieldRange.2 (repr_mem_of_coeff σ κ v hv b)) (RingHom.mem_fieldRange.2 (hf a b))

end GlobalTheory.RowRat

end
