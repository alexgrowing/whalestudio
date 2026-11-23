import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
import Formalism.LocalRingCardinality.SpanPowerMembership.UnitDivisorGood

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)

theorem labelIdempotent_ne_one (ht : THyp H) : e0L H Lb what₂ h ℂ ≠ 1 := by
  intro e1
  let b : ∀ kv : Ix (ndG H Lb what₂ h), Fin R.r → ZMod (H.g kv.1) := fun kv => fun i => (Lb.fA kv.1).coeff i
  have hm : ∀ k, Formalism.CyclotomicNorms.monicOf (fun i : Fin R.r => (Lb.fA k).coeff i) = Lb.fA k := fun k =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (Lb.okA k).1 (Lb.okA k).2.1
  have hS : ¬ GoodT (ndG H Lb what₂ h) (fun k v => Formalism.CyclotomicNorms.monicOf (b ⟨k, v⟩)) := by
    intro hg
    have := (hg 0).1
    simp only [b, hm] at this
    exact ND.not_isGood_const _ _ this
  have hmul := eSum_mul_tens (I := Ix (ndG H Lb what₂ h)) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf a))
    (fun a => GoodT (ndG H Lb what₂ h) fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))
    (fun kv l => esZ_idem _) (fun kv l l' hl => esZ_orth _ _ (monicOf_injective.ne hl)) b
  rw [if_neg hS] at hmul
  have hne : tens (fun kv : Ix (ndG H Lb what₂ h) => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) ≠ 0 :=
    tens_ne_zero _ fun kv => by
      show esZ ℂ _ (Lb.fA kv.1) (Lb.fB kv.1) (Formalism.CyclotomicNorms.monicOf fun i : Fin R.r => (Lb.fA kv.1).coeff i) ≠ 0
      rw [hm]
      unfold esZ
      rw [if_pos rfl]
      exact one_sub_eT_ne_zero (zL H kv.1) (zL_ne_one H ht kv.1)
  apply hne
  have : e0L H Lb what₂ h ℂ = eSum (I := Ix (ndG H Lb what₂ h)) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
      (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => esL Lb ℂ kv.1 (Formalism.CyclotomicNorms.monicOf a))
      (fun a => GoodT (ndG H Lb what₂ h) fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := rfl
  rw [← this, e1, one_mul] at hmul
  exact hmul

theorem one_sub_e0L_mem_center :
    1 - e0L H Lb what₂ h ℂ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) :=
  Subalgebra.sub_mem _ (Subalgebra.one_mem _) (labelIdempotent_mem_center H Lb what₂ h)

def labelComplementCharacter (ht : THyp H) : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h))) →ₐ[ℂ] ℂ :=
  (exists_char _ (one_sub_e0L_mem_center H Lb what₂ h)
    (by rw [sub_mul, mul_sub, mul_sub, labelIdempotent_idem, one_mul, one_mul, mul_one, sub_self, sub_zero])
    (sub_ne_zero.mpr (labelIdempotent_ne_one H Lb what₂ h ht).symm)).choose

theorem labelComplementCharacter_idempotent_zero (ht : THyp H) : labelComplementCharacter H Lb what₂ h ht ⟨e0L H Lb what₂ h ℂ, labelIdempotent_mem_center H Lb what₂ h⟩ = 0 := by
  have h1 : labelComplementCharacter H Lb what₂ h ht ⟨1 - e0L H Lb what₂ h ℂ, one_sub_e0L_mem_center H Lb what₂ h⟩ = 1 :=
    (exists_char _ (one_sub_e0L_mem_center H Lb what₂ h)
      (by rw [sub_mul, mul_sub, mul_sub, labelIdempotent_idem, one_mul, one_mul, mul_one, sub_self, sub_zero])
      (sub_ne_zero.mpr (labelIdempotent_ne_one H Lb what₂ h ht).symm)).choose_spec
  have e : (⟨1 - e0L H Lb what₂ h ℂ, one_sub_e0L_mem_center H Lb what₂ h⟩ :
      Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb what₂ h)))) = 1 - ⟨_, labelIdempotent_mem_center H Lb what₂ h⟩ := rfl
  rw [e, map_sub, map_one] at h1
  linear_combination -h1

end Formalism.BasicNotions.Examples₂.NZ
