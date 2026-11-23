import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LocLevi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatAdapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.CMInst

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermForm_add_right_bis (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_sub_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y - z) = hR R σ J x y - hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hermForm_smul_right_alt (c : R ⊗[F] E) (x y : Fin n → R ⊗[F] E) :
    hR R σ J x (c • y) = c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermForm_sum_right_alt {ι : Type} (s : Finset ι) (d : ι → R ⊗[F] E) (v : ι → Fin n → R ⊗[F] E)
    (x : Fin n → R ⊗[F] E) : hR R σ J x (∑ i ∈ s, d i • v i) = ∑ i ∈ s, d i * hR R σ J x (v i) := by
  classical
  induction s using Finset.induction_on
  · simp only [Finset.sum_empty, hR, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_right_bis, hermForm_smul_right_alt, ih]

theorem conjTensor_incl (a : E) : sigR R σ (inclR R a) = inclR R (σ a) := by
  simp [sigR, inclR]

theorem hermForm_rational_vectors (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  simp [hR, hE, Formalism.UG.hform, ratV, JR, conjTensor_incl, map_sum, map_mul]

theorem mem_tensor_span_iff {r : ℕ} (Y : Fin r → Fin n → E) (y : Fin n → R ⊗[F] E)
    (hy : y ∈ spanR (F := F) R Y Set.univ) : ∃ d : Fin r → R ⊗[F] E, y = ∑ i, d i • ratV (F := F) R (Y i) := by
  simp only [spanR, Set.image_univ] at hy
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, hd⟩ := hy
  exact ⟨d, hd.symm⟩

def WbR {r : ℕ} (P : Frame E n r) (w : Fin n → R ⊗[F] E) : Prop :=
  ∀ i, hR R σ J (ratV (F := F) R (P.e i)) w = 0 ∧ hR R σ J (ratV (F := F) R (P.f i)) w = 0

def WbSub {r : ℕ} (P : Frame E n r) : Submodule (R ⊗[F] E) (Fin n → R ⊗[F] E) where
  carrier := {w | WbR R σ J P w}
  add_mem' := by
    intro a b ha hb i
    rw [hermForm_add_right_bis, hermForm_add_right_bis, (ha i).1, (hb i).1, (ha i).2, (hb i).2]
    simp
  zero_mem' := by
    intro i
    have h := hermForm_smul_right_alt R σ J 0 (ratV (F := F) R (P.e i)) 0
    have h' := hermForm_smul_right_alt R σ J 0 (ratV (F := F) R (P.f i)) 0
    simp only [zero_smul, zero_mul] at h h'
    exact ⟨h, h'⟩
  smul_mem' := by
    intro c w hw i
    rw [hermForm_smul_right_alt, hermForm_smul_right_alt, (hw i).1, (hw i).2]
    simp

variable {R σ J}

theorem witt_decomposition_unique {r : ℕ} (P : Frame E n r) (hee : ∀ a b, hE σ J (P.e a) (P.e b) = 0)
    (hef : ∀ a b, hE σ J (P.e a) (P.f b) = if a = b then 1 else 0)
    (hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if a = b then 1 else 0)
    {x a w b c : Fin n → R ⊗[F] E} (hx : x ∈ spanR (F := F) R P.e Set.univ)
    (ha : a ∈ spanR (F := F) R P.e Set.univ) (hc : c ∈ spanR (F := F) R P.f Set.univ)
    (hw : WbR R σ J P w) (hb : WbR R σ J P b) (h : x + w = a + b + c) : w = b := by
  classical
  have hax : a - x ∈ spanR (F := F) R P.e Set.univ := Submodule.sub_mem _ ha hx
  obtain ⟨g, hg⟩ := mem_tensor_span_iff (R := R) P.e (a - x) hax
  obtain ⟨d, hd⟩ := mem_tensor_span_iff (R := R) P.f c hc
  have hw' : w = a + b + c - x := by
    rw [← h]
    abel
  have hwb : w - b = (a - x) + c := by
    rw [hw']
    abel
  have hd0 : ∀ k, d k = 0 := by
    intro k
    have h1 : hR R σ J (ratV (F := F) R (P.e k)) (w - b) = 0 := by
      rw [hermForm_sub_right, (hw k).1, (hb k).1, sub_self]
    have h2 : hR R σ J (ratV (F := F) R (P.e k)) (a - x) = 0 := by
      rw [hg, hermForm_sum_right_alt]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hermForm_rational_vectors, hee, map_zero, mul_zero]
    have h3 : hR R σ J (ratV (F := F) R (P.e k)) c = d k := by
      rw [hd, hermForm_sum_right_alt, Finset.sum_eq_single k]
      · rw [hermForm_rational_vectors, hef, if_pos rfl, map_one, mul_one]
      · intro i _ hik
        rw [hermForm_rational_vectors, hef, if_neg (Ne.symm hik), map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hwb, hermForm_add_right_bis, h2, h3, zero_add] at h1
    exact h1
  have hc0 : c = 0 := by
    rw [hd]
    exact Finset.sum_eq_zero fun i _ => by rw [hd0 i, zero_smul]
  have hg0 : ∀ k, g k = 0 := by
    intro k
    have h1 : hR R σ J (ratV (F := F) R (P.f k)) (w - b) = 0 := by
      rw [hermForm_sub_right, (hw k).2, (hb k).2, sub_self]
    have h3 : hR R σ J (ratV (F := F) R (P.f k)) (a - x) = g k := by
      rw [hg, hermForm_sum_right_alt, Finset.sum_eq_single k]
      · rw [hermForm_rational_vectors, hfe, if_pos rfl, map_one, mul_one]
      · intro i _ hik
        rw [hermForm_rational_vectors, hfe, if_neg (Ne.symm hik), map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hwb, hc0, add_zero, h3] at h1
    exact h1
  have hax0 : a - x = 0 := by
    rw [hg]
    exact Finset.sum_eq_zero fun i _ => by rw [hg0 i, zero_smul]
  have hwb0 : w - b = 0 := by
    rw [hwb, hax0, hc0, add_zero]
  exact sub_eq_zero.mp hwb0

end Alg

end MassDataLevelSSteps
