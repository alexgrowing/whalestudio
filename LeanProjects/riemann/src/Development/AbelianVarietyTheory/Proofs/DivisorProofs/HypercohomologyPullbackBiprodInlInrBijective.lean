import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.BiprodCls

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull {K L M : _root_.GlobalTheory.EtC.Cx R} (f : K ⟶ L)
    (g : L ⟶ M) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    _root_.GlobalTheory.EtC.cpull f I n (_root_.GlobalTheory.EtC.cpull g I n x) =
      _root_.GlobalTheory.EtC.cpull (f ≫ g) I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_add {K L : _root_.GlobalTheory.EtC.Cx R} (f g : K ⟶ L)
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (f + g) I n x =
      _root_.GlobalTheory.EtC.cpull f I n x + _root_.GlobalTheory.EtC.cpull g I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.add_comp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_zero {K L : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_zero]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_id {K : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    _root_.GlobalTheory.EtC.cpull (𝟙 K) I n x = x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

end GlobalTheory.EtC.BiprodCls

namespace GlobalTheory.EtC
open BiprodCls

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cpull_biprod_bijective : ∀ (R : Type) [CommRing R]
    (K L I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ),
    Function.Bijective fun x : CohomologyClass (K ⊞ L) I n =>
      (_root_.GlobalTheory.EtC.cpull (biprod.inl : K ⟶ K ⊞ L) I n x,
        _root_.GlobalTheory.EtC.cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  intro R _ K L I n
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => _root_.GlobalTheory.EtC.cpull (biprod.fst : K ⊞ L ⟶ K) I n y.1 +
    _root_.GlobalTheory.EtC.cpull (biprod.snd : K ⊞ L ⟶ L) I n y.2, fun x => ?_, fun y => ?_⟩
  · simp only [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, ← _root_.GlobalTheory.EtC.BiprodCls.cpull_add,
      biprod.total, _root_.GlobalTheory.EtC.BiprodCls.cpull_id]
  · obtain ⟨a, b⟩ := y
    simp only [map_add, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_fst, biprod.inl_snd,
      biprod.inr_fst, biprod.inr_snd, _root_.GlobalTheory.EtC.BiprodCls.cpull_id,
      _root_.GlobalTheory.EtC.BiprodCls.cpull_zero, add_zero, zero_add]

end GlobalTheory.EtC
