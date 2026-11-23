import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.DetRootRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_baseRing_of_conjugation_fixed_tensor {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (htr : ∀ x, ∃ t, algebraMap F E t = x + σ x) (y : R ⊗[F] E) (hy : sigR R σ y = y) :
    ∃ a : R, algebraMap R (R ⊗[F] E) a = y := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + sigR R σ z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      have : sigR R σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
      rw [this, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [hy] at ht
  show ((2 : F)⁻¹ • t) ⊗ₜ (1 : E) = y
  rw [← TensorProduct.smul_tmul', ← ht, ← two_smul F y, smul_smul]
  norm_num

theorem sigR_algebraMap {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (a : R) : sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  show a ⊗ₜ σ 1 = a ⊗ₜ 1
  rw [map_one]

theorem det_bc {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    (Formalism.UG.bc φ g).1.det = φ g.1.det := by
  rw [RingHom.map_det]; rfl

theorem inclR_injective {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] : Function.Injective (inclR (F := F) (E := E) R) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective

theorem fixed_mem_range (y : AE D) (hy : cA D y = y) : ∃ a, algebraMap (AF D.host.F) (AE D) a = y :=
  exists_baseRing_of_conjugation_fixed_tensor D.sp.cm.sig
    (fun x => (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])) y hy

theorem fixed_iff_idF (y : (AE D)ˣ) : cA D (y : AE D) = y ↔ ∃ a, idF D a = y := by
  constructor
  · intro hy
    have hy' : cA D ((y⁻¹ : (AE D)ˣ) : AE D) = (y⁻¹ : (AE D)ˣ) := by
      have h1 : cA D (y : AE D) * cA D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [hy] at h1
      exact (Units.inv_eq_of_mul_eq_one_right h1).symm
    obtain ⟨a, ha⟩ := fixed_mem_range _ hy
    obtain ⟨b, hb⟩ := fixed_mem_range _ hy'
    have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
      Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
    have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
    exact ⟨Units.mkOfMulEqOne a b hab, Units.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact sigR_algebraMap D.sp.cm.sig (a : AF D.host.F)

end GlobalTheory.DetRootRows
