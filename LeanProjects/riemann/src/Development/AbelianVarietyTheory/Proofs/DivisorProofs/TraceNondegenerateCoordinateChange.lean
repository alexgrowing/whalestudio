import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.SubintCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finiteDimensional_of_numberField : FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem trace_inclR_mul [FiniteDimensional F E] (c : E) (y : AE F E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) c * y) =
      ∑ i, algebraMap F (AF F) (Algebra.trace F E (c * Module.finBasis F E i)) *
        (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr y i := by
  set b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]
  congr 1
  have hb : b i = inclR (F := F) (AF F) (Module.finBasis F E i) := by
    simp [b, Algebra.TensorProduct.basis_apply]; rfl
  rw [hb, ← map_mul, GlobalTheory.VacIndic.trace_inclR]

def coordEquiv (n : ℕ) [FiniteDimensional F E] :
    (Fin n → AE F E) ≃ₜ+ (Fin n × Fin (Module.finrank F E) → AF F) :=
  let L : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin (Module.finrank F E) → AF F) :=
    (LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun).trans
      (LinearEquiv.curry (AF F) (AF F) (Fin n) (Fin (Module.finrank F E))).symm
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  { toAddEquiv := L.toAddEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }

def coordMat {n : ℕ} {κ κa κb : Type} (ε : κ ≃ κa ⊕ (κb ⊕ κb)) (C : Matrix κa (Fin n) E) :
    Matrix κ ((Fin n × Fin (Module.finrank F E)) ⊕ κb) F := fun k' x =>
  Sum.elim (fun k => Sum.elim (fun p : Fin n × Fin (Module.finrank F E) =>
      Algebra.trace F E (C k p.1 * Module.finBasis F E p.2)) fun _ => 0)
    (fun w => Sum.elim (fun _ => 0) fun b => if Sum.elim id id w = b then 1 else 0) (ε k') x

theorem coordMat_mulVec_inl {n : ℕ} {κ κa κb : Type} [Fintype κb] (ε : κ ≃ κa ⊕ (κb ⊕ κb))
    (C : Matrix κa (Fin n) E) {R : Type} [CommRing R] [Algebra F R] (z : ((Fin n × Fin (Module.finrank F E)) ⊕ κb) → R)
    (k : κa) :
    ((coordMat ε C).map (algebraMap F R) *ᵥ z) (ε.symm (.inl k)) =
      ∑ p : Fin n × Fin (Module.finrank F E),
        algebraMap F R (Algebra.trace F E (C k p.1 * Module.finBasis F E p.2)) * z (.inl p) := by
  simp [Matrix.mulVec, dotProduct, coordMat, Fintype.sum_sum_type]

theorem coordMat_mulVec_inr {n : ℕ} {κ κa κb : Type} [Fintype κb] (ε : κ ≃ κa ⊕ (κb ⊕ κb))
    (C : Matrix κa (Fin n) E) {R : Type} [CommRing R] [Algebra F R] (z : ((Fin n × Fin (Module.finrank F E)) ⊕ κb) → R)
    (w : κb ⊕ κb) :
    ((coordMat ε C).map (algebraMap F R) *ᵥ z) (ε.symm (.inr w)) = z (.inr (Sum.elim id id w)) := by
  simp [Matrix.mulVec, dotProduct, coordMat, Fintype.sum_sum_type]

theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (κ κa κb : Type) [Fintype κ] [Fintype κa] [Fintype κb] (ε : κ ≃ κa ⊕ (κb ⊕ κb)) (C : Matrix κa (Fin n) E),
    (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) →
    ∃ (D : Matrix κ ((Fin n × Fin (Module.finrank F E)) ⊕ κb) F)
      (h : (Fin n → AE F E) ≃ₜ+ (Fin n × Fin (Module.finrank F E) → AF F)),
      (∀ z, D *ᵥ z = 0 → z = 0) ∧ ∀ (y : Fin n → AE F E) (u : κb → AF F),
        GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) (Sum.elim u u) =
          D.map (algebraMap F (AF F)) *ᵥ Sum.elim (h y) u := by
  intro F E _ _ _ _ _ n κ κa κb _ _ _ ε C hC
  haveI : FiniteDimensional F E := finiteDimensional_of_numberField
  refine ⟨coordMat ε C, coordEquiv n, fun z hz => ?_, fun y u => ?_⟩
  · have hm : (coordMat ε C).map (algebraMap F F) = coordMat ε C := by ext; simp
    rw [← hm] at hz
    have hr : ∀ b, z (.inr b) = 0 := fun b => by
      have := congrFun hz (ε.symm (.inr (.inl b)))
      rw [coordMat_mulVec_inr] at this
      simpa using this
    have hl : ∀ k, ∑ p : Fin n × Fin (Module.finrank F E),
        Algebra.trace F E (C k p.1 * Module.finBasis F E p.2) * z (.inl p) = 0 := fun k => by
      have := congrFun hz (ε.symm (.inl k))
      rw [coordMat_mulVec_inl] at this
      simpa using this
    set w : Fin n → E := fun j => ∑ i, z (.inl (j, i)) • Module.finBasis F E i
    have hw : w = 0 := hC w fun k => by
      rw [← hl k, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [w, Finset.mul_sum, map_sum, mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]
    have hz' : ∀ j i, z (.inl (j, i)) = 0 := fun j i => by
      have h0 : ∑ i, z (.inl (j, i)) • Module.finBasis F E i = 0 := congrFun hw j
      exact Fintype.linearIndependent_iff.mp (Module.finBasis F E).linearIndependent (fun i => z (.inl (j, i))) h0 i
    funext x
    rcases x with ⟨j, i⟩ | b
    · exact hz' j i
    · exact hr b
  · funext k'
    obtain ⟨k', rfl⟩ := ε.symm.surjective k'
    rcases k' with k | w
    · rw [GlobalTheory.ThK.Adapt.glue_inl, coordMat_mulVec_inl, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [trace_inclR_mul]
      rfl
    · rw [GlobalTheory.ThK.Adapt.glue_inr, coordMat_mulVec_inr]
      rcases w with b | b <;> rfl

end GlobalTheory.SubintCoords
