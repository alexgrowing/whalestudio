import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FinPartLat

open scoped TensorProduct Matrix
open IsDedekindDomain

def incF (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) LinearMap.id

def prF (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E :=
  Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

theorem prF_incF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (t : Af F ⊗[F] E) :
    prF F E (incF F E t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht]

def inrA {F : Type} [Field F] [NumberField F] (a : Af F) : AF F := LinearMap.inr F (Ainf F) (Af F) a

theorem smul_incV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (a : AF F) (x : Fin n → E) (i : Fin n) : (a • GlobalTheory.ThK.incV F x) i = a ⊗ₜ[F] x i := by
  show a • (Algebra.TensorProduct.includeRight (x i) : AF F ⊗[F] E) = _
  rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem incF_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (X : Spc F E n) (y : Fin n → Af F ⊗[F] E) (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E))) :
    (fun i => incF F E (y i)) ∈ GlobalTheory.ThK.latHat X := by
  have hle : Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) ≤
      (GlobalTheory.ThK.latHat X).comap ((incF F E).compLeft (Fin n)).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨inrA a, ?_, fun v => ha v, x, hx, ?_⟩
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
      exact map_zero _
    · funext i
      rw [smul_incV]
      rfl
  exact hle hy

theorem prF_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (X : Spc F E n) (z : Fin n → AF F ⊗[F] E) (hz : z ∈ GlobalTheory.ThK.latHat X) :
    (fun i => prF F E (z i)) ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  have hle : GlobalTheory.ThK.latHat X ≤ (Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E))).comap
      ((prF F E).toLinearMap.compLeft (Fin n)).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, -, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨sndA F a, fun v => ha v, x, hx, ?_⟩
    funext i
    show prF F E ((a • GlobalTheory.ThK.incV F x) i) = _
    rw [smul_incV]
    rfl
  exact hle hz

theorem finite_part : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (m : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)),
    (∀ z ∈ GlobalTheory.ThK.latHat X, m.mulVec z ∈ GlobalTheory.ThK.latHat X) →
    ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)),
      (m.map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E))).mulVec y ∈
        Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n X m hm y hy
  have h := prF_mem X _ (hm _ (incF_mem X y hy))
  convert h using 1
  funext i
  have e := RingHom.map_mulVec (prF F E).toRingHom m (fun j => incF F E (y j)) i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [e]
  congr 1
  funext j
  exact (prF_incF (y j)).symm

end GlobalTheory.FinPartLat
