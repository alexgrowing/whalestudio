import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OrthIsom

open scoped TensorProduct

theorem mul_inv_mem_UJ {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R)
    (β β' : GL (Fin n) R) (h : Formalism.UG.cT σ β'.1 * J * β'.1 = Formalism.UG.cT σ β.1 * J * β.1) :
    β' * β⁻¹ ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1 = J
  calc Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1
      = Formalism.UG.cT σ (β⁻¹).1 * (Formalism.UG.cT σ β'.1 * J * β'.1) * (β⁻¹).1 := by
        rw [Units.val_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1) := by
        rw [h, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_iff_of_frames {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β β' : GL (Fin n) R)
    (H H' : Set (Fin n → R)) (h : ∀ y, y ∈ H ↔ ∀ i, ((β⁻¹).val *ᵥ y) i ∈ S)
    (h' : ∀ y, y ∈ H' ↔ ∀ i, ((β'⁻¹).val *ᵥ y) i ∈ S) (y : Fin n → R) :
    y ∈ H ↔ (β' * β⁻¹).val *ᵥ y ∈ H' := by
  rw [h, h', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (R : Type) [CommRing R] [Algebra F R]

theorem swap_symm_mem_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (E ⊗[F] R)) (hg : g ∈ Formalism.UG.UPts σ J R) :
    Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g ∈ HR R σ J := by
  have h := Formalism.UG.Final.BCMem _ _ (Fin n) (Formalism.UG.sigR σ R) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)
    (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom
    (RingHom.ext fun x => ?_) (J.map (Formalism.UG.inclE R)) g hg
  · exact h
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x => rfl

theorem swap_mulVec (g : GL (Fin n) (E ⊗[F] R)) (z : Fin n → R ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F R E
      (((Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g).val *ᵥ z) i)) =
      g.val *ᵥ fun i => Algebra.TensorProduct.comm F R E (z i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (Algebra.TensorProduct.comm F R E).apply_symm_apply (g.val i j)

end Alg

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_latHat_iff_swap (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → Af F ⊗[F] E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ z, fun h => ?_⟩
  have h1 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h
  simp only [AlgEquiv.symm_apply_apply] at h1
  exact h1

theorem exists_of_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (g : GL (Fin n) (E ⊗[F] Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Af F))
    (h : ∀ y, y ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ g.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ') :
    ∃ b ∈ HR (Af F) σ J, ∀ w : Fin n → Af F ⊗[F] E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔ b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ' : Set (Fin n → E)) := by
  refine ⟨_, swap_symm_mem_HR (Af F) σ J g hg, fun w => ?_⟩
  rw [mem_latHat_iff_swap, mem_latHat_iff_swap, swap_mulVec]
  exact h _

end Swap

theorem exists_unitary_latHat : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)),
    IsSelfDualC A L → IsSelfDualC A L' →
    ∃ b ∈ HR (Af D.host.F) D.sp.cm.sig A.gram, ∀ w : Fin A.rank → TensorProduct D.host.F (Af D.host.F) D.host.E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L : Set (Fin A.rank → D.host.E)) ↔
        b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L' : Set (Fin A.rank → D.host.E)) := by
  intro D A L L' hL hL'
  obtain ⟨β, e, hβ⟩ := GlobalTheory.AdIsom.exists_orth hL
  obtain ⟨β', e', hβ'⟩ := GlobalTheory.AdIsom.exists_orth hL'
  refine exists_of_swap D.sp.cm.sig A.gram L L' (β' * β⁻¹) (mul_inv_mem_UJ _ _ β β' (hβ'.trans hβ.symm)) ?_
  rw [e, e']
  exact mem_iff_of_frames (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) β β' _ _ (GlobalTheory.AdIsom.mem_hat_lat β) (GlobalTheory.AdIsom.mem_hat_lat β')

end GlobalTheory.Core.Rk.OrthIsom
