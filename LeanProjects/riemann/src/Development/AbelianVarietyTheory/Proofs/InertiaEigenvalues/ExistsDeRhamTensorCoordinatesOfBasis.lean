import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_tensor_coord_of_basis {k V M : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] {d : ℕ} (bV : Module.Basis (Fin d) k V) :
    ∃ Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M), (∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b) ∧
      ∀ z, z = ∑ i, bV i ⊗ₜ[k] Φ z i := by
  classical
  let Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M) :=
    (TensorProduct.congr bV.equivFun (LinearEquiv.refl k M)).trans
      ((TensorProduct.comm k _ _).trans (TensorProduct.piScalarRight k k M (Fin d)))
  have h : ∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b := by
    intro v b i
    simp [Φ]
  refine ⟨Φ, h, fun z => ?_⟩
  apply Φ.injective
  funext j
  rw [map_sum, Finset.sum_apply]
  simp only [h, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Finsupp.single_apply, hij]
  · simp

theorem exists_coord_tensor_dR : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV
  obtain ⟨Φ, h, hz⟩ := exists_tensor_coord_of_basis (M := BdR) bV
  refine ⟨Φ, fun a z => ⟨?_, fun H => ?_⟩, fun g z => ?_⟩
  · rintro ⟨w, rfl⟩ i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [AlgebraTensorModule.map_tmul, h]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ b.2
    | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply]
      exact add_mem hx hy
  · rw [hz z]
    refine Submodule.sum_mem _ fun i _ => ⟨bV i ⊗ₜ ⟨Φ z i, H i⟩, ?_⟩
    rw [AlgebraTensorModule.map_tmul]
    rfl
  · have hact : ∀ (v : V) (b : BdR), actVdR PD ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ PD.actdR g b := by
      intro v b
      unfold actVdR
      rw [AlgebraTensorModule.map_tmul]
      rfl
    funext i
    conv_lhs => rw [hz z]
    rw [map_sum, map_sum, Finset.sum_apply]
    simp only [hact, h, Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.smul_def]

end GlobalTheory
