import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem deRham_invariants_coord_finrank :
    ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV hL hfin hrk Φ hΦ
  haveI := PD.finK
  let D : Submodule K (Fin d → BdR) :=
    { carrier := {y | ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec
          (fun i => PD.actdR g (y i)) = y}
      add_mem' := by
        intro a b ha hb g
        have : (fun i => PD.actdR g ((a + b) i)) =
            (fun i => PD.actdR g (a i)) + (fun i => PD.actdR g (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, ha g, hb g]
      zero_mem' := by
        intro g
        have : (fun i => PD.actdR g ((0 : Fin d → BdR) i)) = 0 := by
          funext i; simp
        rw [this, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha g
        have : (fun i => PD.actdR g ((c • a) i)) = c • (fun i => PD.actdR g (a i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_smul, ha g] }
  have hmem : ∀ z, z ∈ DdR PD ρ ↔ Φ z ∈ D := by
    intro z
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← hΦ g z]
    exact Φ.injective.eq_iff.symm
  let e : ↥(DdR PD ρ) ≃ₗ[Qp] ↥D :=
    { toFun := fun z => ⟨Φ z.1, (hmem _).1 z.2⟩
      invFun := fun y => ⟨Φ.symm y.1, (hmem _).2 (by simpa using y.2)⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp)
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  haveI : Module.Finite Qp ↥(DdR PD ρ) := Module.Finite.trans LL _
  haveI : Module.Finite Qp ↥D := Module.Finite.equiv e
  refine ⟨D, fun y => Iff.rfl, Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K ↥D
  have h2 := Module.finrank_mul_finrank Qp LL ↥(DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  have h4 : Module.finrank Qp V = d := by simpa using Module.finrank_eq_card_basis bV
  have h5 := e.finrank_eq
  have hpos : 0 < Module.finrank Qp K := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h5, ← h2, hrk, ← h4, ← h3]
  ring

end GlobalTheory
