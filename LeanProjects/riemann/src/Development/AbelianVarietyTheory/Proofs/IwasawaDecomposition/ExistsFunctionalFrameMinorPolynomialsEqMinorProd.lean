import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BideterminantFunctionsOfShape
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

namespace GlobalTheory.Mem.RangeMinors

theorem exists_dual_sum_smul_eq {V ι : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] (n : ι → V) (J₀ : ι) :
    ∃ ψ : Module.Dual ℚ V, ∑ J, ψ (n J) • n J = n J₀ := by
  let T : Module.Dual ℚ V →ₗ[ℚ] V :=
    { toFun := fun ψ => ∑ J, ψ (n J) • n J
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.smul_sum, mul_smul] }
  by_contra h
  have hn : n J₀ ∉ LinearMap.range T := fun ⟨ψ, hψ⟩ => h ⟨ψ, hψ⟩
  obtain ⟨φ, hφ, hbot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have h0 : φ (T φ) = 0 := by
    have : φ (T φ) ∈ (LinearMap.range T).map φ := Submodule.mem_map_of_mem ⟨φ, rfl⟩
    rw [hbot] at this
    simpa using this
  have h1 : ∑ J, φ (n J) * φ (n J) = 0 := by
    simpa [T, map_sum] using h0
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun J _ => mul_self_nonneg (φ (n J)))).1 h1 J₀ (Finset.mem_univ _)
  exact hφ (mul_self_eq_zero.1 h2)

theorem exists_dual_baseChange {σ : Type} (k : Type) [Field k] [CharZero k] (ψ : Module.Dual ℚ (MvPolynomial σ ℚ)) :
    ∃ ph : Module.Dual k (MvPolynomial σ k),
      ∀ F : MvPolynomial σ ℚ, ph (MvPolynomial.map (algebraMap ℚ k) F) = algebraMap ℚ k (ψ F) := by
  refine ⟨(MvPolynomial.basisMonomials σ k).constr k fun m => algebraMap ℚ k (ψ (MvPolynomial.monomial m 1)), fun F => ?_⟩
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have e1 : (MvPolynomial.monomial m a : MvPolynomial σ ℚ) = a • MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have e2 : MvPolynomial.map (algebraMap ℚ k) (MvPolynomial.monomial m a : MvPolynomial σ ℚ) =
        algebraMap ℚ k a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.map_monomial, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e2, map_smul, Module.Basis.constr_basis]
    conv_rhs => rw [e1, map_smul, smul_eq_mul, map_mul]
    rw [smul_eq_mul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

theorem eval_nablaX_eq_minY {Lt k : Type} [Fintype Lt] [DecidableEq Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram)
    (J : KM.ColChoice N nu) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial.eval (fun v : Lt × ℕ × Fin N => y v.1 v.2.2 v.2.1)
      (MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J)) = GL3Columns.minY N nu J y := by
  unfold KM.nablaX GL3Columns.minY
  simp only [map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp

theorem exists_dual_DeX_eq_minY : ∀ (D : D7) (k : Type) [Field k] [CharZero k] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (J : KM.ColChoice N nu), ∃ ph : Module.Dual k (MvPolynomial ((Bool × Formalism.MainNotions.G.HH D) × ℕ × Fin N) k),
      ∀ y : Bool × Formalism.MainNotions.G.HH D → Fin N → ℕ → k, ph (GL3Columns.DeX N nu y) = GL3Columns.minY N nu J y := by
  intro D k _ _ N nu J₀
  classical
  haveI : Finite (KM.ColChoice N nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N nu) := Fintype.ofFinite _
  obtain ⟨ψ, hψ⟩ := exists_dual_sum_smul_eq
    (fun J : KM.ColChoice N nu => MvPolynomial.map (Int.castRingHom ℚ) (KM.nablaX N nu J)) J₀
  obtain ⟨ph, hph⟩ := exists_dual_baseChange k ψ
  have hm : ∀ J : KM.ColChoice N nu, MvPolynomial.map (algebraMap ℚ k)
      (MvPolynomial.map (Int.castRingHom ℚ) (KM.nablaX N nu J)) =
      MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J) := fun J => by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  refine ⟨ph, fun y => ?_⟩
  rw [GL3Columns.wwCB_holds D k N nu y, finsum_eq_sum_of_fintype, map_sum]
  have h := congrArg (fun F => MvPolynomial.eval (fun v : (Bool × Formalism.MainNotions.G.HH D) × ℕ × Fin N => y v.1 v.2.2 v.2.1)
    (MvPolynomial.map (algebraMap ℚ k) F)) hψ
  simp only [map_sum] at h
  rw [hm, eval_nablaX_eq_minY] at h
  rw [← h]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, ← hm, hph, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_mul,
    MvPolynomial.eval_C, hm, eval_nablaX_eq_minY, smul_eq_mul, mul_comm]

end GlobalTheory.Mem.RangeMinors
