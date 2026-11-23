import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Divisibility.BrJoint
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeEmbeddedLastCoordinateSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateSubstLinearEquivSymmMemNablaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfLastCoordinateExtensionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairLocal

theorem finLocal : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  have hLlat : Submodule.IsLattice E L := GlobalTheory.T.isLattice_of_lastCoordinate_extension hN M L hM hL
  have h1 := GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr E K ι N emb Λ L hLlat w u hu
  obtain ⟨s, hs, hsu⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h1
  have hdel : delAtr emb Λ L = delK Λ (fun τ => Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) (1 : K)) := by
    unfold delAtr
    congr 1
    funext τ
    exact GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum emb hN M L hL τ
  rw [hdel] at hsu
  have h2 := GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs K ι N n hN Λ σ hI hS
    (fun τ => dualFr (tauLat emb τ M)) (fun _ => 1) (fun _ => one_ne_zero) _ hsu
  have hbr : Formalism.L2.Col.Br.brAt hN Λ σ (fun _ => (1 : K)) = Formalism.L2.Col.Br.brStd hN Λ σ := by
    simp [Formalism.L2.Col.Br.brAt]
  rw [hbr] at h2
  have hy := GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla emb σ M hM v hv
  have h3 := ((Formalism.L2.DIV.pairBDual E K ι n emb σ M hM _).1.1 h2) _ hy
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
  have key : (s : K) * (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) *
      GlobalTheory.BrPairF.brPairF σ hN Λ u v = (r : K) := by
    have e1 : (r : K) = algebraMap (𝓞 K) K r := rfl
    rw [e1, hr, GlobalTheory.BrPairF.brPairF_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply,
      Algebra.smul_def, Algebra.smul_def, map_pow, map_natCast, mul_assoc]
  by_cases hP : GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0
  · exact Or.inl hP
  right
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact w.asIdeal.zero_mem
  have hp0 : (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Formalism.EigenvalueLevelCeiling.plc_prime w).ne_zero)
  have h4 := Formalism.DivisionValues.ReductionFirst.vw_int_nonneg w r
  rw [← key, Formalism.DivisionValues.ReductionFirst.vw_mul w (mul_ne_zero hs0 hp0) hP, Formalism.DivisionValues.ReductionFirst.vw_mul w hs0 hp0,
    Formalism.DivisionValues.ReductionFirst.vw_unit w s hs] at h4
  linarith

end GlobalTheory.BrPairLocal
