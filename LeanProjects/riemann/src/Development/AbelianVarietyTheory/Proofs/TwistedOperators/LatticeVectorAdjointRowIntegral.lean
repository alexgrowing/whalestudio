import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftedTensorLatticePartMemLiftGroupPoints
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftDat

theorem rowAdj_isIntM_of_mem : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2P e he a k₀ hab hmov hgen h1 h2 h3 h4 v hv
  rcases Nat.eq_zero_or_pos T.rank with h0 | hpos
  · intro i j; exact absurd j.2 (by omega)
  have hS : 0 < S.rank := lt_of_lt_of_le hpos hn
  let i0 : Fin S.rank := ⟨0, hS⟩
  let y : Matrix (Fin S.rank) (Fin T.rank) D.host.E := vecMulVec (Pi.single i0 1) v
  have hy : y ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    AddSubgroup.subset_closure ⟨_, Submodule.subset_span ⟨i0, rfl⟩, v, hv, rfl⟩
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hfin : finPart D (cA D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hce])
  have hA : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) C.X.Λ :=
    fun o z hz => GlobalTheory.LiftLevel.smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have h0 : finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]; exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hy
  have hx : cA D e • finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) :=
    GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hfin h0
  have hhalf : IsHalf (cA D e) (cA D e • finW S T y) := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hce]
  have hint := ((hgen _ hhalf).1).2 hx
  have hM : ∀ N : Matrix (Fin S.rank) (Fin T.rank) (EAf D),
      HMul.hMul βS.val (HMul.hMul (HMul.hMul (βS⁻¹).val N) βT.val) = HMul.hMul N βT.val := by
    intro N
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, βS.mul_inv, Matrix.one_mul]
  have key : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e v 0 j =
      GlobalTheory.LiftLevel.adjA S T βS βT a (cA D e • finW S T y) i0 j := by
    intro j
    simp only [GlobalTheory.LiftLevel.adjA, frMapAdj]
    rw [hM]
    simp only [GlobalTheory.LiftDat.rowAdj, Matrix.smul_apply, C.m.gS, inv_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, finW, y, vecMulVec_apply, Pi.single_eq_same, one_mul, i0]
  intro i j
  rw [Fin.fin_one_eq_zero i, key]
  exact hint i0 j

end GlobalTheory.LiftDat

end
