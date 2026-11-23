import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDat

theorem frMapAdj_partAt_actO_finW : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) = Matrix.of fun i j => GlobalTheory.LiftDat.rowAdj T βT a e (y i) 0 j := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2 e he a k₀ hab hmov hgen h1 h2' h3 h4 y
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hp : ∀ (c : AE D) (z : WO S T), GlobalTheory.LiftLevel.partAt c z = c • z := fun c z => by
    ext i j; simp [GlobalTheory.LiftLevel.partAt, smul_eq_mul]
  have hcomm : GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) =
      actO S T k₀ 1 (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := by
    rw [hp, hp]
    show _ = HMul.hMul (HMul.hMul (mt T 1) ((cA D e • finW S T y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S k₀⁻¹)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hx : IsHalf (cA D e) (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [GlobalTheory.LiftLevel.partAt, Matrix.map_apply, ← mul_assoc, hcc]
  rw [hcomm, hmov.2.2 _ hx]
  unfold GlobalTheory.LiftLevel.adjA frMapAdj
  rw [C.m.gS]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hi : ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E)⁻¹).map (incA D) = 1 := by
    rw [inv_one]; exact Matrix.map_one (incA D) (map_zero _) (map_one _)
  rw [hi, Matrix.one_mul]
  ext i j
  simp only [rowAdj, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    GlobalTheory.LiftLevel.partAt, finW]

end GlobalTheory.LiftDat
