import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBall
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_twist_coboundary_on_ball : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ) (c : GQ l → Fin r → PadicComplex l) (k : ℕ), CocOn (Gj K m) (twAct act χ i U) (ball l r) c → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ k • c σ) → CobOn (Gj K m) (twAct act χ i U) (ball l r) (fun σ => (l : PadicComplex l) ^ (1 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • c σ) := by
  first | exact @GlobalTheory.Cyc.FrameTorsion.torsion_killed | exact GlobalTheory.Cyc.FrameTorsion.torsion_killed | (intros; apply GlobalTheory.Cyc.FrameTorsion.torsion_killed <;> assumption)
