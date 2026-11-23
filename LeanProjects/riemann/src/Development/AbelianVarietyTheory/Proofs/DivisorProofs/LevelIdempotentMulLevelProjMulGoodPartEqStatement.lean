import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIdempotentMulLevelProjMulGoodPartEq
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelIdempotent_mul_levelProj_mul_goodPart_eq : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ = B.vE ℓ := by
  first | exact @GlobalTheory.GoodPartLevelForms.lvlE_lvlPr_vE | exact GlobalTheory.GoodPartLevelForms.lvlE_lvlPr_vE | (intros; apply GlobalTheory.GoodPartLevelForms.lvlE_lvlPr_vE <;> assumption)
