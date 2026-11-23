import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientTwistFiltration
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_twist_filtration : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (χ : G →* ℂˣ) (φ : H →* G) (n : ℕ) (S : Fin (n + 1) → Subrepresentation ρ), Monotone S → S 0 = ⊥ →
    S (Fin.last n) = ⊤ → ∀ {W' Vy : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Vy] [Module ℂ Vy]
    (Q : Representation ℂ H W') (Y : Representation ℂ H Vy),
    GlobalTheory.SmGL.IsSubquotient Q ((GlobalTheory.SmGL.twist ρ χ).comp φ) → ∀ F : Q.IntertwiningMap Y, F ≠ 0 →
    ∃ (t : Fin n) (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (Q' : Representation ℂ H V'),
      GlobalTheory.SmGL.IsSubquotient Q' ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)) χ).comp φ) ∧
      ∃ F' : Q'.IntertwiningMap Y, F' ≠ 0 := by
  first | exact @GlobalTheory.SmGL.exists_step_subquotient_ne_zero_of_filtration | exact GlobalTheory.SmGL.exists_step_subquotient_ne_zero_of_filtration | (intros; apply GlobalTheory.SmGL.exists_step_subquotient_ne_zero_of_filtration <;> assumption)
