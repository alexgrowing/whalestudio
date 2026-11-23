import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFrameCongruenceSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_frame_congruence_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ Ψ' : Finset (E →+* ℂ)) (G G' : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (x' : Frame Ψ' r) (p0 : Ψ → ℕ) (p1 : ℕ) (Γ : Subgroup (GL (Fin r) E)), Ψ' = Ψ → G' = -G → (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ τ : Ψ', gram τ.1 G' (mat x' τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) → covolume (inReal Ψ G Γ) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ' G' Γ) (realSU Ψ' G') (riemHaar Ψ' G' x') := by
  first | exact @GlobalTheory.CovolNegFrame.covolume_neg_frame | exact GlobalTheory.CovolNegFrame.covolume_neg_frame | (intros; apply GlobalTheory.CovolNegFrame.covolume_neg_frame <;> assumption)
