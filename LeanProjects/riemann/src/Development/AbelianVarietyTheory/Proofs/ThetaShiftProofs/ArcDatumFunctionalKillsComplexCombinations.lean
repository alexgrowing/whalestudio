import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumCmArcFunctionalVanishesLowFourierJacobiStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFDOfCuspFiniteClaim
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ArcCM

section Free

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ

theorem kill_comb_over (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁]
    [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (σ : c.F →+* ℂ) (hσ : ι.comp (algebraMap c.F K₁) = σ)
    (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ)
    (hg : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hd : Fam n' La c₁ d) (hD : Dom a' n)
    (hP : GlobalTheory.FrameNorm.HasPrinc U l.M)
    (hχ : ∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (Formalism.L2.PjFree.laU U a' n k) gm = 1)
    (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ)
    (hF : ∀ i, F i ∈ sec Xo c a' n)
    (hB : ∀ i k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a' n k) (Formalism.L2.PjFree.rdU U (F i) k))
    (hf : ∀ k, f k ∈ (U.X k).SSgt (Formalism.L2.PjFree.laU U a' n k) c₁)
    (he : ∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * Formalism.L2.PjFree.rdU U (F i) k x) (μ : ArcLt Dw →₀ ℕ) :
    ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  subst hσ
  exact GlobalTheory.T.sum_cmArcFunctional_vanishes_low_fourierJacobi GlobalTheory.ArcCM.known_holds E H Dw l Xo c K₁ d ι r U a' n n' La c₁ hg hU hd hD
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hP hχ) m a F f hF hB hf he μ

end Free

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

theorem kill_comb_rec : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T.toCore j ka CR Tt cc K₁ d → ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (cfOf d.yF d.μ d.jj (F i).1) = 0 := by
  intro D T h j hj ka CR Tt cc K₁ _ _ _ d hd σ₁ hσ m a F f hf he
  exact kill_comb_over _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d σ₁ T.σ₀ hσ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
    (wtA ka) ka.n _ _ _ T.good_σ₀ (h.unf j hj _ T.good_σ₀) hd (dom_wtA ka)
    (GlobalTheory.RunIn.gamAt_of_lawsM D T.toCore h.toLawsCore.toLawsM j hj _ T.good_σ₀)
    (h.chiTriv j hj _ T.good_σ₀ _ _ (dom_wtA ka)) m a (fun i => (F i).1) f
    (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j _ (F i).2))
    (fun i k => ((GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS _ _ _).1
      (((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) _ _ _).1 (cutR_le T.C j _ (F i).2)).2 _ T.good_σ₀) k).1) hf he d.μ

end GlobalTheory.ArcCM
