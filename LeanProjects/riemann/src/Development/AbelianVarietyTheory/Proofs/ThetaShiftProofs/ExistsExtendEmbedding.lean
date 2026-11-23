import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobiStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobiStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem exists_extend_embedding {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (σ : F →+* ℂ) : ∃ em : K →+* ℂ, em.comp (algebraMap F K) = σ := by
  letI : Algebra F ℂ := σ.toAlgebra
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let f : K →ₐ[F] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩

theorem killQ_of_gamAt : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → KillQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hm K₁ _ _ _ d hd F hF
  have key : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      (∀ k, rdU (T.U j σ) F.1 k ∈ ((T.U j σ).X k).SSgt (laU (T.U j σ) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) →
      cfOf d.yF d.μ d.jj F.1 = 0 := by
    intro σ hσ hr
    obtain ⟨em, rfl⟩ := exists_extend_embedding (K := K₁) σ
    have hc : F.1 ∈ T.C j ka := cutR_le T.C j ka F.2
    exact GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ em _
      (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n hd hσ (h.unf j hj _ hσ) (dom_wtA ka)
      (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ (T.Q.Xo j) T.Q.c _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n
        (hG j hj _ hσ) (h.chiTriv j hj _ hσ _ _ (dom_wtA ka))) F.1 hc.1 hr
  exact key T.σ₀ T.good_σ₀ ((GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hm F).2.1 hF)

end GlobalTheory.ArcCM
