import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FlatGenInjective
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BilLActRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigDirInt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDir

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartAct

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart GlobalTheory.LawLog

theorem logOf_eq {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} (G : Germ.FGLaw k d) (i : Fin d) :
    GlobalTheory.FormalLog.logOf G i = ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i := rfl

theorem subst_act_log {k O : Type} [CommRing k] [Algebra ℚ k] [CommRing O] {d : ℕ} (G : Germ.FGLaw k d)
    (A : Germ.OAct O G) (a : O) (b : Fin d) :
    subst (fun i => subst (oneVar k d) (A.act a i)) (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G b)) =
      ∑ j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a b) •
        (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G j) : MvPowerSeries (Fin d) k) := by
  rw [subst_oneVar _ cc_oneVar _ (A.const a), logOf_eq, GlobalTheory.TwistCheck.log_act, ← coe_substAlgHom hs_oneVar, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem isIntHom_actX_and_eigen (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (a : 𝓞 E) :
    IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧
      ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  refine ⟨⟨fun b => ?_, fun b α => ?_, fun b => ?_⟩, fun ℓ => ?_⟩
  · refine constantCoeff_subst_eq_zero hs_oneVar cc_oneVar ?_
    rw [constantCoeff_map, (GlobalTheory.IntChartCheck.const_zero Ch).2 a b, map_zero]
  · have e : actX Ch X a b = map (jX X) (subst (oneVar T.V _) (Ch.actT a b)) := by
      rw [actX, map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact isIntV_jX X _
  · let _ := io.toAlgebra
    let A : Germ.OAct (𝓞 E) (lawX Ch X) := GlobalTheory.FBMap.mapAct X.ιF Ch.ch.B.A
    have hA : ∀ i, A.act a i = map (jX X) (Ch.actT a i) := fun i => by
      show map X.ιF (Ch.ch.B.A.act a i) = _
      rw [Ch.gen.1.2.1 a i, jX, map_comp]; rfl
    have h := subst_act_log (lawX Ch X) A a b
    simp only [hA, coeff_map] at h
    exact h
  · obtain ⟨χ, hχ⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir.exists_char c T io ℓ.1
    have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a (χ a) (hχ a)
    have hz : embX io X ℓ.1 a = jX X (χ a) := by
      rw [jX, RingHom.comp_apply, hχ]; rfl
    funext i
    have h2 := congrArg (jX X) (congrFun h i)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply, smul_eq_mul] at h2
    rw [hz]
    simpa only [Matrix.mulVec, dotProduct, tanX, lieVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] using h2

end GlobalTheory.ChartAct
