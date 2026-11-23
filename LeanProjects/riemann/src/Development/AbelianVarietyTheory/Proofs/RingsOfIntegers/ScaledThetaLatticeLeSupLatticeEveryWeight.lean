import Mathlib
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePowerStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightAssemblyClause
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PlaceTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem vLa_int_mul_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (n : ℕ)
    (hs : a * (n : 𝓞 K) ≠ 0) :
    vLa la ((a * (n : 𝓞 K) : 𝓞 K) : K) = vLa la (a : K) + vLa la (n : K) := by
  have ha : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (left_ne_zero_of_mul hs)
  have hn : (n : K) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hs (by simp)
    exact Nat.cast_ne_zero.2 this
  have e : ((a * (n : 𝓞 K) : 𝓞 K) : K) = (a : K) * (n : K) := by
    show algebraMap (𝓞 K) K _ = _
    rw [map_mul, map_natCast]
  rw [e, Crude.crv_vLa_mul la ha hn]

theorem thetaScalar_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ}
    (w : WeightFamilies.Wt D j) : GlobalTheory.RunIn.sOf B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact Nat.cast_ne_zero.2 (D.host.g_prime i).ne_zero
  refine mul_ne_zero ?_ ?_
  · unfold nnW
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))
  · refine Nat.cast_ne_zero.2 ?_
    unfold pPow
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ D.host.hyp.1.ne_zero))
      (pow_ne_zero _ D.host.hyp.2.1.ne_zero)

theorem thInt_of_oriented (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (hO : Oriented T EX) (w : WeightFamilies.Wt D j) :
    GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w := by
  have hs := thetaScalar_ne_zero (recB h.toLawsCore) hinj EX w
  refine Pf.WWc_le_Mlat (recPJ h j hj) _ hs w ?_
  intro G hG la y
  have hG' : G.1 ∈ Submodule.span (𝓞 T.Q.c.F) (T.th j w) := hG
  refine (Pf.le_val_of_mem_span (isVal_vAt (y : T.PtA j la)) (fun g hg => ?_) _ hG').trans
    (recPJ_vAt_inc h j hj la y w G).ge
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (GlobalTheory.T.thetaGenerator_place_valuation_bound D T h j hj hinj EX hO w g hg la y)
  have h1 := GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power D T.Q.c.F la j w _ _ le_rfl le_rfl
  have h2 := vLa_int_mul_natCast (K := T.Q.c.F) la (nnW (recB h.toLawsCore) hinj EX w) _ hs
  have h3 : ((vAdd la ((GlobalTheory.RunIn.sOf (recB h.toLawsCore) hinj EX w : 𝓞 (recB h.toLawsCore).KO) :
      (recB h.toLawsCore).KO) : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) h2
  rw [h3, Int.cast_add]
  exact neg_le_neg ((add_comm _ _).le.trans (add_le_add le_rfl h1))

end GlobalTheory.PlaceTop
