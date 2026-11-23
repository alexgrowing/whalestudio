import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitSmall
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplit
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LengthQuotientEqLengthH0
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMemSupport
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PointSecsLenSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem CycleSplit.Small.exists_residue {S : Type u} [CommRing S] {R : Type w} [CommRing R] [Algebra S R]
    (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type w) (_ : Field K) (_ : Algebra S K) (ψ : R →ₐ[S] K), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom S (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ S P), ?_⟩
  ext a
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.coe_toAlgHom',
    ← map_zero (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))),
    (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))).eq_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem CycleSplit.Small.proof (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hPt : CycleSplit.PointSecs.Statement.{u, w}) : CycleSplit.Small.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M 𝔪 _ pp hpp hhom hle _ hdim
  by_cases hrel : ∃ j, (X j : Poly S N) ∉ pp
  swap
  · push Not at hrel
    exact Eventually.of_forall fun c => by
      rw [interSum_one, restrLen_of_irrelevant _ hrel, restrLen_of_irrelevant _ hrel, sub_zero]
  obtain ⟨j, hj⟩ := hrel
  have hxj : x j ≠ 0 := fun h0 =>
    hj (hle ((mem_primeOf_of_isHomogeneous (S := S) x (isHomogeneous_X S j)).mpr (by rw [aeval_X, h0])))
  obtain ⟨hPprime, hPy⟩ := PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hxj hj

  have := hPprime
  obtain ⟨K', _, _, ψ, hψ⟩ := CycleSplit.Small.exists_residue (S := S) (chartPrime pp hxj)
  let y : Fin (N + 1) → K' := fun i => ψ (ratio hxj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i hyi hxi
    apply hyi
    have : ratio (S := S) hxj i = 0 := Subtype.ext (by simp [ratio, hxi])
    simp only [y, this, map_zero]
  have hpy : primeOf (S := S) y = pp := hPy K' ψ hψ
  have hy0 : y ≠ 0 := by
    intro h
    have h1 : ratio (S := S) hxj j = 1 := Subtype.ext (by simp [ratio, div_self hxj])
    have := congrFun h j
    simp only [y, h1, map_one, Pi.zero_apply] at this
    exact one_ne_zero this
  have hyrel : ∃ i, (X i : Poly S N) ∉ primeOf (S := S) y := ⟨j, hpy ▸ hj⟩
  have hydim : ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1 := hpy ▸ hdim

  have key : ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
      restrLen pp (Q.toSubSystem.twist (twistSys S x (c : ℤ))) =
        ((Module.length S ((twistBundle S y 0).twist (twistSys S y 0)).secs).toNat : ℤ) := by
    intro Q
    obtain ⟨Q', r, hR⟩ := PrimeFiltration.Restrict.proof S Ω N x pp hpp hhom hle j hxj hj K' ψ hψ hxy Q
    have hRD : RestrictData Q.toSubSystem hxy Q'.toSubSystem r :=
      ⟨fun I => (hR I).1, fun I => (hR I).2.1, fun I => (hR I).2.2.1, fun I => (hR I).2.2.2⟩
    obtain ⟨c₀, hc₀⟩ := SurjectiveClosed.proof Extension.full.{u, w, w} IdealTwistFamily.proof
      (TildeVanish.proof SerreVanish.full.{u, w}) S Ω N x Q pp hhom
    filter_upwards [eventually_ge_atTop c₀.toNat] with c hc
    have hcc : c₀ ≤ (c : ℤ) := by omega
    unfold restrLen
    rw [QuotientH0Length.length_secs_eq _ _ (hc₀ c hcc),
      (hRQ S Ω N x pp hpp hhom hle j hxj hj K' ψ hψ hxy Q Q' r hRD c 0).some.length_eq,
      (CechZerothCohomologySections.proof.{u, w, w} S K' N y K' _ hy0).some.length_eq,
      hPt S K' N y hyrel hydim Q' (twistBundle S y 0) c 0]
  filter_upwards [key M, key (twistBundle S x 0)] with c h1 h2
  rw [interSum_one, h1, show (twistSys S x 0).twist (twistSys S x (c : ℤ)) =
    (twistBundle S x 0).toSubSystem.twist (twistSys S x (c : ℤ)) from rfl, h2, sub_self]

end GroundTheory.Heights₂.Heights.Kleiman
