import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltFiniteSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechH0SectionsHypothesesLine
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem quotH_zero_subsingleton_of_irrelevant (F : SubSystem S x Ω) (pp : Ideal (Poly S N))
    (hpp : ∀ i, (X i : Poly S N) ∈ pp) :
    Subsingleton (SubSystem.quotH F (F.twist (idealSys x pp)) 0) := by
  have hsub : ∀ I : Chart x,
      Subsingleton (F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq]
    change ((a - b : F.sub I) : Ω) ∈ (F.twist (idealSys x pp)).sub I
    rw [SubSystem.twist_sub_eq_mul_of_line]
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
        isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
    simpa using Submodule.mul_mem_mul h1 (a - b).2
  have hC : Subsingleton (Cech.Cochain (fun I : Chart x =>
      F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) 0) := by
    unfold Cech.Cochain
    exact ⟨fun a b => funext fun I => (hsub I.1).elim _ _⟩
  unfold SubSystem.quotH Cech.H
  infer_instance

end

theorem SectionCount.Drop.Filt.Finite.proof
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hH0 : CechZerothCohomologySections.Statement.{u, w, w})
    (hFS : FiniteSections.Statement.{u, w}) :
    SectionCount.Drop.Filt.Finite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q pp c hpp hhom hle
  by_cases hirr : ∀ i, (X i : Poly S N) ∈ pp
  · have := quotH_zero_subsingleton_of_irrelevant (Q.twist (twistSys S x c)) pp hirr
    infer_instance
  push Not at hirr
  obtain ⟨j, hj'⟩ := hirr
  have hj : x j ≠ 0 := fun h0 => hj' (hle (by
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X S j), aeval_X, h0]))
  have hPtj := PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hj hj'

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type w) (_ : Field K') (_ : Algebra S K')
      (ψ : chartRing S x (singleChart hj) →ₐ[S] K'), RingHom.ker ψ = chartPrime pp hj := by
    have : (chartPrime pp hj).IsPrime := hPtj.1
    have : IsDomain (chartRing S x (singleChart hj) ⧸ chartPrime pp hj) := Ideal.Quotient.isDomain _
    refine ⟨FractionRing (chartRing S x (singleChart hj) ⧸ chartPrime pp hj), inferInstance, inferInstance,
      (IsScalarTower.toAlgHom S _ _).comp (Ideal.Quotient.mkₐ S (chartPrime pp hj)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (chartRing S x (singleChart hj) ⧸ chartPrime pp hj))
      (Ideal.Quotient.mk (chartPrime pp hj) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i hi h0
    apply hi
    have : ratio (S := S) hj i = 0 := Subtype.ext (show x i / x j = 0 by rw [h0, zero_div])
    rw [this, map_zero]
  have hy0 : (fun i => ψ (ratio hj i)) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 j
    rw [ratio_self hj ψ] at h1
    exact one_ne_zero h1

  obtain ⟨Q', r, hr⟩ := PrimeFiltration.Restrict.proof S Ω N x pp hpp hhom hle j hj hj' K' ψ hker hxy Q
  have hRD : RestrictData Q.toSubSystem hxy Q'.toSubSystem r :=
    ⟨fun I => (hr I).1, fun I => (hr I).2.1, fun I => (hr I).2.2.1, fun I => (hr I).2.2.2⟩
  obtain ⟨E1⟩ := hRQ S Ω N x pp hpp hhom hle j hj hj' K' ψ hker hxy Q Q' r hRD c 0

  obtain ⟨E2⟩ := hH0 S K' N _ K' (Q'.toSubSystem.twist (twistSys S (fun l => ψ (ratio hj l)) c)) hy0
  have hfin := (hFS S K' N _ (Q'.tensorProd (twistBundle S _ c)) hy0).1
  have hfin' : Module.Finite S (Q'.toSubSystem.twist (twistSys S (fun l => ψ (ratio hj l)) c)).secs := hfin
  exact Module.Finite.equiv (E1.trans E2).symm
