import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.DenseInvFrob

theorem isSplitAt_of_inertiaDeg_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hf : w.asIdeal.inertiaDeg ℤ = 1)
    (he : w.asIdeal.ramificationIdx ℤ = 1) : IsSplitAt w := by
  classical
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  set p : Ideal (𝓞 (maximalRealSubfield E)) := v.asIdeal with hp
  haveI : p.IsPrime := v.isPrime
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI hlo : w.asIdeal.LiesOver p := ⟨rfl⟩
  by_contra hns
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 (maximalRealSubfield E)) (𝓞 E) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
    exact (IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p w.asIdeal
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) p w.asIdeal
    rw [he] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : w.asIdeal ∈ p.primesOver (𝓞 E) := ⟨inferInstance, hlo⟩
  have huniq : ∀ q : p.primesOver (𝓞 E), q = ⟨w.asIdeal, hPmem⟩ := by
    intro q
    have hq : q.1.IsPrime := q.2.1
    have hql : q.1.LiesOver p := q.2.2
    have hne : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1
    let u : HeightOneSpectrum (𝓞 E) := ⟨q.1, hq, hne⟩
    by_contra hqw
    apply hns
    refine ⟨u, fun h => hqw (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)), ?_⟩
    ext1
    simp only [HeightOneSpectrum.under_asIdeal]
    exact hql.over.symm
  rw [Finset.sum_eq_single ⟨w.asIdeal, hPmem⟩ (fun b _ hb => absurd (huniq b) hb)
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  simp only [he1, hf1, mul_one] at hsum
  omega

end GlobalTheory.DenseInvFrob

namespace GlobalTheory.DenseInvFrob

end GlobalTheory.DenseInvFrob
