import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OActFinEtNorm

theorem dvd_natAbs_norm {E : Type} [Field E] [NumberField E] (b : 𝓞 E) :
    b ∣ (((Algebra.norm ℤ b).natAbs : ℕ) : 𝓞 E) := by
  rw [← Ideal.absNorm_span_singleton]
  exact Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)

theorem finite_etale_act_of_norm {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {Ω : Type}
    [Field Ω] [IsAlgClosed Ω] (X : Obj F 𝔠 (Sp Ω)) (b : 𝓞 F)
    (hb : ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0) :
    IsFinite (X.rm.act b).left ∧ Etale (X.rm.act b).left ∧
      Finite {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} := by
  have hA := X.ab
  have hg := X.dim
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  set n : ℕ := (Algebra.norm ℤ b).natAbs with hn_def
  obtain ⟨b', hb'⟩ := dvd_natAbs_norm b
  have hnk : (n : Ω) ≠ 0 := by
    intro h
    apply hb
    rcases Int.natAbs_eq (Algebra.norm ℤ b) with h' | h'
    · rw [h', Int.cast_natCast]; exact h
    · rw [h', Int.cast_neg, Int.cast_natCast, h, neg_zero]
  have hu : IsUnit (n : Γ(Sp Ω, ⊤)) := by
    simpa using (Ne.isUnit hnk).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  have h1 : X.rm.act b ≫ X.rm.act b' = 𝟙 X.A ^ n := by
    rw [← X.rm.mul, ← hb', GlobalTheory.OActFinEt.act_natCast]
  haveI := X.rm.hom b
  haveI := X.rm.hom b'
  haveI hF : IsFinite (𝟙 X.A ^ n).left := GrpTangent.isFinite_id_pow X.A hu
  haveI hE : Etale (𝟙 X.A ^ n).left := GrpTangent.etale_id_pow X.A hu
  have hsep : ∀ f : X.A ⟶ X.A, IsSeparated f.left := fun f => by
    have : IsSeparated (f.left ≫ X.A.hom) := by rw [Over.w f]; infer_instance
    exact IsSeparated.of_comp f.left X.A.hom
  haveI := hsep (X.rm.act b')
  haveI : IsFinite ((X.rm.act b).left ≫ (X.rm.act b').left) := by
    rw [← Over.comp_left, h1]; exact hF
  haveI hfin : IsFinite (X.rm.act b).left := IsFinite.of_comp _ (X.rm.act b').left
  haveI : FormallyUnramified ((X.rm.act b).left ≫ (X.rm.act b').left) := by
    rw [← Over.comp_left, h1]; infer_instance
  haveI : FormallyUnramified (X.rm.act b).left := FormallyUnramified.of_comp _ (X.rm.act b').left
  haveI : Flat (X.rm.act b).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected Ω X.A hA _ inferInstance
      hfin).1
  haveI : LocallyOfFinitePresentation ((X.rm.act b).left ≫ X.A.hom) := by
    rw [Over.w]; infer_instance
  haveI : LocallyOfFinitePresentation (X.rm.act b).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ X.A.hom
  refine ⟨hfin, Etale.of_formallyUnramified_of_flat _, ?_⟩
  have hfinN := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA hg hnk
  refine Finite.of_injective (β := {x : 𝟙_ (Over (Sp Ω)) ⟶ X.A // x ^ n = 1})
    (fun x => ⟨x.1, ?_⟩) ?_
  · have := congrArg (· ≫ X.rm.act b') x.2
    simp only [Category.assoc, h1, one_comp] at this
    rwa [comp_pow, Category.comp_id] at this
  · intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

end GlobalTheory.OActFinEtNorm
