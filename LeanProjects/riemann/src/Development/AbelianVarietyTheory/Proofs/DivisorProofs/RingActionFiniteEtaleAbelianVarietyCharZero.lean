import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OActFinEt

variable {S : Scheme.{0}} {O : Type} [CommRing O] {A : Over S} [GrpObj A]

theorem act_zero (act : OAct O A) : act.act 0 = 1 :=
  mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one, ← act.add, add_zero])

theorem act_natCast (act : OAct O A) : ∀ n : ℕ, act.act (n : O) = 𝟙 A ^ n
  | 0 => by rw [Nat.cast_zero, act_zero, pow_zero]
  | n + 1 => by rw [Nat.cast_succ, act.add, act_natCast act n, act.one, pow_succ]

theorem exists_natCast_dvd {E : Type} [Field E] [NumberField E] (b : 𝓞 E) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ b ∣ (n : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · exact Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)

theorem finite_etale_act (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ) :
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ b : 𝓞 E, b ≠ 0 →
      IsFinite (act.act b).left ∧ Etale (act.act b).left ∧
        Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act b = 1} := by
  intro hA hg b hb
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  obtain ⟨n, hn0, b', hb'⟩ := exists_natCast_dvd b hb
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hnk).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have h1 : act.act b ≫ act.act b' = 𝟙 A ^ n := by rw [← act.mul, ← hb', act_natCast]
  have h2 : act.act b' ≫ act.act b = 𝟙 A ^ n := by rw [← act.mul, mul_comm, ← hb', act_natCast]
  haveI := act.hom b
  haveI := act.hom b'
  haveI hF : IsFinite (𝟙 A ^ n).left := GrpTangent.isFinite_id_pow A hu
  haveI hE : Etale (𝟙 A ^ n).left := GrpTangent.etale_id_pow A hu
  haveI : IsSeparated A.hom := inferInstance
  have hsep : ∀ f : A ⟶ A, IsSeparated f.left := fun f => by
    have : IsSeparated (f.left ≫ A.hom) := by rw [Over.w f]; infer_instance
    exact IsSeparated.of_comp f.left A.hom
  haveI := hsep (act.act b')
  haveI : IsFinite ((act.act b).left ≫ (act.act b').left) := by rw [← Over.comp_left, h1]; exact hF
  haveI hfin : IsFinite (act.act b).left := IsFinite.of_comp _ (act.act b').left
  haveI : FormallyUnramified ((act.act b).left ≫ (act.act b').left) := by
    rw [← Over.comp_left, h1]; infer_instance
  haveI : FormallyUnramified (act.act b).left := FormallyUnramified.of_comp _ (act.act b').left
  haveI : Flat (act.act b).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A hA _ inferInstance
      hfin).1
  haveI : LocallyOfFinitePresentation ((act.act b).left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFinitePresentation (act.act b).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  refine ⟨hfin, Etale.of_formallyUnramified_of_flat _, ?_⟩
  have hfinN := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA hg hnk
  refine Finite.of_injective (β := {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ n = 1})
    (fun x => ⟨x.1, ?_⟩) ?_
  · have := congrArg (· ≫ act.act b') x.2
    simp only [Category.assoc, h1, one_comp] at this
    rwa [comp_pow, Category.comp_id] at this
  · intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

end GlobalTheory.OActFinEt
