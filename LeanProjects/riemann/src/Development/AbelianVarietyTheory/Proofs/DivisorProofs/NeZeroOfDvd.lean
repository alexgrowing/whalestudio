import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionCohomologyMapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.RedCoef

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

def semiId (I : Cx S) : SemiMap I I where
  app _ _ := AddMonoidHom.id _
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

def semiComp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (σ.app _ s (ρ.app _ s a)) = σ.app _ s (ρ.app _ s (Sec.res g a))
    rw [σ.nat, ρ.nat]
  comm U s t a := by
    change Sec.map (K.d s t) (σ.app U s (ρ.app U s a)) = σ.app U t (ρ.app U t (Sec.map (I.d s t) a))
    rw [σ.comm, ρ.comm]

theorem semiId_op (I : Cx S) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (semiId I).op.app E n x = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S S (semiId I)).2 E n α α (fun _ _ _ _ _ => rfl)

theorem semiComp_op {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (semiComp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).1 E n β
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).2 E n β γ hγ]
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S T (semiComp ρ σ)).2 E n α γ (fun p s h U y => by
    rw [hγ p s h U y, hβ p s h U y]; rfl)

theorem neZero_of_dvd {q Q : ℕ} [NeZero Q] (h : q ∣ Q) : NeZero q :=
  ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp h)⟩

theorem div_mul_div {Q q r : ℕ} [NeZero Q] (hq : q ∣ Q) (hr : r ∣ q) : Q / q * (q / r) = Q / r := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨l, rfl⟩ := hr
  have hQ := NeZero.ne (r * l * k)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hQ
  have hl0 : l ≠ 0 := by rintro rfl; simp at hQ
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hr0 hl0)),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0), mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0),
    mul_comm]

end GlobalTheory.EtC.RedCoef

namespace GlobalTheory.EtC.RedCoef

theorem a11 : GlobalTheory.EtC.A11 := by
  intro Q q _ hqQ E
  haveI : NeZero q := neZero_of_dvd hqQ
  refine ⟨fun a b => GlobalTheory.T.tateTwistCoefficientReduction_cup Q q hqQ E a b, fun hE => ⟨GlobalTheory.T.tateTwistCoefficientReduction_unitClass Q q hqQ E hE, fun L => GlobalTheory.T.red_c1_eq_c1_of_dvd Q q hqQ E hE L⟩,
    fun n i a => ?_, fun r hr n i a => ?_⟩
  · have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (redMap Q Q i).app U 0 (resGen i ζ) = (semiId (res _ (tw Q i))).app U 0 (resGen i ζ) := by
      intro U ζ
      refine GlobalTheory.T.tateTwistReductionResolutionMap_generator Q Q dvd_rfl i U ζ ζ ?_
      rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne Q)), pow_one]
    exact (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q Q dvd_rfl i _ _ hgen E n a).trans (semiId_op _ E n a)
  · haveI : NeZero r := neZero_of_dvd hr
    have hrQ : r ∣ Q := hr.trans hqQ
    have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (semiComp (redMap Q q i) (redMap q r i)).app U 0 (resGen i ζ) = (redMap Q r i).app U 0 (resGen i ζ) := by
      intro U ζ
      obtain ⟨η, hη⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.2.2 r hr η
      change (redMap q r i).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) = _
      rw [GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ η hη, GlobalTheory.T.tateTwistReductionResolutionMap_generator q r hr i U η ξ hξ,
        GlobalTheory.T.tateTwistReductionResolutionMap_generator Q r hrQ i U ζ ξ (by rw [hξ, hη, ← pow_mul, div_mul_div hqQ hr])]
    exact (semiComp_op _ _ E n a).symm.trans (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q r hrQ i _ _ hgen E n a)

end GlobalTheory.EtC.RedCoef
