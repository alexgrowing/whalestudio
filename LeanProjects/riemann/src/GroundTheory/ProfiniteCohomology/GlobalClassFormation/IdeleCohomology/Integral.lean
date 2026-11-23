import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.IntegerUnits
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Finite
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Unramified
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

variable (L) in

noncomputable abbrev integerUnitsAboveRep :
    Representation ℤ Gal(L/K) (∀ w : PlacesOver L v, Additive (w.1.adicCompletionIntegers L)ˣ) :=
  piUnitsRep

theorem integerUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    ((((σ • z) w' : (w'.1.adicCompletionIntegers L)ˣ) : w'.1.adicCompletionIntegers L) :
      w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) ((z w : w.1.adicCompletionIntegers L) :
        w.1.adicCompletion L) := by
  subst h
  exact integerUnitsAbove_smul_apply v σ z w

theorem permutesFactors_integerUnitsAboveRep : PermutesFactors (integerUnitsAboveRep L v) := by
  intro σ f w hf
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  change ((((σ • fun x => (f x).toMul) (σ • w) : ((σ • w).1.adicCompletionIntegers L)ˣ) :
    (σ • w).1.adicCompletionIntegers L) : (σ • w).1.adicCompletion L) = 1
  rw [integerUnitsAbove_smul_apply, hf]
  exact map_one _

section Decomposition

variable (w : PlacesOver L v)

theorem stabRep_integerUnitsAboveRep (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (a : Additive (w.1.adicCompletionIntegers L)ˣ) :
    stabRep (integerUnitsAboveRep L v) (permutesFactors_integerUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w) σ a =
      Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletionIntegers L)ˣ σ a := by
  classical
  rw [stabRep_apply]
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  have hw : w = (σ : Gal(L/K)) • w := ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2).symm
  simp only [piUnitsRep_apply, toMul_ofMul]
  rw [integerUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) _ w w hw, galEquiv_apply,
    galHom_eq_decomposition]
  simp only [Pi.single_eq_same]
  rfl

noncomputable def stabRepIntegralIso :
    Rep.of (stabRep (integerUnitsAboveRep L v) (permutesFactors_integerUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w)) ≅
      Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletionIntegers L)ˣ :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) fun σ =>
    LinearMap.ext fun a => stabRep_integerUnitsAboveRep v w σ a)

variable [IsGalois K L]

noncomputable def integralShapiroIso (n : ℕ) :
    cohomology (Rep.of (integerUnitsAboveRep L v)) n ≅
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletionIntegers L)ˣ) n :=
  orbitShapiroIso (permutesFactors_integerUnitsAboveRep v)
      ⟨MulAction.stabilizer Gal(L/K) w.1.asIdeal, isOpen_discrete _⟩
      (mem_stabilizer_iff_smul_eq v w) n ≪≫
    cohomologyIsoOfIso (stabRepIntegralIso v w) n

theorem isZero_cohomology_integerUnitsAboveRep (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    {n : ℕ} (hn : 1 ≤ n) : IsZero (cohomology (Rep.of (integerUnitsAboveRep L v)) n) :=
  (isZero_cohomology_decomposition_integerUnits v w.1 he hn).of_iso (integralShapiroIso v w n)

end Decomposition

end GroundTheory.ProfCoh
