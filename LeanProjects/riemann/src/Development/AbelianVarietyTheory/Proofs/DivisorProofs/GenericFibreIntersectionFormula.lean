import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreClosedSubvarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePreimmersionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

noncomputable section

namespace GlobalTheory.GenFibreDegree

theorem interNum_eq_zero_of_not_generic (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (z : Y)
    (hz : f z ≠ genericPoint B) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsIntegral Z]
    (hi : i (genericPoint Z) = z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField)
    (hG' : IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)))
    {ι : Type} [Fintype ι] (P : ι → LB Z) (hP : ∀ a, (P a).IsLB) :
    (letI := algebraΓOfHom s'
     interNum B.functionField (structureModule G') (fun a => (P a).pull j')) = 0 := by
  have hE : IsEmpty G' := by
    refine ⟨fun g => hz ?_⟩
    obtain ⟨_, hr, _, h4⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Z (i ≫ f) G' j' s' hG'
    obtain ⟨hGi, hη⟩ := h4 ⟨g⟩
    have hmem : j' (genericPoint G') ∈ Set.range j' := ⟨_, rfl⟩
    rw [hr, hη] at hmem
    simpa [← hi] using hmem
  letI := algebraΓOfHom s'
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _)
    (fun a => LB.isLB_pull (hP a) j')

theorem degree_genericFibre_ratSec : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsLocallyNoetherian Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → IsArithVar p (d + (e + 1)) → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin (e + 1) → LB Y) (hL : ∀ a, (L a).IsLB) (r : (L 0).ι → Y.functionFieldˣ) (hr : IsRatSec (L 0) r) (γ : Y → ℤ), (∀ z, (divOfRatSec (hL 0) hr).mult z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧ IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧ γ z = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a : Fin e => ((L a.succ).pull i).pull j'))) → (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) (fun a => (L a).pull j)) = ∑ᶠ z, (divOfRatSec (hL 0) hr).mult z * γ z := by
  intro k _ B Y _ _ _ q p d e hq hp f hfq G j s hpb L hL r hr γ hγ
  obtain ⟨hpre, hrange, hstalk, hint⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hpb
  set F : Y → ℤ := fun z => (divOfRatSec (hL 0) hr).mult z * γ z with hF
  have hoff : ∀ z, z ∉ Set.range j → F z = 0 := by
    intro z hz
    by_cases hm : (divOfRatSec (hL 0) hr).mult z = 0
    · simp [hF, hm]
    obtain ⟨Z, i, _, _, G', j', s', hi, hpb', hγz⟩ := hγ z hm
    have hfz : f z ≠ genericPoint B := by
      intro h
      exact hz (hrange ▸ (show z ∈ f ⁻¹' {genericPoint B} from h))
    simp only [hF]
    rw [hγz, interNum_eq_zero_of_not_generic B Y f z hfz Z i hi G' j' s' hpb'
      (fun a : Fin e => (L a.succ).pull i) (fun a => LB.isLB_pull (hL a.succ) i), mul_zero]
  have hinj : Function.Injective j := j.isEmbedding.injective
  have hs : Function.support F ⊆ Set.range j := fun z hz => by
    by_contra h
    exact hz (hoff z h)
  have hre : ∑ᶠ w, F (j w) = ∑ᶠ z, F z := by
    rw [← finsum_mem_range hinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs,
      finsum_mem_support]
  rw [← hre]
  rcases isEmpty_or_nonempty G with hG | hG
  · letI := algebraΓOfHom s
    rw [interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _)
      (fun a => LB.isLB_pull (hL a) j)]
    exact (finsum_of_isEmpty _).symm
  · obtain ⟨hGi, hη⟩ := hint hG
    letI := algebraΓOfHom s
    have hsproj : IsProjOver s :=
      GlobalTheory.T.generic_fibre_projective k B Y q p hq.isProjOver hp.isProjOver f hfq G j s hpb
    have hstr : strHom B.functionField G = s := strHom_eq fun _ => rfl
    haveI : AlgebraicGeometry.IsNoetherian G := isNoetherian_of_isProjOver hsproj
    haveI : IsProper q := CommonModel.isProper_of_isProjOver hq.isProjOver
    haveI : IsProper (f ≫ q) := by rw [hfq]; exact CommonModel.isProper_of_isProjOver hp.isProjOver
    haveI : IsProper f := IsProper.of_comp f q
    have hdim : topologicalKrullDim G ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
      GlobalTheory.T.generic_fibre_dimension_le B Y (d + 1) (e + 1) hq.dim_eq
        (by rw [hp.dim_eq]; exact le_of_eq (congrArg _ (by omega))) f G j s hpb
    obtain ⟨r', hr', hmult⟩ := GlobalTheory.T.rational_section_divisor_pullback_generic G Y j hη hstalk (L 0) (hL 0) r hr
    have hcyc := GlobalTheory.T.rational_section_cycle_formula_projective B.functionField G (by rw [hstr]; exact hsproj) e hdim
      ((L 0).pull j) (LB.isLB_pull (hL 0) j) (fun a => (L a.succ).pull j)
      (fun a => LB.isLB_pull (hL a.succ) j) r' hr'
    have hcons : (Fin.cons ((L 0).pull j) (fun a : Fin e => (L a.succ).pull j) :
        Fin (e + 1) → LB G) = fun a => (L a).pull j := by
      funext a
      exact Fin.cases rfl (fun b => rfl) a
    rw [hcons] at hcyc
    rw [hcyc]
    congr 1
    funext w
    simp only [hF]
    rw [hmult w]
    by_cases hm : (divOfRatSec (hL 0) hr).mult (j w) = 0
    · simp [hm]
    obtain ⟨Z, i, _, _, G', j', s', hi, hpb', hγz⟩ := hγ (j w) hm
    rw [hγz, GlobalTheory.T.generic_fibre_closed_subvariety B Y f G j s hpb w Z i hi G' j' s' hpb' (Fin e) (fun a => L a.succ)
      (fun a => hL a.succ)]

end GlobalTheory.GenFibreDegree
