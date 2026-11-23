import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionOpenCover
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveSecDeg

theorem topSelf_pos_of_sec : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (e : ℕ), IsArithVar p e →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
      [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → ∀ (M : ReciprocityTheory.ChartRestriction.G.Semi.LB Z), M.IsLB → ∀ s : M.Sec,
      (∃ z, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) → (∃ z, z ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) →
      0 < topSelfIntersection κ M 1 := by
  intro k _ X p e hX Z i _ _ κ _ _ _ hd M hM s ⟨z, hz⟩ ⟨y, hy⟩
  have := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e' : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e']; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have hg : genericPoint Z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s :=
    ((genericPoint_spec Z).mem_open_set_iff (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s).isOpen).2
      ⟨z, trivial, hz⟩
  have h := (interNum_one_nonneg_of_sec (k := κ) hA hd hM s hg).2 (fun ht => hy (ht ▸ trivial))
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

end GlobalTheory.CurveSecDeg
