import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EndoConstantFamilyDualNumbersEqBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoPullOfIsConst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionConstantFamilyDualNumbersStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

namespace GlobalTheory.KS
private theorem k_ne_zero_lemma {o : Type} [CommRing o] {k : ℕ} (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) :
    k ≠ 0 := by
  rintro rfl
  have h0 : (0 : o) = 1 := isUnit_zero_iff.mp (by simpa using b.unit)
  haveI : Subsingleton o := subsingleton_of_zero_eq_one h0
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum ℂ))
  exact (s₀.base x).isPrime.ne_top (Subsingleton.elim _ _)

theorem tMap_of_isConst : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (s₀ : Sp ℂ ⟶ Sp o) (s' : Sp (DualNumber ℂ) ⟶ Sp o) (t₀ : TObj g k J b s₀) (t' : TObj g k J b s') (ρ : t'.A.left ⟶ t₀.A.left) (j : t₀.A.left ⟶ t'.A.left), IsConst t'.A t₀.A ρ j → (IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ LBIso t₀.L (t'.L.pull j) ∧ (∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left) → TMap t' t₀ (spMap (algebraMap ℂ (DualNumber ℂ))) := by
  intro hL hL2 hT o _ g k J b s₀ s' t₀ t' ρ j hc ⟨hpb, hlb, hpt, hact⟩
  have hk : k ≠ 0 := k_ne_zero_lemma b s₀
  refine ⟨ρ, hc.1, ?_, ?_, ?_⟩
  · obtain ⟨u, Hm, χ, hu, -⟩ := GlobalTheory.KSInh.exists_goodU_ksRel hT t₀.pol
    exact GlobalTheory.SymRigid.lbIso_pull_of_isConst hL t₀.pol u Hm χ hu t'.A ρ j hc t'.L t'.isLB t'.sym hlb
  · intro i
    exact GlobalTheory.T.torsionSection_constantFamily_dualNumbers hL t₀.pol t'.A ρ j hc k (t'.pt i) (t₀.pt i) hk (t'.torsion i) (t₀.torsion i) (hpt i).symm
  · intro jj
    exact GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange hL hL2 t₀.pol t'.A ρ j hc (t'.act jj) (t₀.act jj) t'.ab (t'.hom jj) (t₀.hom jj) (hact jj).symm
end GlobalTheory.KS
