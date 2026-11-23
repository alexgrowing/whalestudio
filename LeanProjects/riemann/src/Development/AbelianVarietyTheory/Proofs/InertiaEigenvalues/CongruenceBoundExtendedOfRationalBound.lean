import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

open scoped ENNReal

namespace GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

open GlobalTheory.IndefiniteRowSideFullHecke

theorem congBound_of_rational : ∀ (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), π ∈ D.nd.Z i → (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → (Br.sFin D.loc D.nbr i (fun _ => ρ) π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i (fun _ => ρ) π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})) → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vCC D i π ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sPi D i π ρ + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.shaSum D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vClass D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.epsQ D i := by
  intro D i π ρ hπ hζ h
  classical
  obtain ⟨he0, het⟩ := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i
  refine (GlobalTheory.Proof.QuotientLengthInfimum.conclusion_iff D i π ρ).2 ?_
  by_cases hs : Br.sFin D.loc D.nbr i (fun _ => ρ) π
  swap
  · have h1 : SelmerSumLargePrime.selLen D i ρ π = ⊤ := not_lt_top_iff.mp hs
    rw [h1]; simp
  by_cases hsh : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤
  swap
  · push Not at hsh
    obtain ⟨k, hk, hk'⟩ := hsh
    have h1 : SelmerSumLargePrime.shaSum D i = ⊤ := by
      unfold SelmerSumLargePrime.shaSum
      refine top_le_iff.mp (le_trans hk' ?_)
      exact Finset.single_le_sum (f := fun e : ℕ => Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ))
        (fun _ _ => zero_le) hk
    rw [h1, ENat.mul_top he0]; simp
  have hr := h hs hsh
  have hc : SelmerSumLargePrime.ccLen D i π ≠ ⊤ := by
    unfold SelmerSumLargePrime.ccLen
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.vcc_ne_top _ (D.nd.T_sep i) _ _ hπ
  have hs' : SelmerSumLargePrime.selLen D i ρ π ≠ ⊤ := hs.ne
  have hq : ∀ P ∈ D.nd.Q i,
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1}) ≠ ⊤ := by
    intro P hP
    have h0 : SelmerSumLargePrime.zetaP D i P - 1 ≠ 0 := by
      rw [← GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq, BaseSizes.zetaP_eq D i P hP]
      exact sub_ne_zero.mpr (hζ P hP)
    exact Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero h0))
  have hrow : ∀ k ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) k : ℚ) =
      ((Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat : ℚ) := fun k hk =>
    D.nd.sha_eq _ k (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2 _
      (ENat.natCast_toNat (hsh k hk).ne).symm
  have hlq : ∀ P ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i P - 1}) =
      ((Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat : ℚ) /
        ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    intro P hP
    rw [← BaseSizes.zetaP_eq D i P hP, GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq]
    rfl
  have hv : D.nd.vcc i π = ((SelmerSumLargePrime.ccLen D i π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  have hsp : Br.sPi D.loc D.nbr i (fun _ => ρ) π =
      ((SelmerSumLargePrime.selLen D i ρ π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  rw [hv, hsp, Finset.sum_congr rfl hrow, Finset.sum_congr rfl hlq, ← Finset.sum_div] at hr
  have hE0 : (0 : ℚ) < ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    have : (SelmerSumLargePrime.ramLen D i).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; tauto
    exact_mod_cast Nat.pos_of_ne_zero this
  set E := (SelmerSumLargePrime.ramLen D i).toNat with hEdef
  set c := (SelmerSumLargePrime.ccLen D i π).toNat
  set s := (SelmerSumLargePrime.selLen D i ρ π).toNat
  set A := ∑ k ∈ Finset.Ioo 0 D.R.t, (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat with hA
  set B := ∑ P ∈ D.nd.Q i,
    (Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat with hB
  set v := padicValNat (D.nd.l i) (hE D.host)
  have key : (c : ℚ) ≤ s + E * A + E * v + D.R.t * B := by
    have h2 : ((s : ℚ) / E + (A : ℚ) + (v : ℚ) + (D.R.t : ℚ) * ((B : ℚ) / E)) * E =
        s + E * A + E * v + D.R.t * B := by
      field_simp
    rw [← h2, ← div_le_iff₀ hE0]
    push_cast [hA, hB]
    exact hr
  have knat : c ≤ s + E * A + E * v + D.R.t * B := by exact_mod_cast key
  have hsum : SelmerSumLargePrime.shaSum D i = (A : ℕ∞) := by
    unfold SelmerSumLargePrime.shaSum
    rw [hA, Nat.cast_sum]
    exact Finset.sum_congr rfl fun k hk => (ENat.natCast_toNat (hsh k hk).ne).symm
  have htw : SelmerSumLargePrime.twistLen D i = ((D.R.t * B : ℕ) : ℕ∞) := by
    unfold SelmerSumLargePrime.twistLen
    rw [hB, Nat.cast_mul, Nat.cast_sum]
    exact congrArg _ (Finset.sum_congr rfl fun P hP => (ENat.natCast_toNat (hq P hP)).symm)
  rw [hsum, htw, ← ENat.natCast_toNat hc, ← ENat.natCast_toNat hs', ← ENat.natCast_toNat het]
  exact_mod_cast knat

end GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

end
