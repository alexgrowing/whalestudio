import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSecondBlockOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowersDiagonalAtTBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgEqZeroOfInfiniteRange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaGLMemIwGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactClosureZpowersMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationQuotientSeparatedDvd

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MT PositivityTheory.Rg.BcB.F.MLM
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RegPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open GlobalTheory.CompanionTheory.MatchPow in

theorem hasVals_nrm (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a : ℕ}
    {y : Fin a → ℤ} (hy : StrictAnti y) {δ : GLw a w} (hδ : dcos a w (tdiag ϖ y) δ ≠ 0) :
    HasVals (nrmL a w δ).val.charpoly (nv y) := by
  obtain ⟨m, -, τ, hτ, e⟩ := GlobalTheory.CompanionTheory.ThetaContraction.contr_tw hU w hw ϖ hϖ a y hy δ hδ
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.CompanionTheory.TwSide.exists_diagT_of_mem_TO hτ
  have hdu : m⁻¹ * δ * thL a w m = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) fun i => ϖ ^ y i * v i := by
    rw [e, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (((ϖ ^ y i * v i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = y i := by
    intro i
    simp only [Units.val_mul]
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
      GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, hϖ.1,
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, map_one]),
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one]
    simp
  rw [← GlobalTheory.CompanionTheory.MatchLinear.charpoly_nrmL_twConj hU a w δ m, hdu, GlobalTheory.CompanionTheory.TwSide.nrmL_diagT hw, GlobalTheory.SmGL.val_diagT,
    Matrix.charpoly_diagonal]
  exact ⟨fun i => _, rfl, fun i => ⟨Units.ne_zero _, GlobalTheory.CompanionTheory.TwSide.ordL_norm_entry hU _ y hord i⟩⟩

open GlobalTheory.CompanionTheory.MatchPow in

theorem mpow_entT {w : Pl E} {n : ℕ} (a : ℕ) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {J : Type} [Fintype J]
    (c : J → ℂ) (x : J → Fin n → ℤ) (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (k : ℕ) :
    ∃ (J' : Type) (_ : Fintype J') (c' : J' → ℂ) (x' : J' → Fin n → ℤ),
      (∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j))) ∧
      ∀ s, mpow w (entT n w ϖ a c x s) (k + 1) = fun y => beta a (n - a) w ^ k * entT n w ϖ a c' x' s y := by
  induction k with
  | zero =>
    refine ⟨J, inferInstance, c, x, hx, fun s => ?_⟩
    funext y
    have := conv_unit (iwahori_pair_le_maximal a (n - a) w) (iwahori_pair_index_ne_zero a (n - a) w)
      (fun k hk z => ((entT_hecke n w ϖ a c x s).2 k hk z).2) y
    rw [pow_zero, one_mul]
    exact this
  | succ k ih =>
    obtain ⟨J', _, c', x', hx', e⟩ := ih
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => x p.1 + x' p.2, fun p => ⟨?_, ?_⟩, fun s => ?_⟩
    · exact fun i j hij => add_lt_add ((hx p.1).1 hij) ((hx' p.2).1 hij)
    · rw [lOf_add]
      exact cone_add (hx p.1).2 (hx' p.2).2
    · show mconv _ (mpow w _ (k + 1)) = _
      rw [e, mconv_entT GlobalTheory.CompanionTheory.DcosProduct.dcosMul n ϖ hϖ a c x c' x' hx hx', pow_succ]

theorem regPowT : RegPowT := by
  intro E _ _ _ hU n d _ hm a ha m w hT y hy
  obtain ⟨hw, -, hϖ, hc⟩ := hm.T w hT
  rw [GlobalTheory.CompanionTheory.MatchLMB2.trace_test_function_eq d ha hT m] at hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  obtain ⟨J', _, c', x', hx', e⟩ := mpow_entT a hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w)
    (fun j => hc j.1 j.2) m
  rw [GlobalTheory.CompanionTheory.MatchLMPlaces.qT_eq d s, GlobalTheory.CompanionTheory.MatchLMPlaces.mpow_scale, e s] at hs
  have h1 : entT n w (d.ϖ w) a c' x' s y ≠ 0 := fun h => hs (by simp [h])
  by_cases hA : MT.admitted n a s
  swap
  · exact absurd (dif_neg hA) h1
  unfold entT at h1
  rw [dif_pos hA] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hd2 : dcos (n - a) w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.2)) y.2 ≠ 0 := right_ne_zero_of_mul hj
  have hd1 : dcos a w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.1)) y.1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hj)
  obtain ⟨u₁, hQ₁, hu₁⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.1) hd1
  obtain ⟨u₂, hQ₂, hu₂⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.2) hd2
  rw [hQ₁, hQ₂]
  exact GlobalTheory.CompanionTheory.SymmetricIndexRegularity.localization_quotient_separated_dvd (fun z => ordL z) (hx' j).1 _ _ hA.2.2.2.1 hA.2.2.2.2 (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ s)
    (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ sᶜ) (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_disj n _ _ s (by have := hA.2.2.1; omega)) u₁ u₂
    (fun j => (hu₁ j).2) (fun j => (hu₂ j).2)

end GlobalTheory.CompanionTheory.RegPow

end
