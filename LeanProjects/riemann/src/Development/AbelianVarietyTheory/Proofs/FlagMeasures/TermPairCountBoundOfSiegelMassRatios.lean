import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairBdMulDatBdLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExistsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHoldsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMeanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ParameterSizeConstraintsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeansStatement

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PairsPf

theorem massC_nonneg {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : 0 ≤ massC Y u := by
  show 0 ≤ ∑ Λ ∈ Y.what₂ u, wRow D (X.Fu u) Λ
  exact Finset.sum_nonneg fun Λ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem datBd_nonneg (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) (hD : 0 ≤ Del)
    (hDb : 0 ≤ Db) (hN : 0 ≤ NT) (hx : 0 ≤ x) : 0 ≤ GlobalTheory.DegAsm.datBd K k r Del Db NT x := by
  unfold GlobalTheory.DegAsm.datBd
  positivity

theorem termPairBoundFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Ch Cp : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2e large₂ CH Ch Cp j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have h1 : 0 ≤ k2Del D j δ := Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := Real.rpow_nonneg hb.le _
  have h3 : 0 ≤ k2S D (H1C large₂ CH) j δ := by
    unfold k2S k2sg
    exact Finset.prod_nonneg fun τ _ => le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  unfold k2e
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) (Real.rpow_nonneg h3 _)
private lemma le_mul_sum_sum_of_ofReal_le_ennreal_sum (s s' : Finset ℕ) (f P : ℕ → ℕ → ℝ) (c L : ℝ) (hf : ∀ x x', 0 ≤ f x x')
    (hP : ∀ x x', 0 ≤ P x x') (hc : 0 ≤ c)
    (h : ENNReal.ofReal L ≤ ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x')) :
    L ≤ c * ∑ x ∈ s, ∑ x' ∈ s', P x x' * f x x' := by
  have hnn : ∀ x x', 0 ≤ f x x' * (c * P x x') := fun x x' => mul_nonneg (hf x x') (mul_nonneg hc (hP x x'))
  have e : ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x') =
      ENNReal.ofReal (∑ x ∈ s, ∑ x' ∈ s', f x x' * (c * P x x')) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [ENNReal.ofReal_mul (hf x x')]
  rw [e] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')).1 h
  refine le_trans h' (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

end PairsPf
open PairsPf in

theorem pair_count_bound_of_siegel_mass : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → PairsP := by
  intro hMM hSR
  unfold PairsP
  intro Cg cb Cw cT CT C0 CH hCH

  obtain ⟨Ca, hCa1, hCaH, hCaT⟩ : ∃ Ca : ℝ, 1 ≤ Ca ∧ 2 * (CH + 1) ≤ Ca ∧ CT ≤ Ca :=
    ⟨max 1 (max (2 * (CH + 1)) CT), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨Ch, Cl', hCh, hsum⟩ := GlobalTheory.DegAsm.sum_pairBd_mul_datBd_le Ca hCa1
  refine ⟨Ch, 16, hCh, by norm_num, 1, max 1 Cl', ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hK2 _
  have hStd : GlobalTheory.TypeAsm.Std D large₂ :=
    show ∃ C' Cl Cg cb Cw cT CT C0 : ℝ, Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 from
      ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK2⟩
  have hHost : HostC := GlobalTheory.T.unitaryHostFieldArithmeticConditions
  have hfD : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := (hHost D large₂ hStd).2.2.2.2.1
  have hCl1 : 1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hClCl : Cl' ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨hrk, hm, hClm, hm4, hm5, hClk, hlog, hb2, hv1, hvb, hg, hTu⟩ :=
    GlobalTheory.T.parameter_size_constraints Ca Cg cb Cw cT CT C0 C' Cl D large₂ hHost hK2 hC' hCl1 hCaT
  have hlb : 0 ≤ (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hClm' : Cl' ≤ (D.R.m : ℝ) := le_trans hClCl hClm
  have hClk' : Cl' * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k :=
    le_trans (mul_le_mul_of_nonneg_right hClCl hlb) hClk

  have hHb : Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f ≤
      large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E) := by
    show large₂.sc.b ^ (2 * (CH + 1) * (D.R.m : ℝ) ^ 2 * D.R.f) ≤ _
    rw [hfD]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr)
  have hHb0 : 0 ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := Real.rpow_nonneg (by linarith) _
  have hNT : NT D u = ((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E := by
    rw [hfD]
    rfl
  have hNT0 : 0 ≤ NT D u := by
    rw [hNT]
    positivity
  have hk2e : ∀ (j : ℕ) (δ : ℕ → D.host.E), k2e large₂ CH Ch 16 j δ =
      k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (large₂.sc.b ^ (Ch * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E)) ^ (Ch * (D.R.rS : ℝ) ^ 4) *
        k2S D (H1C large₂ CH) j δ ^ (16 * (D.R.k : ℝ)) := by
    intro j δ
    rw [hfD]
    rfl
  unfold PairsAt
  intro j' _ j'' _ δ' δ'' S hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [Finset.sum_empty]
    exact mul_nonneg (massC_nonneg Y u) (mul_nonneg (termPairBoundFactor_nonneg large₂ CH Ch 16 j' δ') (termPairBoundFactor_nonneg large₂ CH Ch 16 j'' δ''))
  obtain ⟨hpp, hj1, hj2, hl1, hl2⟩ := hS p hp
  obtain ⟨hr1, hr2, -⟩ := hpp
  have hF := GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost GlobalTheory.T.exists_adaptedNormalForm_relevantTerm GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label GlobalTheory.T.rowLattice_term_adaptedNormalForm hK2
  obtain ⟨hD1, hDb1, hDle, hDble⟩ := hF p.1 hr1
  obtain ⟨hD1', hDb1', hDle', hDble'⟩ := hF p.2 hr2
  rw [hj1, hl1] at hD1 hDb1 hDle hDble
  rw [hj2, hl2] at hD1' hDb1' hDle' hDble'
  have hS1 : 1 ≤ k2S D (H1C large₂ CH) j' δ' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hS1' : 1 ≤ k2S D (H1C large₂ CH) j'' δ'' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))

  have hDA := le_trans hDle (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDA' := le_trans hDle' (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDbA := le_trans hDble (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hDbA' := le_trans hDble' (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hbound := hsum D.host.E D.R.k D.R.rS D.R.m (gS D) (Tu D u) large₂.sc.b (k2Del D j' δ') (k2Del D j'' δ'')
    (DbL D j' δ') (DbL D j'' δ'') (k2S D (H1C large₂ CH) j' δ') (k2S D (H1C large₂ CH) j'' δ'') hrk hm hClm' hm4 hm5 hClk'
    hlog hb2 hv1 hvb hg (hTu u).1 (hTu u).2 hS1 hS1' hD1 hD1' hDb1 hDb1' hDA hDA' hDbA hDbA'

  obtain ⟨W, HW, hemb, hrkW, hPD⟩ := GlobalTheory.T.definite_quotient_model_exists D large₂ X u hStd
  have hI := GlobalTheory.T.weightedTermPairs_sum_le_via_rows_genusMeans D large₂ X Y u hStd GlobalTheory.T.termsOverRow_compatible GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings GlobalTheory.T.rowsMeanC_holds W HW hemb
    (fun s M x x' => GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul _ _ HW (gS D) D.R.rS x x' s M)
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x')
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _)
    (fun Λ hΛ x x' hx hx' => GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound hMM hSR hHost GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hemb hrkW hPD Λ hΛ x x' hx hx')
    j' j'' δ' δ'' S hS
  rw [hNT] at hI
  have hstep := le_mul_sum_sum_of_ofReal_le_ennreal_sum _ _
    (fun x x' => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x *
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x')
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') (massC Y u) _
    (fun x x' => mul_nonneg (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _))
      (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _)))
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _) (massC_nonneg Y u) hI
  refine le_trans hstep ?_
  rw [hk2e, hk2e]
  exact mul_le_mul_of_nonneg_left hbound (massC_nonneg Y u)

end GlobalTheory.TypeAsm
