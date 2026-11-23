import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSubEqChartSecOver
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
import Development.WeilBound.CoreStatements.HodgeTatePoints.KleimanInputUniverseZero
import Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuKodaira
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuaNum
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiubOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankChartLatQMono
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.NefLower

open PositivityTheory.HtPt.Siua in

theorem num_lower {M : Type} [AddCommGroup M] (d : ℕ)
    (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => M) ℤ) (μ e : M) (δ : ℚ) (hδ : 0 < δ) :
    ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t →
      ((f (fun _ => μ) : ℚ) - δ) * (a : ℚ) ^ (d + 1) ≤
        (f (fun _ => a • μ + m • e) : ℚ) - ((d + 1 : ℕ) : ℚ) *
          (f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) (m • e)) : ℚ) := by
  let x : Fin (d + 1) → ℤ := Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => 1) 0
  let g : ℚ → ℚ := fun t => form f μ e (fun _ => 1) (fun _ => 1 * t) -
    ((d + 1 : ℕ) : ℚ) * form f μ e (fun i => x i) (fun _ => 1 * t)
  have hg : Continuous g :=
    (form_cont f μ e (fun _ => 1) (fun _ => 1)).sub (continuous_const.mul (form_cont f μ e _ _))
  have hg0 : (f (fun _ => μ) : ℚ) - δ < g 0 := by
    have h1 := form_cast f μ e (fun _ => 1) (fun _ => 0)
    have h2 := form_cast f μ e x (fun _ => 0)
    have h3 : f (fun i => x i • μ + (0 : ℤ) • e) = 0 :=
      f.map_coord_zero (Fin.last d) (by simp [x])
    rw [h3] at h2
    simp only [one_smul, zero_smul, add_zero, Int.cast_one, Int.cast_zero] at h1 h2
    simp only [g, mul_zero]
    rw [← h1, ← h2, mul_zero, sub_zero]
    linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℚ), (f (fun _ => μ) : ℚ) - δ < g t ∧ 0 < t :=
    ((hg.continuousAt.eventually (lt_mem_nhds hg0)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, hgt, ht⟩ := hev.exists
  refine ⟨t, ht, fun a m ha hm => ?_⟩
  have e1 : (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) (m • e)) =
      fun i => ((a : ℤ) * x i) • μ + m • e := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [x]
  have e2 : (fun _ : Fin (d + 1) => a • μ + m • e) = fun _ => (a : ℤ) • μ + m • e := by
    funext i; simp
  have h1 := form_cast f μ e (fun i => (a : ℤ) * x i) (fun _ => m)
  have h2 := form_cast f μ e (fun _ => (a : ℤ)) (fun _ => m)
  have h3 := form_smul f μ e (fun i => x i) (fun _ => 1 * t) a
  have h4 := form_smul f μ e (fun _ => 1) (fun _ => 1 * t) a
  have h5 : form f μ e (fun i => (((a : ℤ) * x i : ℤ) : ℚ)) (fun _ => ((m : ℤ) : ℚ)) =
      form f μ e (fun i => (a : ℚ) * x i) (fun _ => (a : ℚ) * (1 * t)) := by
    congr 1 <;> funext i <;> push_cast
    · rfl
    · rw [hm]; ring
  have h6 : form f μ e (fun _ => (((a : ℤ) : ℤ) : ℚ)) (fun _ => ((m : ℤ) : ℚ)) =
      form f μ e (fun _ => (a : ℚ) * 1) (fun _ => (a : ℚ) * (1 * t)) := by
    congr 1 <;> funext i <;> push_cast
    · ring
    · rw [hm]; ring
  have hapos : (0 : ℚ) < (a : ℚ) ^ (d + 1) := pow_pos (by exact_mod_cast ha) _
  have hfin := mul_lt_mul_of_pos_left hgt hapos
  rw [e1, e2, h1, h2, h5, h6, h3, h4]
  simp only [g] at hfin
  push_cast at hfin ⊢
  nlinarith [hfin]

theorem eventually_lower (f : ℕ → ℝ) (A C : ℝ) (hA : 0 ≤ A) (d a₀ L : ℕ) (ha : 1 ≤ a₀)
    (h : ∀ᶠ N : ℕ in atTop, ∃ m : ℕ, a₀ * m ≤ N ∧ N ≤ a₀ * m + L ∧
      A * (a₀ : ℝ) ^ (d + 1) * (m : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (m : ℝ) ^ d ≤ f N)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (A - ε) * (N : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤ f N := by
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast (d + 1).factorial_pos
  set C' : ℝ := max C 0 with hC'
  have hlim : Tendsto (fun N : ℕ => A * (1 - (L : ℝ) / N) ^ (d + 1) -
      ((d + 1).factorial : ℝ) * C' * (1 / (N : ℝ))) atTop (𝓝 (A * (1 - 0) ^ (d + 1) -
        ((d + 1).factorial : ℝ) * C' * 0)) := by
    have h0 : Tendsto (fun N : ℕ => (L : ℝ) / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h1 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    exact (((tendsto_const_nhds.sub h0).pow (d + 1)).const_mul A).sub (h1.const_mul _)
  have hval : A * (1 - 0 : ℝ) ^ (d + 1) - ((d + 1).factorial : ℝ) * C' * 0 = A := by simp
  rw [hval] at hlim
  have hev := hlim.eventually (lt_mem_nhds (show A - ε < A by linarith))
  filter_upwards [h, hev, eventually_gt_atTop L, eventually_gt_atTop 0] with N ⟨m, hm1, hm2, hm3⟩ hN hNL hN0
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hNL' : (L : ℝ) < (N : ℝ) := by exact_mod_cast hNL
  have hfrac : (1 - (L : ℝ) / N) * N = N - L := by field_simp
  have hm1' : ((a₀ : ℝ) * m) ≤ N := by exact_mod_cast hm1
  have hm2' : (N : ℝ) ≤ a₀ * m + L := by exact_mod_cast hm2
  have ha' : (1 : ℝ) ≤ a₀ := by exact_mod_cast ha
  have hmN : (m : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hpow : ((N : ℝ) - L) ^ (d + 1) ≤ ((a₀ : ℝ) * m) ^ (d + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hCm : C * (m : ℝ) ^ d ≤ C' * (N : ℝ) ^ d := by
    have h1 : (m : ℝ) ^ d ≤ (N : ℝ) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hmN _
    have h2 : C ≤ C' := le_max_left _ _
    have h3 : 0 ≤ C' := le_max_right _ _
    have h4 : (0 : ℝ) ≤ (m : ℝ) ^ d := by positivity
    nlinarith
  have hNpow : (0 : ℝ) < (N : ℝ) ^ (d + 1) := pow_pos hN' _
  have key := mul_lt_mul_of_pos_right hN hNpow
  have e1 : (A * (1 - (L : ℝ) / N) ^ (d + 1) - ((d + 1).factorial : ℝ) * C' * (1 / (N : ℝ))) * (N : ℝ) ^ (d + 1) =
      A * ((N : ℝ) - L) ^ (d + 1) - ((d + 1).factorial : ℝ) * C' * (N : ℝ) ^ d := by
    rw [← hfrac, mul_pow, pow_succ (N : ℝ) d]
    field_simp
  rw [e1] at key
  have e2 : A * (a₀ : ℝ) ^ (d + 1) * (m : ℝ) ^ (d + 1) = A * ((a₀ : ℝ) * m) ^ (d + 1) := by
    rw [mul_pow]; ring
  rw [e2] at hm3
  have hAp := mul_le_mul_of_nonneg_left hpow hA
  rw [div_le_iff₀ hfac]
  have hm4 : A * ((a₀ : ℝ) * m) ^ (d + 1) - ((d + 1).factorial : ℝ) * (C * (m : ℝ) ^ d) ≤
      f N * ((d + 1).factorial : ℝ) := by
    have := mul_le_mul_of_nonneg_right hm3 hfac.le
    rw [sub_mul, div_mul_cancel₀ _ hfac.ne'] at this
    linarith
  have hCm' := mul_le_mul_of_nonneg_left hCm hfac.le
  nlinarith

section Sections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_secOver (y : (Σ k, ι k) → Ω) (β : K → ℤ) :
    chartLatQ y β 1 = KH.secOver ℚ y β := by
  ext s
  simp only [KH.secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c hc
    have h1 := h c hc
    simp only [Nat.cast_one, one_mul] at h1
    exact h1
  · intro h c hc
    show s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * β k)) ∈ chartRingQ y c
    simp only [Nat.cast_one, one_mul]
    exact h c hc

theorem finrank_le_add_of_mem (y : (Σ k, ι k) → Ω) (β γ : K → ℤ) (e : Ω) (he0 : e ≠ 0)
    (he : e ∈ chartLatQ y γ 1) (hfd : FiniteDimensional ℚ (chartLatQ y (β + γ) 1)) :
    Module.finrank ℚ (chartLatQ y β 1) ≤ Module.finrank ℚ (chartLatQ y (β + γ) 1) := by
  have hmem : ∀ s ∈ chartLatQ y β 1, s * e ∈ chartLatQ y (β + γ) 1 := by
    intro s hs
    rw [chartLatQ_eq_secOver] at hs he ⊢
    exact GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.secOver_mul y hs he
  let g : chartLatQ y β 1 →ₗ[ℚ] chartLatQ y (β + γ) 1 :=
    { toFun := fun s => ⟨s.1 * e, hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := g) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ he0 (congrArg Subtype.val hst))

theorem pow_mem_chartLatQ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (e : Ω) (he : e ∈ chartLatQ y γ 1) (c : ℕ) :
    e ^ c ∈ chartLatQ y ((c : ℤ) • γ) 1 := by
  rw [chartLatQ_eq_secOver] at he ⊢
  exact GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.pow_mem_secOver y he c

end Sections

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization in

theorem count_lower (hK : VeryAmpleNefPlusAmple.Statement) (hS : SectionCount.Statement)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (hV : IsArithVar (mCoordIdeal y) (d + 1 + 1))
    (hN : NefOnGenericDeg (mCoordIdeal y) a) (δ : ℚ) (hδ : 0 < δ) :
    ∃ (a₀ : ℕ) (C : ℝ), 1 ≤ a₀ ∧ ∀ n : ℕ, 1 ≤ n →
      ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ)) * (a₀ : ℝ) ^ (d + 1) * (n : ℝ) ^ (d + 1) /
          ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank ℚ (chartLatQ y (((n * a₀ : ℕ) : ℤ) • a) 1) : ℝ) := by
  let _ : DecidableEq K := fun x y => Classical.propDecidable (x = y)
  have : Nonempty K := hV.1
  have hI : KH.genIdeal y = KH.mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
  have hP := isProjVarF_map_of_isArithVar hV
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  have hdim : FieldNumbers.relDim (KH.mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
  have hnef : IsNef ℚ y a := fun W hW hle hW1 =>
    NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hN W
      ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
      (hI.le.trans hle)
  have hmodel := (SegreBase.proof ℚ K ι Ω y hnz).1
  have hdim' := (SegreDim.proof ℚ K ι Ω y hnz).trans hdim
  have hnef' := (SegreNef.proof SegreDim.proof SegreNum.proof ℚ K ι Ω y hnz a).2 hnef
  have hPr := isMultiProjPrime_mIdealOver (S := ℚ) (segreJoin y) hmodel.1
  obtain ⟨f, hf⟩ := PositivityTheory.HtPt.Siub.exists_multilinear (M := Unit ⊕ K → ℤ) (n := d + 1)
    (fun v => NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y)) v)
    (FieldNumbers.IntNumAdd.full ℚ (Unit ⊕ K) _ (KH.mIdealOver ℚ (segreJoin y)) hPr.multiHomog
      hPr.relevant (d + 1) hdim')
  obtain ⟨t, ht, hlt⟩ := num_lower d f (pullDeg a) (baseDeg (Sum.inl ())) δ hδ
  obtain ⟨a₀, m, ha, hm, hva⟩ := hK (d + 1) ℚ _ _ Ω (segreJoin y) (Sum.inl ()) hmodel hdim'
    (pullDeg a) hnef' t ht
  have hmpos : 0 < m := by
    have ha' : (0 : ℚ) < a₀ := by exact_mod_cast ha
    have : (0 : ℚ) < m := by rw [hm]; exact mul_pos ha' ht
    exact_mod_cast this
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  have hr : 0 < r := by exact_mod_cast hmpos
  obtain ⟨C, hC⟩ := hS ℚ (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d
    (a₀ • pullDeg a + (r : ℤ) • baseDeg (Sum.inl ())) r hmodel hdim' hva (by omega)
  refine ⟨a₀, C, ha, fun n hn => ?_⟩
  have h1 := hC n hn
  have e : n • (a₀ • pullDeg (K₁ := Unit) a + (r : ℤ) • baseDeg (Sum.inl ()) - r • baseDeg (Sum.inl ())) =
      pullDeg (K₁ := Unit) (((n * a₀ : ℕ) : ℤ) • a) := by
    funext k
    cases k <;> simp [pullDeg]
    ring
  rw [e, (SegreBase.proof ℚ K ι Ω y hnz).2.1, ← chartLatQ_eq_secOver] at h1
  have hlt' := hlt a₀ (r : ℤ) ha hm
  rw [hf, hf, hf] at hlt'
  have hG : NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y)) (fun _ : Fin (d + 1) => pullDeg a) =
      genDeg (mCoordIdeal y) (d + 1) a := by
    rw [SegreNum.proof ℚ K ι Ω y hnz (d + 1) (fun _ => a), ← hI]
    rfl
  rw [hG] at hlt'
  have hq : ((r : ℤ)) • baseDeg (K := Unit ⊕ K) (Sum.inl ()) = r • baseDeg (Sum.inl ()) := by
    rw [← natCast_zsmul]
  rw [← hq] at h1
  have hR : ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ)) * (a₀ : ℝ) ^ (d + 1) ≤
      (NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y))
        (fun _ : Fin (d + 1) => a₀ • pullDeg a + (r : ℤ) • baseDeg (Sum.inl ())) : ℝ) -
      ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y))
        (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ)
          (fun _ : Fin d => a₀ • pullDeg a + (r : ℤ) • baseDeg (Sum.inl ()))
          ((r : ℤ) • baseDeg (Sum.inl ()))) : ℝ) := by
    exact_mod_cast (Rat.cast_le (K := ℝ)).2 hlt'
  have hfac : (0 : ℝ) ≤ (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hR hfac
  simp only [mul_div_assoc] at h1 ⊢
  linarith

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 in

theorem lower_of_pos (hK : VeryAmpleNefPlusAmple.Statement) (hS : SectionCount.Statement)
    (hKod : KodairaGeneric.Statement)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (a b : K → ℤ) (hV : IsArithVar (mCoordIdeal y) (d + 1 + 1))
    (hB : Birational y) (hN : NefOnGenericDeg (mCoordIdeal y) a) (ε : ℝ) (hε : 0 < ε)
    (hpos : ε < (genDeg (mCoordIdeal y) (d + 1) a : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - ε) * (N : ℝ) ^ (d + 1) /
        ((d + 1).factorial : ℝ) ≤ (Module.finrank ℚ (chartLatQ y ((N : ℤ) • a + b) 1) : ℝ) := by
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  obtain ⟨δ, hδ0, hδ1⟩ := exists_rat_btwn hε
  have hδ0' : 0 < δ := by exact_mod_cast hδ0
  obtain ⟨a₀, C, ha, hcount⟩ := count_lower hK hS K ι Ω y d a hV hN δ hδ0'
  have hGpos : 0 < genDeg (mCoordIdeal y) (d + 1) a := by
    have : (0 : ℝ) < (genDeg (mCoordIdeal y) (d + 1) a : ℝ) := hε.trans hpos
    exact_mod_cast this
  obtain ⟨k, e, hk, he0, he⟩ := hKod K ι Ω y (d + 1) a (by omega) hV hB hN hGpos
  obtain ⟨B, hB'⟩ : ∃ B : ℕ, ∀ r : ℕ, r < a₀ → ∀ κ, -(B : ℤ) ≤ (r : ℤ) * a κ + b κ := by
    refine ⟨∑ κ, (a₀ * (a κ).natAbs + (b κ).natAbs), fun r hr κ => ?_⟩
    have h1 : a₀ * (a κ).natAbs + (b κ).natAbs ≤ ∑ κ, (a₀ * (a κ).natAbs + (b κ).natAbs) :=
      Finset.single_le_sum (f := fun κ => a₀ * (a κ).natAbs + (b κ).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)
    have h1' : (a₀ : ℤ) * |a κ| + |b κ| ≤ ((∑ κ, (a₀ * (a κ).natAbs + (b κ).natAbs) : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      exact_mod_cast h1
    have h2 : -|b κ| ≤ b κ := neg_abs_le _
    have h3 : -|a κ| ≤ a κ := neg_abs_le _
    have h4 : (r : ℤ) ≤ a₀ := by exact_mod_cast hr.le
    have h5 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
    have h6 : (0 : ℤ) ≤ |a κ| := abs_nonneg _
    nlinarith
  have ha0 : 0 < a₀ := ha
  have hmain := eventually_lower
    (fun N : ℕ => (Module.finrank ℚ (chartLatQ y ((N : ℤ) • a + b) 1) : ℝ))
    ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ)) C (by linarith) d a₀ (a₀ * (B * k) + a₀) ha ?_
    (ε - δ) (by linarith)
  · have e' : (genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ) - (ε - δ) =
        (genDeg (mCoordIdeal y) (d + 1) a : ℝ) - ε := by ring
    rw [e'] at hmain
    exact hmain
  · filter_upwards [eventually_ge_atTop (a₀ * (B * k + 1))] with N hN1
    have hNr : a₀ * (N / a₀) + N % a₀ = N := Nat.div_add_mod N a₀
    have hr : N % a₀ < a₀ := Nat.mod_lt _ ha0
    have hn : B * k + 1 ≤ N / a₀ := (Nat.le_div_iff_mul_le ha0).2 (by rw [Nat.mul_comm]; exact hN1)
    obtain ⟨m, hm⟩ : ∃ m, N / a₀ = m + B * k := ⟨N / a₀ - B * k, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hmul : a₀ * (N / a₀) = a₀ * m + a₀ * (B * k) := by rw [hm, Nat.mul_add]
    refine ⟨m, by omega, by omega, ?_⟩
    refine (hcount m hm1).trans ?_
    have hce := pow_mem_chartLatQ y ((k : ℤ) • a - 1) e he (a₀ * B)
    have hfd := fun β => GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y (d + 1) β hV
    have s1 := finrank_le_add_of_mem y (((m * a₀ : ℕ) : ℤ) • a) (((a₀ * B : ℕ) : ℤ) • ((k : ℤ) • a - 1))
      (e ^ (a₀ * B)) (pow_ne_zero _ he0) hce (hfd _)
    have hle : (((m * a₀ : ℕ) : ℤ) • a + ((a₀ * B : ℕ) : ℤ) • ((k : ℤ) • a - 1)) ≤ (N : ℤ) • a + b := by
      intro κ
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
      have hNz : (N : ℤ) = (a₀ : ℤ) * (m + B * k) + ((N % a₀ : ℕ) : ℤ) := by
        have : N = a₀ * (m + B * k) + N % a₀ := by rw [← hm]; exact hNr.symm
        exact_mod_cast this
      have hb := hB' (N % a₀) hr κ
      have hBB : (B : ℤ) ≤ (a₀ : ℤ) * B := by
        have : B ≤ a₀ * B := Nat.le_mul_of_pos_left _ ha0
        exact_mod_cast this
      have hdiff : (N : ℤ) * a κ + b κ - (((m * a₀ : ℕ) : ℤ) * a κ + ((a₀ * B : ℕ) : ℤ) * ((k : ℤ) * a κ - 1)) =
          ((N % a₀ : ℕ) : ℤ) * a κ + b κ + (a₀ : ℤ) * B := by
        rw [hNz]; push_cast; ring
      linarith
    have s2 := GlobalTheory.CompanionTheory.ChartSections.finrank_chartLatQ_mono K ι Ω y _ ((N : ℤ) • a + b) hnz hle (hfd _)
    exact_mod_cast s1.trans s2

theorem nef_sections_lower : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ((genDeg (mCoordIdeal y) D a : ℝ) - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) := by
  intro K _ ι _ Ω _ _ y D a b hD hV hB hN ε hε
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  by_cases hG : (genDeg (mCoordIdeal y) (d + 1) a : ℝ) ≤ ε
  · refine Eventually.of_forall fun n => ?_
    have h1 : ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - ε) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) (by positivity)
    exact h1.trans (Nat.cast_nonneg _)
  · obtain ⟨-, hK, hS⟩ := PositivityTheory.HtPt.Ktw.k_twins PositivityTheory.HtPt.Kra.kleiman_input_universe_zero
    exact lower_of_pos hK hS (PositivityTheory.HtPt.Siua.siu_kodaira hK hS) K ι Ω y d a b hV hB hN ε hε
      (not_le.mp hG)

end GlobalTheory.CompanionTheory.NefLower
