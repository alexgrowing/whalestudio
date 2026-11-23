import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankChartLatQMono
import Development.WeilBound.CoreStatements.HodgeTatePoints.KleimanInputUniverseZero
import Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins
import Development.WeilBound.CoreStatements.HodgeTatePoints.A36
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuaNum
import Development.WeilBound.CoreStatements.HodgeTatePoints.SiubOf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.NefSections

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem eval_le_top_add (P : Polynomial ℚ) (e : ℕ) (hP : P.natDegree ≤ e + 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ((P.eval (n : ℚ) : ℚ) : ℝ) ≤ ((P.coeff (e + 1) : ℚ) : ℝ) * (n : ℝ) ^ (e + 1) + C * (n : ℝ) ^ e := by
  refine ⟨∑ i ∈ Finset.range (e + 1), |((P.coeff i : ℚ) : ℝ)|, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_range_succ]
  push_cast
  rw [add_comm, Finset.sum_mul]
  refine add_le_add le_rfl (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ((P.coeff i : ℚ) : ℝ) * (n : ℝ) ^ i ≤ |((P.coeff i : ℚ) : ℝ)| * (n : ℝ) ^ i :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |((P.coeff i : ℚ) : ℝ)| * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 hi') (abs_nonneg _)

theorem finrank_secOver_nsmul_le (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (ν : K → ℤ)
    (hmod : IsModelWithBase F y k₀)
    (hdim : FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)))
    (hva : VeryAmple F y ν) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (Module.finrank F (secOver F y (n • ν)) : ℝ) ≤
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) * (n : ℝ) ^ (d + 1) /
        ((d + 1).factorial : ℝ) + C * (n : ℝ) ^ d := by
  have hpos : 0 < Fintype.card (ι k₀) := by
    obtain ⟨i, -⟩ := hmod.1 k₀
    exact Fintype.card_pos_iff.2 ⟨i⟩
  obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
  obtain ⟨Q, hQ⟩ := Kleiman.SectionsOverLocalization.BundleOfDeg.full F K ι Ω y k₀ N e hmod ν
  have hsub := (Kleiman.SectionsOverLocalization.ModelDim.proof F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
  have hvaQ := (PositivityTheory.HtPt.Ktw.a74 F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
  obtain ⟨-, P, hdeg, hlead, hev⟩ := PositivityTheory.HtPt.Ktw.a37 F Ω N _ (d + 1) Q hsub hvaQ
  have hnum := PositivityTheory.HtPt.Ktw.a18 F K ι Ω y k₀ N e _ rfl hmod (d + 1) (fun _ => Q) (fun _ => ν) (fun _ => hQ) hsub
  obtain ⟨C, hC⟩ := eval_le_top_add P d hdeg
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hsec : (Q.toSubSystem.pow n).secs = secOver F y (n • ν) := by
    have h := PositivityTheory.HtPt.Ktw.a66 F K ι Ω y k₀ N e _ rfl hmod Q ν hQ n 0
    rw [Kleiman.twistMul, Kleiman.SubSystem.twist_twistSys_zero] at h
    rw [h]
    simp
  rw [← hsec]
  have h1 : (Module.finrank F (Q.toSubSystem.pow n).secs : ℝ) = ((P.eval (n : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hn
  rw [h1]
  have hfac : ((d + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hco : ((P.coeff (d + 1) : ℚ) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) / ((d + 1).factorial : ℝ) := by
    have : P.coeff (d + 1) = (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℚ) /
        ((d + 1).factorial : ℚ) := by
      rw [eq_div_iff hfac, hlead, hnum]
    rw [this]; push_cast; rfl
  have := hC n hn1
  rw [hco] at this
  calc _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.CompanionTheory.NefSections

namespace GlobalTheory.CompanionTheory.NefSections

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem exists_rat_multilinear_le {M : Type} [AddCommGroup M] {n : ℕ}
    (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (μ e : M) (ε : ℚ) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t →
      ((f (fun _ => a • μ + m • e) : ℤ) : ℚ) ≤ (a : ℚ) ^ n * (((f fun _ => μ : ℤ) : ℚ) + ε) := by
  let g : ℚ → ℚ := fun t => PositivityTheory.HtPt.Siua.form f μ e (fun _ => 1) (fun _ => 1 * t)
  have hg : Continuous g := PositivityTheory.HtPt.Siua.form_cont f μ e (fun _ => 1) (fun _ => 1)
  have hg0 : g 0 = ((f fun _ => μ : ℤ) : ℚ) := by
    have h1 := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => 1) (fun _ => 0)
    simp only [one_smul, zero_smul, add_zero, Int.cast_one, Int.cast_zero] at h1
    simp only [g, mul_zero]
    rw [← h1]
  have hlt : g 0 < ((f fun _ => μ : ℤ) : ℚ) + ε := by rw [hg0]; linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℚ), g t < ((f fun _ => μ : ℤ) : ℚ) + ε ∧ 0 < t :=
    ((hg.continuousAt.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, hgt, ht⟩ := hev.exists
  refine ⟨t, ht, fun a m ha hm => ?_⟩
  have e2 : (fun _ : Fin n => a • μ + m • e) = fun _ => (a : ℤ) • μ + m • e := by
    funext i; simp
  have h2 := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => (a : ℤ)) (fun _ => m)
  have h4 := PositivityTheory.HtPt.Siua.form_smul f μ e (fun _ => 1) (fun _ => 1 * t) a
  have h6 : PositivityTheory.HtPt.Siua.form f μ e (fun _ => (((a : ℤ) : ℤ) : ℚ)) (fun _ => ((m : ℤ) : ℚ)) =
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (a : ℚ) * 1) (fun _ => (a : ℚ) * (1 * t)) := by
    congr 1 <;> funext i <;> push_cast
    · ring
    · rw [hm]; ring
  have hapos : (0 : ℚ) ≤ (a : ℚ) ^ n := by positivity
  rw [e2, h2, h6, h4]
  exact mul_le_mul_of_nonneg_left hgt.le hapos

theorem secOver_eq_chartLatQ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ) : secOver ℚ y β = chartLatQ y β 1 := by
  ext s
  constructor
  · intro hs c hc
    have h1 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hs c) hc
    have h2 : s * ∏ j, y ⟨j, c j⟩ ^ (-β j) ∈ chartRingOver ℚ y c := h1
    have h3 : ∀ j, -(((1 : ℕ) : ℤ) * β j) = -β j := fun j => by simp
    simp only [h3]
    exact h2
  · intro hs
    refine (Submodule.mem_iInf _).2 fun c => (Submodule.mem_iInf _).2 fun hc => ?_
    have h1 := hs c hc
    have h3 : ∀ j, -(((1 : ℕ) : ℤ) * β j) = -β j := fun j => by simp
    simp only [h3] at h1
    exact h1

theorem real_step {X G ε' ε C A nR T fc : ℝ} (d : ℕ) (hfc : 0 < fc) (hG : 0 ≤ G) (hε' : 0 < ε') (hε : 2 * ε' ≤ ε)
    (hA : 1 ≤ A) (hn : 0 ≤ nR) (hAT : A * nR ≤ T) (hX : X ≤ A ^ (d + 1) * (G + ε'))
    (hT : |C| * fc ≤ ε' * T) (h1T : 1 ≤ T) {v : ℝ} (hv : v ≤ X * nR ^ (d + 1) / fc + C * nR ^ d) :
    v ≤ (G + ε) * T ^ (d + 1) / fc := by
  have hT0 : 0 ≤ T := by linarith
  have hnT : nR ≤ T := by nlinarith
  have h1 : X * nR ^ (d + 1) / fc ≤ (G + ε') * T ^ (d + 1) / fc := by
    apply div_le_div_of_nonneg_right _ hfc.le
    calc X * nR ^ (d + 1) ≤ (A ^ (d + 1) * (G + ε')) * nR ^ (d + 1) :=
          mul_le_mul_of_nonneg_right hX (by positivity)
      _ = (G + ε') * (A * nR) ^ (d + 1) := by rw [mul_pow]; ring
      _ ≤ (G + ε') * T ^ (d + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hAT _) (by linarith)
  have h2 : C * nR ^ d ≤ ε' * T ^ (d + 1) / fc := by
    rw [le_div_iff₀ hfc]
    calc C * nR ^ d * fc ≤ |C| * T ^ d * fc := by
          apply mul_le_mul_of_nonneg_right _ hfc.le
          calc C * nR ^ d ≤ |C| * nR ^ d := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
            _ ≤ |C| * T ^ d := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hnT _) (abs_nonneg _)
      _ = (|C| * fc) * T ^ d := by ring
      _ ≤ (ε' * T) * T ^ d := mul_le_mul_of_nonneg_right hT (by positivity)
      _ = ε' * T ^ (d + 1) := by ring
  have h3 : (G + ε') * T ^ (d + 1) / fc + ε' * T ^ (d + 1) / fc ≤ (G + ε) * T ^ (d + 1) / fc := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hfc.le
    have : 0 ≤ T ^ (d + 1) := by positivity
    nlinarith
  linarith

theorem twist_le {K : Type} [Fintype K] (a b : K → ℤ) (a₀ : ℕ) :
    ∃ B : ℕ, ∀ (τ q : ℕ), 1 ≤ a₀ → 1 ≤ q → B ≤ τ / a₀ →
      (τ : ℤ) • a + b ≤ ((τ / a₀ * a₀ : ℕ) : ℤ) • a + fun _ => ((τ / a₀ * q : ℕ) : ℤ) := by
  refine ⟨∑ k, (a₀ * |a k| + |b k|).toNat, fun τ q ha hq hB k => ?_⟩
  set n := τ / a₀ with hn
  have hτ : τ = n * a₀ + τ % a₀ := by rw [hn]; exact (Nat.div_add_mod' τ a₀).symm
  have hr : τ % a₀ < a₀ := Nat.mod_lt _ ha
  set r := τ % a₀ with hrdef
  have hk : (a₀ * |a k| + |b k|).toNat ≤ n :=
    le_trans (Finset.single_le_sum (f := fun k => (a₀ * |a k| + |b k|).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)) hB
  have hnn : (0 : ℤ) ≤ a₀ * |a k| + |b k| := by positivity
  have hk' : (a₀ : ℤ) * |a k| + |b k| ≤ n := by
    have : (((a₀ * |a k| + |b k|).toNat : ℕ) : ℤ) ≤ n := by exact_mod_cast hk
    rwa [Int.toNat_of_nonneg hnn] at this
  have hra : (r : ℤ) * a k ≤ a₀ * |a k| := by
    calc (r : ℤ) * a k ≤ r * |a k| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ a₀ * |a k| := mul_le_mul_of_nonneg_right (by exact_mod_cast hr.le) (abs_nonneg _)
  have hbk : b k ≤ |b k| := le_abs_self _
  have hnq : (n : ℤ) ≤ ((n * q : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_right n hq
  have hτ' : (τ : ℤ) = n * a₀ + r := by exact_mod_cast hτ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hτ']
  push_cast at hnq ⊢
  nlinarith

end GlobalTheory.CompanionTheory.NefSections

namespace GlobalTheory.CompanionTheory.NefSections

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem finrank_chartLatQ_nsmul_add_le : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) →
    Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) ≤
        ((genDeg (mCoordIdeal y) D a : ℝ) + ε) * (n : ℝ) ^ D / (D.factorial : ℝ) := by
  intro K _ ι _ Ω _ _ y D a b hD hV _ hN ε hε
  classical
  have : Nonempty K := hV.1
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hI : genIdeal y = mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
  have hP := isProjVarF_map_of_isArithVar hV
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  have hdim : FieldNumbers.relDim (mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
  have hnef : IsNef ℚ y a := fun W hW hle hW1 =>
    NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hN W
      ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
      (hI.le.trans hle)
  obtain ⟨hNP, hKl, -⟩ := PositivityTheory.HtPt.Ktw.k_twins PositivityTheory.HtPt.Kra.kleiman_input_universe_zero
  have hGdef : genDeg (mCoordIdeal y) (d + 1) a =
      NumbersDVR.intNum ℚ (mIdealOver ℚ y) (fun _ : Fin (d + 1) => a) := by
    rw [← hI]; rfl
  have hG0 : 0 ≤ genDeg (mCoordIdeal y) (d + 1) a := by
    rw [hGdef]; exact hNP ℚ K ι Ω y (d + 1) (fun _ => a) hnz hdim (fun _ => hnef)
  have hmod := (SegreBase.proof ℚ K ι Ω y hnz).1
  have hdim' : FieldNumbers.relDim (mIdealOver ℚ (segreJoin y)) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    (SegreDim.proof ℚ K ι Ω y hnz).trans hdim
  have hnef' : IsNef ℚ (segreJoin y) (pullDeg a) :=
    (SegreNef.proof SegreDim.proof SegreNum.proof ℚ K ι Ω y hnz a).2 hnef
  have hPr := isMultiProjPrime_mIdealOver (S := ℚ) (segreJoin y) hmod.1
  obtain ⟨f, hf⟩ := PositivityTheory.HtPt.Siub.exists_multilinear (M := Unit ⊕ K → ℤ) (n := d + 1)
    (fun v => NumbersDVR.intNum ℚ (mIdealOver ℚ (segreJoin y)) v)
    (FieldNumbers.IntNumAdd.full ℚ _ _ (mIdealOver ℚ (segreJoin y)) hPr.multiHomog hPr.relevant (d + 1) hdim')
  have hfa : f (fun _ => pullDeg a) = genDeg (mCoordIdeal y) (d + 1) a := by
    rw [hf, hGdef]
    exact SegreNum.proof ℚ K ι Ω y hnz (d + 1) (fun _ => a)
  obtain ⟨ε', hε'0, hε'⟩ : ∃ ε' : ℚ, 0 < ε' ∧ 2 * (ε' : ℝ) ≤ ε := by
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
    exact ⟨q, by exact_mod_cast hq0, by linarith⟩
  obtain ⟨t, ht, hbd⟩ := exists_rat_multilinear_le f (pullDeg a) (baseDeg (Sum.inl ())) ε' hε'0
  obtain ⟨a₀, m, ha₀, hm, hva⟩ := hKl (d + 1) ℚ (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) hmod hdim'
    (pullDeg a) hnef' t ht
  have hmpos : 0 < m := by
    have ha' : (0 : ℚ) < a₀ := by exact_mod_cast ha₀
    have : (0 : ℚ) < m := by rw [hm]; exact mul_pos ha' ht
    exact_mod_cast this
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  have hq : 1 ≤ q := by exact_mod_cast hmpos
  obtain ⟨C, hC⟩ := finrank_secOver_nsmul_le ℚ (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d _ hmod hdim' hva
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hC
  obtain ⟨B, hB⟩ := twist_le a b a₀
  have hsec : ∀ n : ℕ, secOver ℚ (segreJoin y) (n • (a₀ • pullDeg a + (q : ℤ) • baseDeg (Sum.inl ()))) =
      chartLatQ y (((n * a₀ : ℕ) : ℤ) • a + fun _ => ((n * q : ℕ) : ℤ)) 1 := by
    intro n
    rw [← secOver_eq_chartLatQ, ← SegreTwist.proof ℚ K ι Ω y hnz]
    congr 1
    funext k
    rcases k with k | k <;> simp [pullDeg, baseDeg, Pi.single_apply] <;> ring
  have hfc : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hXq : ((f (fun _ => a₀ • pullDeg a + (q : ℤ) • baseDeg (Sum.inl ())) : ℤ) : ℝ) ≤
      (a₀ : ℝ) ^ (d + 1) * ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) + (ε' : ℝ)) := by
    have h := hbd a₀ q ha₀ hm
    rw [hfa] at h
    exact_mod_cast h
  have hε'R : (0 : ℝ) < ε' := by exact_mod_cast hε'0
  obtain ⟨T₀, hT₀⟩ := exists_nat_ge (|C| * ((d + 1).factorial : ℝ) / (ε' : ℝ))
  filter_upwards [eventually_ge_atTop (a₀ * (max n₀ B + 1)), eventually_ge_atTop T₀] with τ hτ hτ₀
  have hdiv : max n₀ B + 1 ≤ τ / a₀ := (Nat.le_div_iff_mul_le ha₀).2 (by rwa [mul_comm] at hτ)
  have hn₁ : n₀ ≤ τ / a₀ := by omega
  have hB₁ : B ≤ τ / a₀ := by omega
  have h1τ : 1 ≤ τ := by
    have : 1 ≤ τ / a₀ := by omega
    exact le_trans this (Nat.div_le_self _ _)
  have hmono := GlobalTheory.CompanionTheory.ChartSections.finrank_chartLatQ_mono K ι Ω y _ _ hnz (hB τ q ha₀ hq hB₁)
    (GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y (d + 1) _ hV)
  have hup := hn₀ (τ / a₀) hn₁
  rw [hsec, ← hf] at hup
  have hmonoR : (Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + b) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((τ / a₀ * a₀ : ℕ) : ℤ) • a + fun _ => ((τ / a₀ * q : ℕ) : ℤ)) 1) : ℝ) := by
    exact_mod_cast hmono
  refine real_step d hfc (by exact_mod_cast hG0) hε'R hε' (A := (a₀ : ℝ)) (nR := ((τ / a₀ : ℕ) : ℝ)) (T := (τ : ℝ))
    (C := C) (by exact_mod_cast ha₀) (by positivity) ?_ hXq ?_ (by exact_mod_cast h1τ) (hmonoR.trans hup)
  · have : a₀ * (τ / a₀) ≤ τ := Nat.mul_div_le τ a₀
    exact_mod_cast this
  · have h1 : |C| * ((d + 1).factorial : ℝ) / (ε' : ℝ) ≤ τ := hT₀.trans (by exact_mod_cast hτ₀)
    rw [div_le_iff₀ hε'R] at h1
    linarith

end GlobalTheory.CompanionTheory.NefSections
