import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopConstantTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveComplexPoint
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveIsOrbit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPtsIntegralZeroLowerNE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeWithoutBigness

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem tensor_constLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) :
    (A.tensor (constLine c)).h z = A.h z * Real.exp (-c) := rfl

theorem tensor_constLine_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) : (A.tensor (constLine c)).a = A.a := by
  show A.a + (constLine (ι := ι) c).a = A.a
  simp [constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]

theorem isSmoothHerm_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (c : ℝ) :
    IsSmoothHerm (A.tensor (constLine c)) := by
  unfold IsSmoothHerm
  have : (A.tensor (constLine c)).h = fun z => A.h z * Real.exp (-c) := rfl
  rw [this]
  exact hA.mul contDiffOn_const

theorem leviForm_twist (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((A.tensor (constLine c)).h z)) z w =
      leviForm (fun z => Real.log (A.h z)) z w := by
  have hev : (fun z => Real.log ((A.tensor (constLine c)).h z)) =ᶠ[𝓝 z]
      (fun z => Real.log (A.h z) + (-c)) := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [tensor_constLine_h, Real.log_mul (A.pos z' hz').ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fderiv ℝ (fun z => Real.log ((A.tensor (constLine c)).h z))) z =
      fderiv ℝ (fderiv ℝ (fun z => Real.log (A.h z))) z := by
    rw [hev.fderiv.fderiv_eq]
    congr 1
    funext z'
    exact fderiv_add_const _
  unfold leviForm
  rw [h2]

theorem isSemipositiveRel_twist {P0 P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (h : IsSemipositiveRel P0 P A) (c : ℝ) : IsSemipositiveRel P0 P (A.tensor (constLine c)) := by
  refine ⟨isSmoothHerm_twist h.1 c, fun z hz w hw => ?_⟩
  rw [leviForm_twist A c hz.1 w]
  exact h.2 z hz w hw

theorem isConjInvariantH_twist {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : IsConjInvariantH A) (c : ℝ) :
    IsConjInvariantH (A.tensor (constLine c)) := by
  intro z
  rw [tensor_constLine_h, tensor_constLine_h, h z]

theorem nefOnFibres_twist {P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : NefOnFibres P A.a) (c : ℝ) :
    NefOnFibres P (A.tensor (constLine c)).a := by
  rw [tensor_constLine_a]
  exact h

theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Q : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Q La 1 D) : ∃ τ, 1 ≤ τ ∧ ∃ s ∈ La τ, s ≠ 0 ∧ Q τ s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k : ℕ, smallSectionCount Q La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hsub : Subsingleton {s : La (1 * k) // Q (1 * k) (s : Ω)} := by
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        have ha0 : (a : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) a a.2 h0 ha
        have hb0 : (b : Ω) = 0 := by
          by_contra h0
          exact hne (1 * k) (by omega) b b.2 h0 hb
        exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
      have hcard : Nat.card {s : La (1 * k) // Q (1 * k) (s : Ω)} ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr hsub
      have hlog : smallSectionCount Q La (1 * k) = 0 := by
        unfold smallSectionCount
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h <;> rw [h] <;> simp
      rw [hlog, zero_div]
  have : arVolP Q La 1 D = 0 := by
    unfold arVolP
    simp only [hzero]
    exact limsup_const 0
  linarith

theorem exists_gt_of_lt {N e' g T : ℝ} (hN : 0 < N) (h : N * e' * g < T) :
    ∃ e'', e' < e'' ∧ N * e'' * g < T := by
  by_cases hg : g ≤ 0
  · refine ⟨e' + 1, by linarith, ?_⟩
    have h1 : N * (e' + 1) * g = N * e' * g + N * g := by ring
    have h2 : N * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le hg
    linarith
  · push Not at hg
    have hd : 0 < (T - N * e' * g) / (2 * N * g) := div_pos (by linarith) (by positivity)
    refine ⟨e' + (T - N * e' * g) / (2 * N * g), by linarith, ?_⟩
    have h1 : N * (e' + (T - N * e' * g) / (2 * N * g)) * g = N * e' * g + (T - N * e' * g) / 2 := by
      field_simp
    rw [h1]
    linarith

end LatticeWithoutBigness

open LatticeWithoutBigness in

theorem LatticeWithoutBigness.proof (hG : ArithmeticVolumeBigRefined.Statement) (hT : TopConstantTwist.Statement)
    (hM : BirationalModelExists.Statement) (hS : SmallSectionPointHeight.Statement)
    (hfin : CurvePointsFinite.Statement) : LatticeWithoutBigness.Statement := by
  intro K _ ι _ P P0 D A e' F II hII har hP0 hsemi hnef hconj hF hdense
  have hA : IsSmoothHerm A := hsemi.1
  have : Nonempty K := har.1

  have hdeg : ∀ W : Ideal (MRing ι), IsArithVar W 1 → (0 : ℝ) < degC W := by
    intro W hW
    have : Finite (projPts W) := hfin K ι W hW
    obtain ⟨z, hz⟩ := IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.full K ι W hW
    have : Nonempty (projPts W) := ⟨Quot.mk _ ⟨z, hz⟩⟩
    have : 0 < Nat.card (projPts W) := Nat.card_pos
    exact_mod_cast this

  have hmc : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, II K ι W 1 ![A.tensor (constLine c)] =
      II K ι W 1 ![A] - ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by
    intro W hW c
    have h := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => c) (fun _ _ _ => rfl) hW
      (fun j => j.elim0) hA contDiffOn_const
    have e1 : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B] :=
      fun B => by
        funext i
        fin_cases i
        rfl
    rw [e1, e1] at h
    exact h
  have hlow : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ,
      c * degC W ≤ ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by
    intro W hW c
    exact PtsIntegralZeroLowerNE.proof K ι W _ (fun _ => c) c hW.2.1.2.1 (hfin K ι W hW)
      (fun _ _ _ _ => rfl) (fun _ _ => le_rfl)
  have h1P : (1 : MRing ι) ∉ P := fun h => har.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hfun : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun _ : Fin 1 => B) = ![B] := fun B => by
    funext i
    fin_cases i
    rfl
  rcases Nat.eq_zero_or_pos D with hD | hD
  ·
    subst hD
    obtain ⟨W, hWF, -⟩ := hdense 1 ⟨fun _ => 0, isMultiHomog_one⟩ h1P
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have : P.IsPrime := har.2.1.1
    have hWP : P = W :=
      CurveIsOrbit.eq_of_le_of_ringKrullDim_eq (d := 1 + Fintype.card K) hPW har.2.2.2 hW.2.2.2
    rw [← hWP] at hle
    have htw : II K ι P 1 (fun _ => A.tensor (constLine e')) =
        II K ι P 1 (fun _ => A) - ((1 : ℕ) : ℝ) * e' * geomDeg P A 0 := hT K ι P 0 A e' II hII har hA
    rw [hfun, hfun] at htw
    have hm := hmc P har e'
    have hl := hlow P har e'
    show II K ι P 1 (fun _ => A) ≤ ((1 : ℕ) : ℝ) * e' * geomDeg P A 0
    rw [hfun]
    push_cast at htw ⊢
    linarith
  ·
    obtain ⟨Ω, _, y, hyP, hbir⟩ := hM K ι P (D + 1) har
    subst hyP
    by_contra hlt
    push Not at hlt
    obtain ⟨e'', hgt, htop⟩ := exists_gt_of_lt (N := ((D + 1 : ℕ) : ℝ)) (by positivity) hlt
    have htw := hT K ι (mCoordIdeal y) D A e'' II hII har hA
    have hvol := hG K ι Ω y D (A.tensor (constLine e'')) P0 II hD hII har hbir hP0
      (isSemipositiveRel_twist hsemi e'') (nefOnFibres_twist hnef e'') (isConjInvariantH_twist hconj e'')
    have hpos : 0 < arVolP (IsSmallH (mCoordIdeal y) y (A.tensor (constLine e'')))
        (chartLatNm y (A.tensor (constLine e'')).a) 1 D := by
      linarith
    obtain ⟨τ, hτ, s, hsL, hs0, hsm⟩ := exists_small_section_of_arithmeticVolume_pos hpos
    obtain ⟨f, hfh, hfP, hfW⟩ := hS K ι Ω y D (A.tensor (constLine e'')) τ s II hII har hbir
      (isSmoothHerm_twist hA e'') hτ hsL hs0 hsm
    obtain ⟨W, hWF, hfW'⟩ := hdense f hfh hfP
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have h0 := hfW W hW hPW hfW'
    have hm := hmc W hW e''
    have hl := hlow W hW e''
    have hd := hdeg W hW
    nlinarith [mul_pos (sub_pos.mpr hgt) hd]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
