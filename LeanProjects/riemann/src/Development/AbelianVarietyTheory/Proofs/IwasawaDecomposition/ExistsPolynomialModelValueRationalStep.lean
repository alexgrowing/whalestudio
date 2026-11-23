import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsSharpAtOfValTied
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CmpEx

theorem lift_ratSpan (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hP : P ∈ RatSpan D lam) :
    ∃ Q0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      Q0 ∈ WtPol D.what₂.LL (fun τ r => (lam τ).natW r) ∧ MvPolynomial.map D.what₂.embLL Q0 = P := by
  have hle : RatSpan D lam ≤ AddSubgroup.map
      (MvPolynomial.map D.what₂.embLL : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL →+* _).toAddMonoidHom
      (WtPol D.what₂.LL (fun τ r => (lam τ).natW r)).toAddSubgroup := by
    unfold RatSpan
    rw [AddSubgroup.closure_le]
    rintro p ⟨r, f, hf, rfl⟩
    refine ⟨r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_, ?_⟩
    · show _ ∈ WtPol _ _
      apply Submodule.smul_mem
      apply GlobalTheory.KerWt.VV_le_WtPol lam
      unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
      apply Submodule.subset_span
      refine ⟨fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ), fun τ => ?_, rfl⟩
      have h1 : MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ) ∈ delSq D.what₂.LL n (lam τ) := by
        rw [← GlobalTheory.Published.span_map_delSq ℤ D.what₂.LL (Int.castRingHom D.what₂.LL) n (lam τ)]
        exact Submodule.subset_span ⟨f τ, hf τ, rfl⟩
      exact Formalism.GradedWeylDivisibility.weylLeDual D.what₂.LL n n le_rfl _ (GlobalTheory.FormsSharpTie.natW_antitone (lam τ)) h1
    · have hc : D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.map_C, Formalism.L2.Forms.ten, map_prod, MvPolynomial.map_rename, MvPolynomial.map_map, hc]
  obtain ⟨Q0, hQ0, e⟩ := hle hP
  exact ⟨Q0, hQ0, e⟩

theorem wt0 : ∀ (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (τ : D.what₂.Tau), 0 ≤ shiftOf (lamTG M 0) τ + twB D u μ 0 τ ∧ ∀ r : Fin (D.R.N 0), (M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat = nuT D u 0 τ r := by
  intro D u μ C A P M τ
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hN : D.R.N 0 = D.R.k := by simp [Ranks.N]
  have hN0 : 0 < D.R.N 0 := hN ▸ hk
  have hw : ∀ r : Fin (D.R.N 0), (((M.lam 0 τ).w r : ℤ) : ℚ) =
      (D.hcW u τ).u ⟨r.1, by omega⟩ - (((D.R.k : ℚ) - 1) / 2 - (r.1 : ℚ)) := by
    intro r
    rw [M.lam_eq 0 (Nat.zero_le _) τ r, dif_pos (by omega)]
    rfl
  have hds0 : (M.lam 0 τ).detShift = (M.lam 0 τ).w ⟨D.R.N 0 - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hN0]
  have hds : ((M.lam 0 τ).detShift : ℚ) = (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ + ((D.R.k : ℚ) - 1) / 2 := by
    rw [hds0, hw]
    have e1 : (D.hcW u τ).u ⟨D.R.N 0 - 1, by omega⟩ = (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ :=
      congrArg _ (Fin.ext (by simp only [hN]))
    simp only [e1]
    have e2 : ((D.R.N 0 - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
      rw [hN, Nat.cast_sub (by omega)]
      simp
    rw [e2]
    ring
  have hsh : shiftOf (lamTG M 0) τ = (M.lam 0 τ).detShift := by
    simp [shiftOf, lamTG, Formalism.L2.Forms.shW, DomWeight.detShift]
  have htw : ((twB D u μ 0 τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨0, hm⟩ - ((D.R.k : ℚ) + D.R.t + 1) / 2 := by
    show (((D.chTw u μ).sSharp 0 τ : ℤ) : ℚ) = _
    rw [(D.chTw u μ).sSharp_eq 0 hm τ]
    unfold sExp' Ranks.N
    push_cast
    ring
  have hpos : 0 ≤ shiftOf (lamTG M 0) τ + twB D u μ 0 τ := by
    have h1 := (D.hcW u τ).u_last_gt hk hm
    have h2 := (D.hcW u τ).gap_be ⟨0, hm⟩
    have h3 : (0 : ℚ) ≤ ((shiftOf (lamTG M 0) τ + twB D u μ 0 τ : ℤ) : ℚ) := by
      push_cast
      rw [hsh, hds, htw]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith
    exact_mod_cast h3
  refine ⟨hpos, fun r => ?_⟩
  have hr : r.1 < D.R.k := by omega
  have hanti : (M.lam 0 τ).detShift ≤ (M.lam 0 τ).w r := by
    rw [hds0]
    exact (M.lam 0 τ).anti (Fin.mk_le_mk.2 (by omega))
  have hnu := (nu_t_identity D u 0 hm τ r).1
  have key : ((((M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat : ℕ) : ℤ) : ℚ) =
      (D.hcW u τ).u ⟨r.1, hr⟩ + (D.hcW u τ).e ⟨0, hm⟩ + r.1 - D.R.k - (D.R.t : ℚ) / 2 := by
    have z1 : ((((M.lam 0 τ).w r - (M.lam 0 τ).detShift).toNat : ℕ) : ℤ) = (M.lam 0 τ).w r - (M.lam 0 τ).detShift :=
      Int.toNat_of_nonneg (by omega)
    have z2 : (((shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat : ℕ) : ℤ) = shiftOf (lamTG M 0) τ + twB D u μ 0 τ :=
      Int.toNat_of_nonneg hpos
    unfold DomWeight.natW
    rw [Nat.cast_add, z1, z2]
    push_cast
    rw [hsh, hw, htw]
    ring
  have hnu2 : ((nuT D u 0 τ r : ℕ) : ℝ) = (((D.hcW u τ).u ⟨r.1, hr⟩ + (D.hcW u τ).e ⟨0, hm⟩ + r.1 - D.R.k - (D.R.t : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hnu]
    unfold DV.nuRow DV.srcPar DV.wSz
    rw [dif_pos hr, dif_pos ⟨le_rfl, by omega⟩, ← D.hcW_e u τ]
    unfold Ranks.N
    push_cast
    ring
  have key2 : ((((M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat : ℕ) : ℤ) : ℚ) = ((nuT D u 0 τ r : ℕ) : ℚ) := by
    rw [key]
    exact_mod_cast hnu2.symm
  exact_mod_cast key2

theorem wtS : ∀ (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (j : ℕ), j + 1 < D.R.m → ∀ (τ : D.what₂.Tau), 0 ≤ shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ ∧ ∀ r : Fin (D.R.N (j + 1)), (M.lam (j + 1) τ).natW r + (shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ).toNat = extNu (D.R.N (j + 1)) (nuT D u j) τ r := by
  intro D u μ C A P M j hj τ
  have hj' : j < D.R.m := by omega
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hNs : D.R.N (j + 1) = D.R.N j + (D.R.t + 1) := by unfold Ranks.N; ring
  have hNj : D.R.N j = D.R.k + j * (D.R.t + 1) := rfl
  have hN0 : 0 < D.R.N (j + 1) := by omega

  have hgen : ∀ r : Fin (D.R.N (j + 1)), ∀ h : D.R.k ≤ r.1, ((M.lam (j + 1) τ).w r : ℚ) =
      -wG D.R ((D.hcW u τ).e ⟨(r.1 - D.R.k) / (D.R.t + 1), by
        have h2 : r.1 < D.R.k + (j + 1) * (D.R.t + 1) := r.2
        have : (r.1 - D.R.k) / (D.R.t + 1) < j + 1 := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        omega⟩) ((r.1 - D.R.k) / (D.R.t + 1) + 1) := by
    intro r h
    rw [M.lam_eq (j + 1) hj.le τ r, dif_neg (by omega)]
  have hblk : ∀ r : Fin (D.R.N (j + 1)), D.R.N j ≤ r.1 → ((M.lam (j + 1) τ).w r : ℚ) = -wG D.R ((D.hcW u τ).e ⟨j, hj'⟩) (j + 1) := by
    intro r hr
    have h2 : r.1 < D.R.k + (j + 1) * (D.R.t + 1) := r.2
    have hdiv : (r.1 - D.R.k) / (D.R.t + 1) = j := by
      apply Nat.div_eq_of_lt_le
      · rw [hNj] at hr; omega
      · omega
    rw [hgen r (by rw [hNj] at hr; omega)]
    have e1 : (D.hcW u τ).e ⟨(r.1 - D.R.k) / (D.R.t + 1), by omega⟩ = (D.hcW u τ).e ⟨j, hj'⟩ := congrArg _ (Fin.ext hdiv)
    rw [e1, hdiv]
  have hds0 : (M.lam (j + 1) τ).detShift = (M.lam (j + 1) τ).w ⟨D.R.N (j + 1) - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hN0]
  have hds : ((M.lam (j + 1) τ).detShift : ℚ) = -wG D.R ((D.hcW u τ).e ⟨j, hj'⟩) (j + 1) := by
    rw [hds0]
    exact hblk _ (by simp only []; omega)
  have hc : ((((j + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℚ) = ((j : ℚ) + 1) * ((D.R.t : ℚ) + 1) / 2 := by
    obtain ⟨a, ha⟩ := D.R.t_odd
    have e : (j + 1) * (D.R.t + 1) = 2 * ((j + 1) * (a + 1)) := by rw [ha]; ring
    rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [ha]
    push_cast
    ring
  have hsh : shiftOf (lamTG M (j + 1)) τ = (M.lam (j + 1) τ).detShift - ((((j + 1) * (D.R.t + 1) / 2 : ℕ)) : ℤ) := by
    simp [shiftOf, lamTG, Formalism.L2.Forms.shW, DomWeight.detShift, hN0]
  have htw : ((twB D u μ (j + 1) τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨j, hj'⟩ - ((D.R.k : ℚ) + j * (D.R.t + 1)) / 2 := by
    show (((D.chTw u μ).sDiv j τ : ℤ) : ℚ) = _
    rw [(D.chTw u μ).sDiv_eq j hj' τ]
    unfold sExp Ranks.N
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hS : shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ = 0 := by
    have h3 : ((shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ : ℤ) : ℚ) = 0 := by
      rw [Int.cast_add, hsh, Int.cast_sub, hds, hc, htw]
      unfold wG
      push_cast
      ring
    exact_mod_cast h3
  refine ⟨hS.ge, fun r => ?_⟩
  rw [hS, Int.toNat_zero, add_zero]
  have hanti : (M.lam (j + 1) τ).detShift ≤ (M.lam (j + 1) τ).w r := by
    rw [hds0]
    exact (M.lam (j + 1) τ).anti (Fin.mk_le_mk.2 (by omega))
  have z1 : ((((M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift).toNat : ℕ) : ℤ) = (M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift :=
    Int.toNat_of_nonneg (by omega)
  unfold extNu
  by_cases hr : r.1 < D.R.N j
  · rw [dif_pos hr]
    have hnu := (nu_t_identity D u j hj' τ ⟨r.1, hr⟩).1
    have key : (((M.lam (j + 1) τ).natW r : ℕ) : ℝ) = ((nuT D u j τ ⟨r.1, hr⟩ : ℕ) : ℝ) := by
      rw [hnu]
      have q1 : (((M.lam (j + 1) τ).natW r : ℕ) : ℝ) = ((((M.lam (j + 1) τ).w r : ℚ) - ((M.lam (j + 1) τ).detShift : ℚ) : ℚ) : ℝ) := by
        unfold DomWeight.natW
        have : ((((M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift).toNat : ℕ) : ℝ) =
            ((((M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift : ℤ) : ℚ) : ℝ) := by
          rw [← z1]; push_cast; rfl
        rw [this]; push_cast; rfl
      rw [q1, hds]
      unfold DV.nuRow DV.srcPar DV.wSz
      rw [dif_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m from ⟨by omega, by omega⟩), ← D.hcW_e u τ]
      have ej : (D.hcW u τ).e ⟨j + 1 - 1, by omega⟩ = (D.hcW u τ).e ⟨j, hj'⟩ := rfl
      rw [ej]
      by_cases hrk : r.1 < D.R.k
      · rw [dif_pos hrk, M.lam_eq (j + 1) hj.le τ r, dif_pos hrk]
        unfold hcToWeightQ rhoVec wG Ranks.N
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
      · rw [dif_neg hrk]
        have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
          have : (r.1 - D.R.k) / (D.R.t + 1) < j := by
            rw [Nat.div_lt_iff_lt_mul (by omega)]
            rw [hNj] at hr; omega
          omega
        rw [dif_pos hb, hgen r (by omega)]
        have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
        have hr_eq : (r.1 : ℝ) = D.R.k + ((D.R.t : ℝ) + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
          have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
          conv_lhs => rw [this]
          push_cast
          ring
        unfold wG Ranks.N
        simp only [Nat.add_sub_cancel]
        push_cast
        linear_combination (-1 : ℝ) * hr_eq
    exact_mod_cast key
  · rw [dif_neg hr]
    have h0 : ((M.lam (j + 1) τ).w r : ℚ) - ((M.lam (j + 1) τ).detShift : ℚ) = 0 := by
      rw [hblk r (by omega), hds]; ring
    have h1 : (M.lam (j + 1) τ).w r - (M.lam (j + 1) τ).detShift = 0 := by exact_mod_cast h0
    unfold DomWeight.natW
    rw [h1]
    rfl

theorem eval_mul_det {D : D7} {N : ℕ} (Q0 : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (k : D.what₂.Tau → ℕ)
    (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (Q0 * ∏ τ, frDet D.what₂.LL N τ ^ k τ)) y =
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL Q0) y * ∏ τ, (y τ).det ^ k τ := by
  unfold GL3Theta.evFr
  rw [map_mul, map_mul, map_prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, map_pow, eval_detP]

theorem core (D : D7) (O : ∀ u a, GL3Theta.LiftObj D (D.chTw u a)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pp : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pp)
    (eY : (D.chTw u μ).Y i ≃ Formalism.L2.Forms.Fr D i hi.le)
    (hE : ∀ y, Subtype.val (eY y) = (O u μ).frm i y)
    (f : (D.chTw u μ).Y i → ℂ)
    (hP : ∃ P ∈ Formalism.L2.Forms.RatSpan D (M.lam i), ∀ z, f z = fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 P (eY z)) :
    ∃ v : ValQ O u μ i, evC O u μ i v = f := by
  obtain ⟨P, hP, hf⟩ := hP
  obtain ⟨Q0, hQ0, hmap⟩ := lift_ratSpan D (M.lam i) P hP
  have hwt : ∀ τ, 0 ≤ shiftOf (lamTG M i) τ + twB D u μ i τ := by
    intro τ
    cases i with
    | zero => exact (wt0 D u μ M τ).1
    | succ j => exact (wtS D u μ M j hi τ).1
  have hQ : Q0 * ∏ τ, frDet D.what₂.LL (D.R.N i) τ ^ (shiftOf (lamTG M i) τ + twB D u μ i τ).toNat ∈ polV D u i := by
    have h := wtPol_mul_det _ (fun τ => (shiftOf (lamTG M i) τ + twB D u μ i τ).toNat) hQ0
    cases i with
    | zero =>
      have e : (fun τ r => (M.lam 0 τ).natW r + (shiftOf (lamTG M 0) τ + twB D u μ 0 τ).toNat) = nuT D u 0 :=
        funext fun τ => funext fun r => (wt0 D u μ M τ).2 r
      rw [e] at h
      exact h
    | succ j =>
      have e : (fun τ r => (M.lam (j + 1) τ).natW r + (shiftOf (lamTG M (j + 1)) τ + twB D u μ (j + 1) τ).toNat) =
          extNu (D.R.N (j + 1)) (nuT D u j) := funext fun τ => funext fun r => (wtS D u μ M j hi τ).2 r
      rw [e] at h
      exact h
  refine ⟨Submodule.mkQ _ ⟨_, hQ⟩, ?_⟩
  funext z
  show evP O u μ i ⟨_, hQ⟩ z = f z
  rw [hf z]
  show (∏ τ, (D.chTw u μ).de i z τ ^ (-twB D u μ i τ)) *
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL _) ((O u μ).frm i z) = _
  rw [eval_mul_det, hmap]
  have hde : ∀ τ, (D.chTw u μ).de i z τ = ((O u μ).frm i z τ).det := fun τ => (O u μ).frm_de i hi.le z τ
  have hne : ∀ τ, ((O u μ).frm i z τ).det ≠ 0 := fun τ => hde τ ▸ (D.chTw u μ).de_ne i z τ
  simp only [hde]
  unfold fnOf
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, hE z]
  unfold GL3Theta.evFr
  rw [mul_comm (MvPolynomial.eval _ P), ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_natCast, Int.toNat_of_nonneg (hwt τ), ← zpow_add₀ (hne τ)]
  congr 1
  ring

theorem exists_valQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∃ v : ValQ O u μ i, evC O u μ i v = f := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f hP
  exact core (I.rec7 l Z) O u μ i hi (I.fm l u μ) eY (fun y => (hIdY y).trans (hStd.frm u μ i y).symm) f hP

end GlobalTheory.CmpEx
