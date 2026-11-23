import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesMeas
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesPt

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus

variable {k r : ℕ}

theorem blockW_dT (h : Matrix (Fin k) (Fin k) ℂ) (i j : Fin (2 * r + k + 1)) (hne : blockW k r h i j ≠ 0) :
    dT k r i = dT k r j := by
  unfold blockW at hne
  split_ifs at hne with hi hj hij
  · rw [dT_mid i hi.1 hi.2.le, dT_mid j hj.1 hj.2.le]
  · exact absurd rfl hne
  · rw [hij]
  · exact absurd rfl hne

theorem frame_conj_fix {z : Fin (2 * r + k + 1) → ℂ} {g : Mx k r} (hg : IsFrameW k r z g) (h : Matrix (Fin k) (Fin k) ℂ) :
    tT k r * (g * blockW k r h * g⁻¹) * tTi k r = g * blockW k r h * g⁻¹ := by
  unfold IsFrameW at hg
  obtain ⟨hU, hfix, -⟩ := hg
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have hb1 : ∀ e : Fin (2 * r + k + 1), bvec e e = 1 := fun e => by simp [bvec]
  have hb0 : ∀ e p : Fin (2 * r + k + 1), p ≠ e → bvec e p = 0 := fun e p hp => by
    simp [bvec, Pi.single_apply, hp]
  have hfixv : ∀ e : Fin (2 * r + k + 1), (e.val < r ∨ r + k < e.val) → g *ᵥ bvec e = bvec e := by
    intro e he
    have heL := e.isLt
    rcases he with he | he
    · have hee : e = eI k r ⟨e.val, he⟩ := Fin.ext rfl
      rw [hee]; exact (hfix _).1
    · have ha : 2 * r + k - e.val < r := by omega
      have hee : e = esI k r ⟨2 * r + k - e.val, ha⟩ :=
        Fin.ext (by show e.val = 2 * r + k - (2 * r + k - e.val); omega)
      rw [hee]; exact (hfix _).2
  have hcol : ∀ e : Fin (2 * r + k + 1), (e.val < r ∨ r + k < e.val) → ∀ i, g i e = bvec e i := by
    intro e he i
    have hi := congrFun (hfixv e he) i
    rw [← hi]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single e (fun b _ hb => by rw [hb0 e b hb, mul_zero])
      (fun h => absurd (Finset.mem_univ e) h), hb1, mul_one]
  have hHrow : ∀ q b : Fin (2 * r + k + 1), (q.val < r ∨ r + k < q.val) →
      Hpk k r q b = if q.val + b.val = 2 * r + k then 1 else 0 := by
    intro q b hq
    have := q.isLt
    have := b.isLt
    unfold Hpk
    split_ifs <;> first | rfl | (exfalso; omega)
  have hrow : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → ∀ j, g i j = bvec i j := by
    intro i hi j
    have hiL := i.isLt
    obtain ⟨q, hqv⟩ : ∃ q : Fin (2 * r + k + 1), q.val = 2 * r + k - i.val := ⟨⟨2 * r + k - i.val, by omega⟩, rfl⟩
    have hqo : q.val < r ∨ r + k < q.val := by omega
    have hE := congrFun (congrFun hU' q) j
    have hgHq : ∀ b, (gᴴ * Hpk k r) q b = Hpk k r q b := by
      intro b
      rw [Matrix.mul_apply, Finset.sum_eq_single q]
      · rw [Matrix.conjTranspose_apply, hcol q hqo q, hb1, star_one, one_mul]
      · intro a _ ha
        rw [Matrix.conjTranspose_apply, hcol q hqo a, hb0 q a ha, star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ q) h
    rw [Matrix.mul_apply] at hE
    simp only [hgHq] at hE
    rw [Finset.sum_eq_single i] at hE
    · rw [hHrow q i hqo, if_pos (by omega), one_mul] at hE
      rw [hE, hHrow q j hqo]
      by_cases hji : j = i
      · rw [hji, hb1, if_pos (by omega)]
      · rw [hb0 i j hji, if_neg (by intro h; apply hji; ext; omega)]
    · intro b _ hb
      rw [hHrow q b hqo, if_neg (by intro h; apply hb; ext; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hg_comm : tT k r * g = g * tT k r := by
    ext i j
    simp only [tT, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hrow i hi j]
      by_cases hij : j = i
      · rw [hij]; ring
      · rw [hb0 i j hij, mul_zero, zero_mul]
    · by_cases hj : j.val < r ∨ r + k < j.val
      · rw [hcol j hj i]
        have hij : i ≠ j := fun h => hi (by rw [h]; exact hj)
        rw [hb0 j i hij, mul_zero, zero_mul]
      · push_neg at hi hj
        rw [dT_mid i hi.1 hi.2, dT_mid j hj.1 hj.2, mul_comm]
  have hB_comm : tT k r * blockW k r h = blockW k r h * tT k r := by
    have h1 : tT k r * blockW k r h * tTi k r = blockW k r h := conj_eq_self (fun i j hne => blockW_dT h i j hne)
    calc tT k r * blockW k r h = tT k r * blockW k r h * tTi k r * tT k r := by
          rw [Matrix.mul_assoc _ (tTi k r), tTi_mul_tT, Matrix.mul_one]
      _ = blockW k r h * tT k r := by rw [h1]
  have hginv_comm : tT k r * g⁻¹ = g⁻¹ * tT k r := by
    by_cases hdet : IsUnit g.det
    · calc tT k r * g⁻¹ = g⁻¹ * g * tT k r * g⁻¹ := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
        _ = g⁻¹ * (tT k r * g) * g⁻¹ := by rw [hg_comm]; simp only [Matrix.mul_assoc]
        _ = g⁻¹ * tT k r := by simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit g hdet, Matrix.mul_zero, Matrix.zero_mul]
  have hL : tT k r * (g * blockW k r h * g⁻¹) = g * blockW k r h * g⁻¹ * tT k r := by
    calc tT k r * (g * blockW k r h * g⁻¹) = (tT k r * g) * blockW k r h * g⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = g * (tT k r * blockW k r h) * g⁻¹ := by rw [hg_comm]; simp only [Matrix.mul_assoc]
      _ = g * blockW k r h * (tT k r * g⁻¹) := by rw [hB_comm]; simp only [Matrix.mul_assoc]
      _ = g * blockW k r h * g⁻¹ * tT k r := by rw [hginv_comm]; simp only [Matrix.mul_assoc]
  rw [hL]
  simp only [Matrix.mul_assoc, tT_mul_tTi, Matrix.mul_one]

theorem turn_hσ (L : LocBessel k r) : IsDSHpk k r L.ε L.lam (fun x => L.σ (tT k r * x * tTi k r)) := by
  have h0 := L.hσ
  unfold IsDSHpk at h0 ⊢
  obtain ⟨P, hP, hD⟩ := h0
  unfold IsCayleyU at hP
  obtain ⟨hC, hU⟩ := hP
  unfold IsCayley at hC
  have hfun : (fun g => (fun x => L.σ (tT k r * x * tTi k r)) ((P * tT k r)⁻¹ * g * (P * tT k r))) =
      fun g => L.σ (P⁻¹ * g * P) := by
    funext g
    simp only [Matrix.mul_inv_rev, tT_inv]
    congr 1
    simp only [← Matrix.mul_assoc, tT_mul_tTi, Matrix.one_mul]
    simp only [Matrix.mul_assoc, tT_mul_tTi, Matrix.mul_one]
  refine ⟨P * tT k r, ?_, by rw [hfun]; exact hD⟩
  unfold IsCayleyU IsCayley
  refine ⟨⟨hC.1.mul ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (tT_mul_tTi k r))), ?_⟩,
    Submonoid.mul_mem _ hU (tT_unitary k r)⟩
  rw [Matrix.conjTranspose_mul, conjT_tT]
  calc tTi k r * Pᴴ * Formalism.REAL.Jm L.ε * (P * tT k r) = tTi k r * (Pᴴ * Formalism.REAL.Jm L.ε * P) * tT k r := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hC.2]; exact conjI_eq_self (fun i j h => Hpk_ne_dT i j h)

theorem turn_hπ (L : LocBessel k r) : IsHCTypeW k r L.z L.u (fun x => L.π (tT k r * x * tTi k r)) := by
  have h0 := L.hπ
  unfold IsHCTypeW at h0 ⊢
  obtain ⟨g, hg, hH⟩ := h0
  exact ⟨g, hg, by simpa only [frame_conj_fix hg] using hH⟩

theorem turn_hπ' (L : LocBessel k r) : IsHCTypeW k r L.z' L.u' (fun x => L.π' (tT k r * x * tTi k r)) := by
  have h0 := L.hπ'
  unfold IsHCTypeW at h0 ⊢
  obtain ⟨g, hg, hH⟩ := h0
  exact ⟨g, hg, by simpa only [frame_conj_fix hg] using hH⟩

abbrev turnL (L : LocBessel k r) (ka : ℝ) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := L.z
  z' := L.z'
  hz := L.hz
  hz' := L.hz'
  u := L.u
  u' := L.u'
  Hs := L.Hs
  σ := fun x => L.σ (tT k r * x * tTi k r)
  hσ := turn_hσ L
  Wp := L.Wp
  π := fun x => L.π (tT k r * x * tTi k r)
  hπ := turn_hπ L
  Wq := L.Wq
  π' := fun x => L.π' (tT k r * x * tTi k r)
  hπ' := turn_hπ' L
  c := cOfDpsi (ka : ℂ)
  μW := L.μW
  μW' := L.μW'
  hμW := L.hμW
  hμW' := L.hμW'
  κN := L.κN

abbrev turnF (L : LocBessel k r) (ka : ℝ) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) :
    Mx k r → ((turnL L ka).Wq →L[ℂ] (turnL L ka).Wp) :=
  fun x => f (tT k r * x * tTi k r)

theorem turn_c (ka : ℝ) : cOfDpsi (ka : ℂ) * Complex.I = ((2 * ka : ℝ) : ℂ) := by
  unfold cOfDpsi
  push_cast
  linear_combination (-2 * (ka : ℂ)) * Complex.I_sq

theorem turn_kfin (L : LocBessel k r) (ka : ℝ) {f : Mx k r → (L.Wq →L[ℂ] L.Wp)} (hf : IsKFinCoefH L.σ f) :
    IsKFinCoefH (turnL L ka).σ (turnF L ka f) := by
  unfold IsKFinCoefH at hf ⊢
  obtain ⟨P, Q, hQ, hP, hf⟩ := hf
  have key : ∀ v : L.Hs, IsKFinHpk L.σ v → IsKFinHpk (fun x => L.σ (tT k r * x * tTi k r)) v := by
    intro v hv
    unfold IsKFinHpk at hv ⊢
    obtain ⟨S, hS, hvS, hinv⟩ := hv
    refine ⟨S, hS, hvS, fun g hg x hx => hinv _ ⟨?_, ?_⟩ x hx⟩
    · exact UH_mul (UH_mul (tT_mem_UH k r) hg.1) (tTi_mem_UH k r)
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (tT_unitary k r) hg.2) (tTi_unitary k r)
  exact ⟨P, Q, fun w => key _ (hQ w), fun x => key _ (hP x), fun g => hf _⟩

theorem tT_mul_tTi_assoc (M : Mx k r) : tT k r * (tTi k r * M) = M := by
  rw [← Matrix.mul_assoc, tT_mul_tTi, Matrix.one_mul]

theorem tTi_mul_tT_assoc (M : Mx k r) : tTi k r * (tT k r * M) = M := by
  rw [← Matrix.mul_assoc, tTi_mul_tT, Matrix.one_mul]

theorem besselIntg_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (g : Mx k r) (p : PairSp k r) :
    besselIntg (turnL L ka) (turnF L ka f) g (thP k r p) = besselIntg L f (tT k r * g * tTi k r) p := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := p
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  simp only [besselIntg, thP, Prod.map_apply, of_cA, turnL, turnF]
  rw [psi_conjI L.hz.1 hc', psi_conjI L.hz'.1 hc']
  simp only [← conjI_inv]
  simp only [Matrix.mul_assoc, tT_mul_tTi_assoc, tT_mul_tTi, Matrix.mul_one]

theorem J_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (g : Mx k r) : (turnL L ka).J (turnF L ka f) g = L.J f (tT k r * g * tTi k r) := by
  rw [J_eq_integral, J_eq_integral]
  have hP : pairMeas (turnL L ka) = pairMeas L := rfl
  rw [hP]
  conv_lhs => rw [← map_thP_pairMeas L, ← thE_coe, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  rw [thE_coe]
  exact besselIntg_turn L ka hc f g p

theorem jNorm2_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : jNorm2 (turnL L ka) (turnF L ka f) μsec = jNorm2 L f μsec := by
  unfold jNorm2
  congr 1
  funext p
  rw [J_turn L ka hc, conj_eq_self (bigCell_dT _ _)]

theorem OrbInt_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (g : Mx k r) (ν : Measure (PairSp k r)) :
    OrbInt (turnL L ka) (turnF L ka f) (tTi k r * g * tT k r) (ν.map (thP k r)) = OrbInt L f g ν := by
  unfold OrbInt
  rw [← thE_coe, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show besselIntg (turnL L ka) (turnF L ka f) (tTi k r * g * tT k r) (thE k r p) = besselIntg L f g p
  rw [thE_coe, besselIntg_turn L ka hc f, conj_conjI]

theorem thP_stabAct (g a : Mx k r) (x : PairSp k r) :
    thP k r (stabAct g a x) = stabAct (tTi k r * g * tT k r) (tTi k r * a * tT k r) (thP k r x) := by
  have h1 : tT k r * tTi k r = 1 := tT_mul_tTi k r
  have h2 : tTi k r * tT k r = 1 := tTi_mul_tT k r
  have hinvT : (tT k r)⁻¹ = tTi k r := Matrix.inv_eq_right_inv h1
  have hinvTi : (tTi k r)⁻¹ = tT k r := Matrix.inv_eq_right_inv h2
  have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Matrix.of (fun i j => M i j) = M :=
    fun M => rfl
  obtain ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩ := x
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · funext i j
    show (tTi k r * Matrix.of (fun i j => (a * Matrix.of x2) i j) * tT k r) i j =
      ((tTi k r * a * tT k r) * Matrix.of (fun i j => (tTi k r * Matrix.of x2 * tT k r) i j)) i j
    rw [e, e]
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (tT k r) (tTi k r), h1, Matrix.one_mul]
  · funext i j
    show (tTi k r * Matrix.of (fun i j => (g⁻¹ * a * g * Matrix.of x4) i j) * tT k r) i j =
      ((tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r) *
        Matrix.of (fun i j => (tTi k r * Matrix.of x4 * tT k r) i j)) i j
    rw [e, e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinvT, hinvTi]
    simp only [Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (tT k r) (tTi k r), h1, Matrix.one_mul]

theorem isOrbQuot_turn (L : LocBessel k r) (ka : ℝ) {g : Mx k r} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)}
    (h : IsOrbQuot L g μR ν) : IsOrbQuot (turnL L ka) (tTi k r * g * tT k r) (μR.map (cA k r)) (ν.map (thP k r)) := by
  intro F hF
  have hP : pairMeas (turnL L ka) = pairMeas L := rfl
  calc ∫⁻ x, F x ∂pairMeas (turnL L ka) = ∫⁻ x, F x ∂((pairMeas L).map (thE k r)) := by
        rw [hP, thE_coe, map_thP_pairMeas]
    _ = ∫⁻ x, F (thE k r x) ∂pairMeas L := lintegral_map_equiv _ _
    _ = ∫⁻ x, (∫⁻ a, F (thE k r (stabAct g (Matrix.of a) x)) ∂μR) ∂ν :=
        h (fun x => F (thE k r x)) (hF.comp (thE k r).measurable)
    _ = ∫⁻ x, (∫⁻ a, F (stabAct (tTi k r * g * tT k r) (Matrix.of (cAE k r a)) (thE k r x)) ∂μR) ∂ν := by
        refine lintegral_congr fun x => lintegral_congr fun a => ?_
        rw [thE_coe, thP_stabAct, cAE_coe, of_cA]
    _ = ∫⁻ x, (∫⁻ a, F (stabAct (tTi k r * g * tT k r) (Matrix.of a) (thE k r x)) ∂(μR.map (cAE k r))) ∂ν := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_map_equiv]
    _ = ∫⁻ x, (∫⁻ a, F (stabAct (tTi k r * g * tT k r) (Matrix.of a) x) ∂(μR.map (cAE k r))) ∂(ν.map (thE k r)) :=
        (lintegral_map_equiv (fun x => ∫⁻ a, F (stabAct (tTi k r * g * tT k r) (Matrix.of a) x) ∂(μR.map (cAE k r)))
          (thE k r)).symm
    _ = _ := by rw [cAE_coe, thE_coe]

theorem isRelStab_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) {g : Mx k r} (h : IsRelStab L g) :
    IsRelStab (turnL L ka) (tTi k r * g * tT k r) := by
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  intro a' ha'
  have ha : tT k r * a' * tTi k r ∈ RStab k r g := by
    rw [← conjI_mem_RStab_iff g, conjI_conj]; exact ha'
  have e1 : a' = tTi k r * (tT k r * a' * tTi k r) * tT k r := (conjI_conj a').symm
  have e2 : (tTi k r * g * tT k r)⁻¹ * a' * (tTi k r * g * tT k r) =
      tTi k r * (g⁻¹ * (tT k r * a' * tTi k r) * g) * tT k r := by
    rw [← conjI_inv]
    simp only [Matrix.mul_assoc, tTi_mul_tT_assoc, tT_mul_tTi_assoc, tT_mul_tTi, tTi_mul_tT, Matrix.mul_one]
  show psi k r L.z (cOfDpsi (ka : ℂ)) a' = psi k r L.z' (cOfDpsi (ka : ℂ)) ((tTi k r * g * tT k r)⁻¹ * a' * (tTi k r * g * tT k r))
  rw [e2]
  conv_lhs => rw [e1]
  rw [psi_conjI L.hz.1 hc', psi_conjI L.hz'.1 hc']
  exact h _ ha

theorem rot_mp {S : Type*} [Fintype S] (u : S → ℂ) (hu : ∀ s, Complex.normSq (u s) = 1) :
    MeasurePreserving (fun (v : S → ℂ) s => u s * v s) volume volume := by
  refine measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun s => ?_)
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ (u s)) = 1 := by
    have h1 : LinearMap.det (LinearMap.mulLeft ℝ (u s)) = Algebra.norm ℝ (u s) := by
      rw [Algebra.norm_apply]
      rfl
    rw [h1, Algebra.norm_complex_apply, hu s]
  refine ⟨(LinearMap.mulLeft ℝ (u s)).continuous_of_finiteDimensional.measurable, ?_⟩
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ (u s)) (by rw [hdet]; norm_num)
  rw [hdet] at h
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

theorem flagMat_conjI {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r) (i j : Fin (r + 1)) :
    flagMat k r z (tTi k r * x * tT k r) i j =
      (if i.val < r then star (Complex.I ^ i.val) * Complex.I ^ j.val else 1) * flagMat k r z x i j := by
  unfold flagMat fvec
  by_cases hi : i.val < r
  · rw [dif_pos hi, dif_pos hi, if_pos hi]
    have hv : tT k r *ᵥ (if h : j.val < r then bvec (eI k r ⟨j.val, h⟩) else z) =
        Complex.I ^ j.val • (if h : j.val < r then bvec (eI k r ⟨j.val, h⟩) else z) := by
      by_cases hj : j.val < r
      · rw [dif_pos hj]
        funext p
        simp only [tT, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        by_cases hp : p = eI k r ⟨j.val, hj⟩
        · rw [hp, dT_eI]
        · have hb : bvec (eI k r ⟨j.val, hj⟩) p = 0 := by simp [bvec, Pi.single_apply, hp]
          rw [hb, mul_zero, mul_zero]
      · rw [dif_neg hj, tT_mulVec_Wb hz, show j.val = r by have := j.isLt; omega]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
    simp only [tTi, Matrix.mulVec_diagonal, dT_eI, Fin.val_mk, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [dif_neg hi, dif_neg hi, if_neg hi, one_mul]

theorem continuous_rootCoordsS {z : Fin (2 * r + k + 1) → ℂ} (S : Finset (Fin (r + 1) × Fin (r + 1))) :
    Continuous (fun (x : Mt k r) (q : S) => flagMat k r z (Matrix.of x) q.1.1 q.1.2) := by
  refine continuous_pi fun q => ?_
  unfold flagMat
  split_ifs with hi h2
  · have hc : Continuous fun a : Mt k r => Matrix.of a *ᵥ fvec k r z q.1.2 :=
      Continuous.matrix_mulVec continuous_id continuous_const
    exact (continuous_apply (eI k r ⟨q.1.1.val, hi⟩)).comp hc
  · exact continuous_const
  · exact continuous_const

theorem turn_normc (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ)) :
    ‖(turnL L ka).c‖ = ‖L.c‖ := by
  show ‖cOfDpsi (ka : ℂ)‖ = ‖L.c‖
  rw [hc, ← turn_c, norm_mul, Complex.norm_I, mul_one]

theorem isRootMeas_turn (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ))
    {p : Point ℂ (r + 1)} {g : Mx k r} {μR : Measure (Mt k r)} (h : IsRootMeas L p g μR) :
    IsRootMeas (turnL L ka) (turnPt p) (tTi k r * g * tT k r) (μR.map (cA k r)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← cAE_coe, MeasurableEquiv.map_apply]
    convert h1 using 2
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, cAE_coe, of_cA, conjI_mem_RStab_iff]
  · rw [turn_normc L ka hka hc]
    show Measure.map (fun (x : Mt k r) (q : rootPat (turnPt p)) => flagMat k r L.z (Matrix.of x) q.1.1 q.1.2)
      (μR.map (cA k r)) = _
    rw [rootPat_turnPt]
    have h2' : Measure.map (fun (x : Mt k r) (q : rootPat p) => flagMat k r L.z (Matrix.of x) q.1.1 q.1.2) μR =
        ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume := h2
    set u : rootPat p → ℂ := fun q => if q.1.1.val < r then star (Complex.I ^ q.1.1.val) * Complex.I ^ q.1.2.val else 1
    have hu : ∀ q, Complex.normSq (u q) = 1 := by
      intro q
      simp only [u]
      split_ifs
      · rw [map_mul, Complex.star_def, Complex.normSq_conj]; simp [map_pow]
      · simp
    have e : (fun (x : Mt k r) (q : rootPat p) => flagMat k r L.z (Matrix.of x) q.1.1 q.1.2) ∘ cA k r =
        (fun (v : rootPat p → ℂ) q => u q * v q) ∘ (fun (x : Mt k r) (q : rootPat p) => flagMat k r L.z (Matrix.of x) q.1.1 q.1.2) := by
      funext x q
      simp only [Function.comp_apply, of_cA]
      exact flagMat_conjI L.hz.1 _ _ _
    rw [Measure.map_map (continuous_rootCoordsS _).measurable continuous_cA.measurable, e,
      ← Measure.map_map (rot_mp u hu).measurable (continuous_rootCoordsS _).measurable, h2', Measure.map_smul,
      (rot_mp u hu).map_eq]

theorem isPtRep_turn (L : LocBessel k r) (ka : ℝ) {p : Point ℂ (r + 1)} {g : Mx k r} (h : IsPtRepO L p g) :
    IsPtRep (turnL L ka) (turnPt p) (tTi k r * g * tT k r) :=
  ⟨conjI_mem_UH h.1, Zhat_conjI_turn L.hz.1 L.hz'.1 h.2⟩

end Formalism.MainNotions.S.Pv.Frames

end
