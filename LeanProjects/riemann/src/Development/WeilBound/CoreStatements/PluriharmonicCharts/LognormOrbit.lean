import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
import Development.WeilBound.CoreStatements.PluriharmonicCharts.BlockFnFieldCompLe
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsOpenHoloPreimage
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap GlobalTheory.CompanionTheory.Ar.PB.CovGraph GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

section Fac

variable {N j : ℕ}

def mfac (j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
  else minorIJ h (omIdx N j) (omIdx N j)

theorem mfac_mul (a i : Fin N) (T : Matrix (Fin N) (Fin N) ℂ) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) :
    mfac j a i (T * h) = mfac j a i T * mfac j a i h := by
  unfold mfac
  rw [MinorCalc.minorIJ_mul_of_support T h _ _ (MinorCalc.support_wIdx hh),
    MinorCalc.minorIJ_mul_of_support T h _ _ (MinorCalc.support_omIdx hh)]
  split_ifs <;> simp

theorem mfac_ne (a i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) :
    mfac j a i h ≠ 0 := by
  have h1 := mfac_mul a i h⁻¹ hh
  rw [Matrix.nonsing_inv_mul _ hd.isUnit] at h1
  have h2 : mfac j a i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold mfac
    split_ifs <;> simp [CPts.minorIJ_one]
  rw [h2] at h1
  exact right_ne_zero_of_mul_eq_one h1.symm

theorem minor_w_ne {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) :
    minorIJ h (wIdx N j) (wIdx N j) ≠ 0 ∧ minorIJ h (omIdx N j) (omIdx N j) ≠ 0 := by
  have h1 := MinorCalc.minorIJ_mul_of_support h⁻¹ h (wIdx N j) _ (MinorCalc.support_wIdx hh)
  have h2 := MinorCalc.minorIJ_mul_of_support h⁻¹ h (omIdx N j) _ (MinorCalc.support_omIdx hh)
  rw [Matrix.nonsing_inv_mul _ hd.isUnit, CPts.minorIJ_one] at h1 h2
  exact ⟨right_ne_zero_of_mul_eq_one h1.symm, right_ne_zero_of_mul_eq_one h2.symm⟩

theorem sum_detFac (hj : j ≤ N) {a b : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    {T : Matrix (Fin N) (Fin N) ℂ} (hT : IsBlockDiag j T) (hd : T.det ≠ 0) :
    ∑ i, (xiCoef () a ((), i) : ℝ) * (Real.log ‖detFac j i T‖ -
      if IsProperStep N j i then 0 else Real.log ‖mfac j a i T‖) = 0 := by
  obtain ⟨hw, ho⟩ := minor_w_ne hT hd
  have ha := a.2
  have hb' := b.2
  have key : ∀ i : Fin N, (a : ℕ) ≤ i + 1 → (i : ℕ) ≤ a + 1 → (Real.log ‖detFac j i T‖ -
      if IsProperStep N j i then 0 else Real.log ‖mfac j a i T‖) =
      if j ≤ (a : ℕ) then Real.log ‖minorIJ T (wIdx N j) (wIdx N j)‖ else 0 := by
    intro i h1 h2
    have hi := i.2
    have ho1 : j = N → minorIJ T (omIdx N j) (omIdx N j) = 1 := fun e => by
      rw [show omIdx N j = ∅ by ext c; simp [omIdx, e]]
      exact SchurCalc.minor_empty T
    unfold detFac mfac IsProperStep
    by_cases c1 : (i : ℕ) + 1 = j <;> by_cases c2 : (i : ℕ) + 1 = N <;> by_cases c3 : j ≤ (a : ℕ)
    · omega
    · rw [ho1 (by omega)]
      simp [c1, c3, not_le.1 c3]
    · simp [c1, c3, not_lt.2 c3, show ¬ j = N by omega]
    · simp [c1, c3, not_le.1 c3, show ¬ j = N by omega]
    · simp [c1, c2, c3, hj, show ¬ N = j by omega, Real.log_mul (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 ho)]
    · omega
    · simp [c1, c2, c3, show j ≤ (i : ℕ) + 1 by omega]
    · simp [c1, c2, c3, show ¬ j ≤ (i : ℕ) + 1 by omega]
  rw [SchurCalc.sum_xi _ a b hb (if j ≤ (a : ℕ) then Real.log ‖minorIJ T (wIdx N j) (wIdx N j)‖ else 0)
    (fun i hi => key i (by omega) (by omega)) ?_, key b (by omega) (by omega), key a (by omega) (by omega)]
  · ring
  · intro h0
    split_ifs with c
    · rw [show wIdx N j = ∅ by ext c; simp [wIdx, show j = 0 by omega], SchurCalc.minor_empty]
      simp
    · rfl

theorem sum_xi_prod {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (τ : Ψ) (a : Fin N) (T : Ψ × Fin N → ℝ) :
    ∑ p, (xiCoef τ a p : ℝ) * T p = ∑ i, (xiCoef τ a (τ, i) : ℝ) * T (τ, i) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · intro τ' _ h
    simp [xiCoef, h]
  · simp

theorem log_fac {Ψ : Type} [DecidableEq Ψ] (τ : Ψ) (a : Fin N) {t : ℂ} (ht : t ≠ 0) {A : Fin N → ℂ} (hA : ∀ i, A i ≠ 0) :
    Real.log ‖t * ∏ i, A i ^ xiCoef τ a (τ, i)‖ = Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) * Real.log ‖A i‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 ht)
    (norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hA i))), norm_prod,
    Real.log_prod fun i _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hA i))]
  simp only [norm_zpow, Real.log_zpow]

end Fac

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem log_eval_smul {g : MRing ι} {dg : K → ℕ} (hg : IsMultiHomog g dg) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (h0 : eval z (map (Int.castRingHom ℂ) g) ≠ 0) :
    eval (fun q => c q.1 * z q) (map (Int.castRingHom ℂ) g) ≠ 0 ∧
    Real.log ‖eval (fun q => c q.1 * z q) (map (Int.castRingHom ℂ) g)‖ =
      Real.log ‖eval z (map (Int.castRingHom ℂ) g)‖ + ∑ k, (dg k : ℝ) * Real.log ‖c k‖ := by
  have hu : (∏ k, c k ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  rw [eval_smul_homog g dg hg]
  refine ⟨mul_ne_zero hu h0, ?_⟩
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hu) (norm_ne_zero_iff.2 h0), norm_prod,
    Real.log_prod fun k _ => norm_ne_zero_iff.2 (pow_ne_zero _ (hc k)), add_comm]
  simp only [norm_pow, Real.log_pow]

def lognorm (τ : Ψ) (a : Fin N) (k₀ : K) (g h : MRing fun o : Option K => ι (o.getD k₀))
    (A : Ψ × Fin N → HermLine ι) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : ℝ :=
  Real.log ‖eval z (map (Int.castRingHom ℂ) g)‖ - Real.log ‖eval z (map (Int.castRingHom ℂ) h)‖ +
    (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((A p).h (fstPt k₀ z)) + Real.log ((A p).h (sndPt k₀ z)))

theorem lognorm_orbit {τ : Ψ} {a : Fin N} {k₀ : K} {g h : MRing fun o : Option K => ι (o.getD k₀)}
    {dg dh : Option K → ℕ} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) {A : Ψ × Fin N → HermLine ι}
    (hxi : ∑ p, xiCoef τ a p * (A p).a k₀ = -2)
    (hdeg : ∀ o : Option K, (dg o : ℤ) - dh o =
      o.elim 1 fun k => -(∑ p, xiCoef τ a p * (A p).a k) - if k₀ = k then 1 else 0)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (ho : SameOrbit z' z)
    (h₀ : ∀ k, ∃ i, fstPt k₀ z ⟨k, i⟩ ≠ 0) (h₁ : ∀ k, ∃ i, sndPt k₀ z ⟨k, i⟩ ≠ 0)
    (g0 : eval z (map (Int.castRingHom ℂ) g) ≠ 0) (h0 : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    eval z' (map (Int.castRingHom ℂ) g) ≠ 0 ∧ eval z' (map (Int.castRingHom ℂ) h) ≠ 0 ∧
      lognorm τ a k₀ g h A z' = lognorm τ a k₀ g h A z := by
  obtain ⟨c, hc, rfl⟩ := ho
  obtain ⟨g1, g2⟩ := log_eval_smul hg c hc g0
  obtain ⟨h1, h2⟩ := log_eval_smul hh c hc h0
  refine ⟨g1, h1, ?_⟩
  have e₀ : fstPt k₀ (fun q => c q.1 * z q) = fun q => (fun k => c (some k)) q.1 * fstPt k₀ z q := rfl
  have e₁ : sndPt k₀ (fun q => c q.1 * z q) = fun q => (fun k => c (κ₁ k₀ k)) q.1 * sndPt k₀ z q := by
    funext q
    show c (v₁ k₀ q).1 * _ = _
    rw [(isBlockMap_v₁ k₀).2.2.1]
    rfl
  unfold lognorm
  rw [g2, h2, e₀, e₁]
  simp only [fun p => log_smul (A p) (fun k => c (some k)) (fun k => hc _) h₀,
    fun p => log_smul (A p) (fun k => c (κ₁ k₀ k)) (fun k => hc _) h₁]
  have hd : ∀ o, (dg o : ℝ) - dh o = (((o.elim 1 fun k => -(∑ p, xiCoef τ a p * (A p).a k) -
      if k₀ = k then 1 else 0 : ℤ)) : ℝ) := fun o => by rw [← hdeg]; push_cast; rfl
  have key : ∑ o, (dg o : ℝ) * Real.log ‖c o‖ - ∑ o, (dh o : ℝ) * Real.log ‖c o‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) *
      (∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖) = 0 := by
    have e2 : ∑ p, (xiCoef τ a p : ℝ) *
        (∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖) =
        ∑ k, ((∑ p, xiCoef τ a p * (A p).a k : ℤ) : ℝ) * (Real.log ‖c (some k)‖ + Real.log ‖c (κ₁ k₀ k)‖) := by
      simp only [← Finset.sum_add_distrib, Finset.mul_sum, Int.cast_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => by push_cast; ring
    rw [e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [← sub_mul, hd]
    rw [Fintype.sum_option, add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_single k₀]
    · simp only [Option.elim, hxi, κ₁_self, if_true]
      push_cast
      ring
    · intro k _ hk
      simp only [Option.elim, κ₁_ne hk, if_neg (Ne.symm hk)]
      push_cast
      ring
    · simp
  have e3 : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((A p).h (fstPt k₀ z)) + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ +
      (Real.log ((A p).h (sndPt k₀ z)) + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖)) =
      ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((A p).h (fstPt k₀ z)) + Real.log ((A p).h (sndPt k₀ z))) +
      ∑ p, (xiCoef τ a p : ℝ) *
        (∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e3]
  linarith

theorem flag_of_exact (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {z : (Σ k, ι k) → ℂ}
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (p₀ : Ψ × Fin N) (hh : ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0)
    (H : ∀ p, M.ExactAt F p z (h p.1)) : M.IsFlagOf F z h :=
  ⟨(H p₀).1, hh, fun p k hk => ⟨1, one_ne_zero, fun m => by rw [one_mul]; exact (H p).2 k hk m⟩⟩

theorem log_A (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {z : (Σ k, ι k) → ℂ}
    (hz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    (τ : Ψ) (a i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) :
    (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z) * mfac j a i h) ≠ 0 ∧
    Real.log ‖(if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z) * mfac j a i h)‖ =
      M.upsLog F (τ, i) z + if IsProperStep N j i then 0 else Real.log ‖mfac j a i h‖ := by
  by_cases hp : IsProperStep N j i
  · obtain ⟨k, hk⟩ : ∃ k, M.blk (τ, i) = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hp
    simp [hp, FlagModel.upsLog, hk]
  · have hn := (M.blk_none (τ, i)).2 hp
    obtain ⟨h1, h2, h3⟩ := hG.2.2 _ hn
    have h4 := val_ne_zero hz h1 h2 h3
    have h5 := mfac_ne a i hh hd
    simp only [if_neg hp, FlagModel.upsLog, hn, Option.elim, norm_mul]
    exact ⟨mul_ne_zero h4 h5, Real.log_mul (norm_ne_zero_iff.2 h4) (norm_ne_zero_iff.2 h5)⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {n d : ℕ} {BM : BaseMetric M n} {FA : FlagAn BM d}
  {Cv : FlagCover M' M} {τ : Ψ} {a b : Fin N} {k₀' : K'} {ca cb : Fin N}

theorem norm_pt (CR : CovReal FA Cv) (S' : Sw M' τ a b k₀' ca cb) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {g h : MRing fun o : Option K' => ι' (o.getD k₀')} {dg dh : Option K' → ℕ} (hg : IsMultiHomog g dg)
    (hh : IsMultiHomog h dh) (hxi : ∑ p, xiCoef τ a p * (CR.Re.ref p).a k₀' = -2)
    (hdeg : ∀ o : Option K', (dg o : ℤ) - dh o =
      o.elim 1 fun k => -(∑ p, xiCoef τ a p * (CR.Re.ref p).a k) - if k₀' = k then 1 else 0)
    (LC : ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)), ∀ F, M'.IsFrame F →
      M'.GoodAt F (mCoordIdeal (basePart M'.blk (fstPt k₀' z))) → ∀ (hm : Matrix (Fin N) (Fin N) ℂ) (t : ℂ),
      IsBlockDiag j hm → hm.det ≠ 0 → (∀ i, M'.ExactAt F (τ, i) (fstPt k₀' z) hm) →
      M'.ExactAt F (τ, a) (sndPt k₀' z) (hm * (1 + Matrix.single cb ca t)) →
      eval z (map (Int.castRingHom ℂ) g) = t * (∏ i : Fin N, (if IsProperStep N j i then 1 else
        valAt M'.x (F.υ (τ, i)) (basePart M'.blk (fstPt k₀' z)) * mfac j a i hm) ^ xiCoef τ a (τ, i)) *
        eval z (map (Int.castRingHom ℂ) h))
    {z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)))
    (g0 : eval z (map (Int.castRingHom ℂ) g) ≠ 0) (h0 : eval z (map (Int.castRingHom ℂ) h) ≠ 0)
    {w₀ w₁ : (Σ k, ι k) → ℂ} (hw₀ : w₀ ∈ mcPts (mCoordIdeal y)) (hw₁ : w₁ ∈ mcPts (mCoordIdeal y))
    (i₀ : IsImg Cv (fstPt k₀' z) w₀) (i₁ : IsImg Cv (sndPt k₀' z) w₁) :
    ∃ (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (hm : Matrix (Fin N) (Fin N) ℂ) (t : ℂ),
      M.IsFrame F ∧ M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) ∧ SameOrbit z₀ w₀ ∧ SameOrbit z₁ w₁ ∧
      IsBlockDiag j hm ∧ hm.det ≠ 0 ∧ t ≠ 0 ∧ (∀ i, M.ExactAt F (τ, i) z₀ hm) ∧
      (∀ i, M.ExactAt F (τ, i) z₁ (hm * (1 + Matrix.single cb ca t))) ∧
      lognorm τ a k₀' g h CR.Re.ref z = normRhs M τ a F z₀ z₁ hm t := by
  have hz₀ := fst_mem hz
  have hz₁ := S'.snd_mem hy' hz
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ (CPts.base_mem M' hz₀)
  obtain ⟨z', oz', H, t, fl₀, fl₁⟩ := S'.data hz₀ hz₁ hF' hg'
  obtain ⟨u₀, ou₀, bu₀, ex₀⟩ := exists_exact M' fl₀
  obtain ⟨u₁, ou₁, bu₁, ex₁⟩ := exists_exact M' fl₁
  have bu : basePart M'.blk u₁ = basePart M'.blk u₀ := by rw [bu₀, bu₁, Pts.basePart_snd M' S'.hk]
  have e₁ : sndPt k₀' (joinPt k₀' u₀ u₁) = u₁ := by
    refine join_v₁ fun k hk m => ?_
    by_cases hkb : ∀ p, M'.blk p ≠ some k
    · exact (congrFun bu ⟨⟨k, hkb⟩, m⟩).symm
    · obtain ⟨⟨τ', i⟩, hp⟩ : ∃ p, M'.blk p = some k := by simpa using hkb
      rw [(ex₀ _).2 k hp m, (ex₁ _).2 k hp m, bu]
      by_cases e' : τ' = τ
      · subst e'
        have hi : i ≠ a := fun e => hk (by rw [e, S'.hk] at hp; exact (Option.some.inj hp).symm)
        simp only [Function.update_self, minor_transv M'.j_le S'.hb S'.hab S'.hca S'.hcb hi]
      · simp only [Function.update_of_ne e']
  have e₀ : fstPt k₀' (joinPt k₀' u₀ u₁) = u₀ := rfl
  have oj : SameOrbit (joinPt k₀' u₀ u₁) z := orbit_trans (join_orbit ou₀ ou₁) oz'
  obtain ⟨g1, h1, hl⟩ := lognorm_orbit hg hh hxi hdeg oj hz₀.1 hz₁.1 g0 h0
  have hj := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) oj hz
  have o₀ : SameOrbit u₀ (fstPt k₀' z) := e₀ ▸ fst_orbit oj
  have o₁ : SameOrbit u₁ (sndPt k₀' z) := e₁ ▸ snd_orbit oj
  have m₀ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₀ hz₀
  have m₁ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₁ hz₁
  have hb := CPts.base_mem M' m₀
  have hG' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk u₀)) := by rw [ideal_orbit (base_orbit o₀)]; exact hg'
  have hlc := LC _ hj F' hF' hG' (H τ) t (fl₀.2.1 τ).1 (fl₀.2.1 τ).2 (fun i => ex₀ (τ, i))
    (by rw [e₁]; simpa only [Function.update_self] using ex₁ (τ, a))
  rw [e₀] at hlc
  have ht : t ≠ 0 := fun e => g1 (by rw [hlc, e, zero_mul, zero_mul])
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F, hF, hG⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  obtain ⟨x₀, ox₀, bx₀, fx₀⟩ := i₀ u₀ o₀ F' F hF' hF hG' hG H (flag_of_exact M' (τ, a) fl₀.2.1 ex₀)
  obtain ⟨x₁, ox₁, bx₁, fx₁⟩ := i₁ u₁ o₁ F' F hF' hF (by rw [bu]; exact hG') (by rw [bu]; exact hG) _
    (flag_of_exact M' (τ, a) fl₁.2.1 ex₁)
  obtain ⟨z₀, oz₀, bz₀, ez₀⟩ := exists_exact M fx₀
  obtain ⟨z₁, oz₁, bz₁, ez₁⟩ := exists_exact M fx₁
  rw [← bz₀] at bx₀
  rw [← bz₁] at bx₁
  have hI := CoordinateConeArithVar.isMultiHomogIdeal y
  have M₀ := fun p => CR.metric _ m₀ _ (mem_mcPts_of_sameOrbit hI (orbit_trans oz₀ ox₀) hw₀) F' F hF' hF hG' hG bx₀ p _
    (fl₀.2.1 p.1).1 (fl₀.2.1 p.1).2 (ex₀ p) (ez₀ p)
  have M₁ := fun p => CR.metric _ m₁ _ (mem_mcPts_of_sameOrbit hI (orbit_trans oz₁ ox₁) hw₁) F' F hF' hF
    (by rw [bu]; exact hG') (by rw [bu]; exact hG) bx₁ p _ (fl₁.2.1 p.1).1 (fl₁.2.1 p.1).2 (ex₁ p) (ez₁ p)
  rw [bu] at bx₁ ez₁
  have hT := FibreCount.trans_unit Cv hb hF' hF hG' hG τ
  have hGz : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [ideal_orbit bx₀]; exact hG
  have hbz := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) bx₀ hbv
  refine ⟨z₀, z₁, F, Cv.trans F' F (basePart M'.blk u₀) τ * H τ, t, hF, hGz, orbit_trans oz₀ ox₀, orbit_trans oz₁ ox₁,
    (fx₀.2.1 τ).1, (fx₀.2.1 τ).2, ht, fun i => ez₀ (τ, i),
    fun i => by simpa only [Function.update_self, Matrix.mul_assoc] using ez₁ (τ, i), ?_⟩
  have A' := fun i => log_A M' hb hG' τ a i (fl₀.2.1 τ).1 (fl₀.2.1 τ).2
  have A := fun i => log_A M hbz hGz τ a i (fx₀.2.1 τ).1 (fx₀.2.1 τ).2
  have hU' : ∀ p, M'.upsLog F' p u₁ = M'.upsLog F' p u₀ := fun p => by simp only [FlagModel.upsLog, bu]
  have hU : ∀ p, M.upsLog F p z₁ = M.upsLog F p z₀ := fun p => by
    simp only [FlagModel.upsLog, valAt_orbit bx₀ hbv, valAt_orbit bx₁ hbv]
  have hs := sum_detFac M.j_le S'.hb S'.hab hT.1 hT.2
  have hx : ∀ i, xiCoef () a ((), i) = xiCoef τ a (τ, i) := fun i => by simp [xiCoef]
  simp only [hx] at hs
  rw [← hl, lognorm, hlc, e₀, e₁, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (left_ne_zero_of_mul (hlc ▸ g1)))
    (norm_ne_zero_iff.2 h1), log_fac τ a ht fun i => (A' i).1]
  show _ = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) *
      mfac j a i (Cv.trans F' F (basePart M'.blk u₀) τ * H τ)) ^ xiCoef τ a (τ, i)‖ + _
  rw [log_fac τ a ht fun i => (A i).1, sum_xi_prod, sum_xi_prod]
  simp only [fun i => (A' i).2, fun i => (A i).2]
  have fin : ∀ i, (xiCoef τ a (τ, i) : ℝ) * (M'.upsLog F' (τ, i) u₀ + if IsProperStep N j i then 0 else
        Real.log ‖mfac j a i (H τ)‖) + (1 / 2) * ((xiCoef τ a (τ, i) : ℝ) *
        (Real.log ((CR.Re.ref (τ, i)).h u₀) + Real.log ((CR.Re.ref (τ, i)).h u₁))) =
      (xiCoef τ a (τ, i) : ℝ) * (M.upsLog F (τ, i) z₀ + if IsProperStep N j i then 0 else
        Real.log ‖mfac j a i (Cv.trans F' F (basePart M'.blk u₀) τ * H τ)‖) + (1 / 2) * ((xiCoef τ a (τ, i) : ℝ) *
        (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) +
      (xiCoef τ a (τ, i) : ℝ) * (Real.log ‖detFac j i (Cv.trans F' F (basePart M'.blk u₀) τ)‖ -
        if IsProperStep N j i then 0 else Real.log ‖mfac j a i (Cv.trans F' F (basePart M'.blk u₀) τ)‖) := fun i => by
    have r₀ := M₀ (τ, i)
    have r₁ := M₁ (τ, i)
    rw [hU, hU', bu] at r₁
    rw [mfac_mul a i _ (fl₀.2.1 τ).1, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (mfac_ne a i hT.1 hT.2))
      (norm_ne_zero_iff.2 (mfac_ne a i (fl₀.2.1 τ).1 (fl₀.2.1 τ).2))]
    split_ifs
    · linear_combination (1 / 2 * (xiCoef τ a (τ, i) : ℝ)) * (r₀ + r₁)
    · linear_combination (1 / 2 * (xiCoef τ a (τ, i) : ℝ)) * (r₀ + r₁)
  have tot := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin N)) = _) fun i _ => fin i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs] at tot
  linarith

end PositivityTheory.Xgp.c_sqsys
