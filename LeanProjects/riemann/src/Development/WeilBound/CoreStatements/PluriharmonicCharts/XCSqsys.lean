import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystemStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareBaseIntersection
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSwap
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWSec
import Development.WeilBound.CoreStatements.PluriharmonicCharts.WCoZero
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MapAevalInt
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MapsToTwoFlagFramesOrthogonalOfIsometry
import Development.WeilBound.CoreStatements.PluriharmonicCharts.LognormOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {n d : ℕ} {BM : BaseMetric M n} {FA : FlagAn BM d}
  {Cv : FlagCover M' M}

theorem lift_inj (FA : FlagAn BM d) {x x' : FA.Re.R.X} (h : SameOrbit (FA.Re.R.lift x x) (FA.Re.R.lift x' x')) :
    x = x' :=
  FA.Re.R.inj x x' (fun h => by
    have := h.2 1 (by rw [FA.J_top]; trivial)
    simp at this) h

theorem varpi_eq (CR : CovReal FA Cv) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (hy' : IsArithVar (mCoordIdeal y') (d + 2)) {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y'))
    {x₀ : FA.Re.R.X} (hi : IsImg Cv z (FA.Re.R.lift x₀ x₀)) : CR.ϖ z = FA.Re.π x₀ := by
  obtain ⟨x₁, hx₁⟩ := (GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA).2 (CR.ϖ z)
  have h1 : IsImg Cv z (FA.Re.R.lift x₁ x₁) := fun z₁ o F' F hF' hF hg' hg h hfl =>
    CR.flags z₁ (mem_mcPts_of_sameOrbit hy'.2.1.2.1 o hz) F' F hF' hF hg' hg h hfl x₁
      (hx₁.trans (CR.ϖ_torus z z₁ hz o).symm)
  rw [← hx₁, lift_inj FA (GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z hz _ _ h1 hi)]

theorem pot_pull (CR : CovReal FA Cv) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (hy' : IsArithVar (mCoordIdeal y') (d + 2)) {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    {P J : Ideal (MRing ι₂)} {e : ℕ} (R : AnLogRes P J e) {κ : K' → K₂} {v : (Σ k, ι' k) → Σ k, ι₂ k}
    (hv : IsBlockMap κ v) (hP : ∀ z ∈ mcPts P, z ∘ v ∈ mcPts (mCoordIdeal y')) (g₀ : R.X → FA.Re.R.X)
    (hi : ∀ x, IsImg Cv (R.lift x x ∘ v) (FA.Re.R.lift (g₀ x) (g₀ x))) (p : Ψ × Fin N) (x : R.X) :
    LocRe R.A x fun u => Real.log ((CR.Re.ref p).h (R.lift x u ∘ v)) -
      (FA.S.th (some p)).φ (FA.Re.π (g₀ x)) (FA.Re.π (g₀ u)) := by
  have hg₀ : HoloMap R.A FA.Re.R.A g₀ := by
    refine GlobalTheory.T.log_resolution_map_locally_analytic _ _ _ _ _ _ _ _ _ _ FA.Re.R R g₀ FA.J_top fun x => ?_
    obtain ⟨V, f, hV, hzV, hf, hff⟩ := GlobalTheory.T.flag_cover_arithmetic_first K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _
      (hP _ (R.mem x x (R.mem_U x)))
    refine ⟨(fun z => z ∘ v) ⁻¹' V, fun z => f (z ∘ v), hV.preimage (continuous_comp_idx v), hzV,
      fun z hz => (hf _ hz).comp (f := fun z => z ∘ v) (analytic_comp_idx v z), fun z' hz' x' hx' => ?_⟩
    exact GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (hP _ hz'.2) _ _ (hff _ ⟨hz'.1, hP _ hz'.2⟩).2
      ((hi x').orbit (FibreCount.comp_orbit hv hx') (Cj.sameOrbit_refl _))
  have hW : IsOpen (R.U x ∩ g₀ ⁻¹' FA.Re.R.U (g₀ x)) := (R.isOpen_U x).inter ((FA.Re.R.isOpen_U _).preimage hg₀.1)
  have L1 := pot_loc CR hy hy' (A := R.A) hW ⟨R.mem_U x, FA.Re.R.mem_U _⟩ (Z := fun u => R.lift x u ∘ v)
    (fun q => holo_mono (R.holo x (v q)) Set.inter_subset_left) (fun u hu => hP _ (R.mem x u hu.1))
    (Y := fun u => FA.Re.R.lift (g₀ x) (g₀ u))
    (fun q => holo_mono (GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot.holoOn_comp hg₀ (FA.Re.R.holo (g₀ x) q)) Set.inter_subset_right)
    (fun u hu => (FA.Re.R.mem _ _ hu.2).1)
    (fun u hu => (hi u).orbit (FibreCount.comp_orbit hv (R.compat x u u ⟨hu.1, R.mem_U u⟩))
      (FA.Re.R.compat _ _ _ ⟨hu.2, FA.Re.R.mem_U _⟩)) p
  have L2 : LocRe FA.Re.R.A (g₀ x) fun u => Real.log ((fsHerm ι (M.dy p)).h (FA.Re.R.lift (g₀ x) u)) -
      (FA.S.th (some p)).φ (FA.Re.π (g₀ x)) (FA.Re.π u) := by
    have := FA.Re.ref_pot (some p) (g₀ x) trivial
    rw [FA.ref_some] at this
    exact this
  exact (L1.add (L2.comp hg₀)).congr isOpen_univ trivial fun u _ => by ring

theorem log_comb {σ : Type} [Fintype σ] (A : σ → HermLine ι) (ε : σ → ℤ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Real.log ((combLine A ε).h z) = ∑ p, (ε p : ℝ) * Real.log ((A p).h z) := by
  rw [combLine_h, Real.log_prod fun p _ => zpow_ne_zero _ ((A p).pos z hz).ne']
  simp only [Real.log_zpow]

end PositivityTheory.Xgp.c_sqsys

open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq PositivityTheory.Xgp.c_sqsys GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter in
theorem PositivityTheory.Xgp.t_c_sqsys : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (CR : CovReal FA Cv), IsArithVar (mCoordIdeal y) (d + 2) → ∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → Nonempty (SqSys CR.Re (τ, a) (xiCoef τ a)) := by
  intro hI K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA K' _ ι' _ Φ' _ y' M' Cv CR hy τ a b hb hab
  have hy' : IsArithVar (mCoordIdeal y') (d + 2) := CR.Re.arith
  obtain ⟨k₀, ca, cb, hk, hca, hcb, -, -, -⟩ := PositivityTheory.Xgp.t_c_swap K ι Φ y Ψ N j M τ a b hb hab
  obtain ⟨k₀', ca', cb', hk', hca', hcb', -, hxi', hdy'⟩ := PositivityTheory.Xgp.t_c_swap K' ι' Φ' y' Ψ N j M' τ a b hb hab
  obtain rfl : ca = ca' := Fin.ext (hca.trans hca'.symm)
  obtain rfl : cb = cb' := Fin.ext (hcb.trans hcb'.symm)
  have S : Sw M τ a b k₀ ca cb := ⟨hb, hab, hk, hca, hcb, PositivityTheory.Xgp.t_c_w_arith⟩
  have S' : Sw M' τ a b k₀' ca cb := ⟨hb, hab, hk', hca, hcb, PositivityTheory.Xgp.t_c_w_arith⟩
  obtain ⟨Q, RW, e, he, hde, hq0, hq1, -, hnorm⟩ :=
    GlobalTheory.T.flag_adjacent_swap_square_system hI K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hab hk hca hcb hy
  obtain ⟨g, h, dg, dh, hg, hh, hgn, hhn, hdeg, hq, hdiv⟩ :=
    PositivityTheory.Xgp.t_c_w_sec K' ι' Φ' y' Ψ N j M' d τ a b k₀' ca cb hb hab hk' hca hcb hy'
  have LC := PositivityTheory.Xgp.c_algsq.lc K' ι' Φ' y' Ψ N j M' d τ a b k₀' ca cb hb hab hk' hca hcb hy' g h dg dh hg hh hdeg hq
  obtain ⟨J, R', γ, br, hγ, hdegW, hrel⟩ := mapsTo_twoFlagFramesOrthogonal_of_isometry hI.2.1.1 Cv S S' hy hy' Q.SW.A RW e he hde
  have hxi : ∑ p, xiCoef τ a p * (CR.Re.ref p).a k₀' = -2 := by simpa only [CR.ref_deg] using hxi'
  have hdeg₁ : ∀ o : Option K', (dg o : ℤ) - dh o = o.elim 1 fun k => -(combLine CR.Re.ref (xiCoef τ a)).a k -
      (if M'.blk (τ, a) = some k then 1 else 0) := by simpa only [combLine_a, CR.ref_deg] using hdeg
  have hdeg₂ : ∀ o : Option K', (dg o : ℤ) - dh o =
      o.elim 1 fun k => -(∑ p, xiCoef τ a p * (CR.Re.ref p).a k) - if k₀' = k then 1 else 0 := by
    simpa only [combLine_a, hk', Option.some.injEq] using hdeg₁
  have hv₀ := Pts.isBlockMap_v₀ (ι := ι') k₀'
  have hv₁ := isBlockMap_v₁ (ι := ι') k₀'
  have hsurj := (GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA).2
  have o₀ : ∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x)) := hq0
  have o₁ : ∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x)) := by
    intro x x₀ hx
    obtain ⟨z₁, h1, h2, h3⟩ := hq1 x x₀ hx
    have : z₁ = sndPt k₀ (RW.lift x x) := by
      funext ⟨k, m⟩
      by_cases ek : k = k₀
      · subst ek
        rw [h3, Pts.snd_self]
      · rw [h2 ⟨k, m⟩ ek, Pts.snd_fst_ne ek]
        rfl
    exact this ▸ h1
  choose g₀ hg₀ using fun x => hsurj (Q.q 0 (e (γ x)))
  choose g₁ hg₁ using fun x => hsurj (Q.q 1 (e (γ x)))
  have i₀ : ∀ x, IsImg Cv (fstPt k₀' (R'.lift x x)) (FA.Re.R.lift (g₀ x) (g₀ x)) := fun x =>
    (hrel x).1.orbit (Cj.sameOrbit_refl _) (o₀ _ _ (hg₀ x))
  have i₁ : ∀ x, IsImg Cv (sndPt k₀' (R'.lift x x)) (FA.Re.R.lift (g₁ x) (g₁ x)) := fun x =>
    (hrel x).2.orbit (Cj.sameOrbit_refl _) (o₁ _ _ (hg₁ x))
  have mem : ∀ x, R'.lift x x ∈ mcPts _ := fun x => R'.mem x x (R'.mem_U x)
  have m₀ := fun x => fst_mem (mem x)
  have m₁ := fun x => S'.snd_mem hy' (mem x)
  have w₀ : ∀ x, CR.ϖ (fstPt k₀' (R'.lift x x)) = Q.q 0 (e (γ x)) := fun x =>
    (varpi_eq CR hy hy' (m₀ x) (i₀ x)).trans (hg₀ x)
  have w₁ : ∀ x, CR.ϖ (sndPt k₀' (R'.lift x x)) = Q.q 1 (e (γ x)) := fun x =>
    (varpi_eq CR hy hy' (m₁ x) (i₁ x)).trans (hg₁ x)
  have hπ : HoloMap R'.A Q.SW.A (e ∘ γ) := holoMap_comp hγ he
  let ReW : Realis Q.SW (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)) :=
    { arith := S'.arith hy'
      J := J
      R := R'
      π := e ∘ γ
      holo := hπ
      deg := CR.Re.deg
      deg_pos := CR.Re.deg_pos
      br := br
      degree := by rw [CR.deg_eq]; exact hdegW
      ref := fun o => o.elim (pullHerm hv₁ (CR.Re.ref (τ, a))) fun p => pullHerm hv₀ (CR.Re.ref p)
      ref_smooth := fun o => by
        cases o with
        | none =>
          exact SqFirst.isSmoothHerm_of_pull hv₁ (CR.Re.ref_smooth _)
            (isPullHerm_pullHerm hv₁ _)
        | some p =>
          exact SqFirst.isSmoothHerm_of_pull hv₀ (CR.Re.ref_smooth _)
            (isPullHerm_pullHerm hv₀ _)
      ref_pot := fun o x _ => by
        cases o with
        | none =>
          have L1 := pot_pull CR hy hy' R' hv₁ (fun z hz => S'.snd_mem hy' hz) g₁ i₁ (τ, a) x
          have L2 := LocRe.comp hπ (show LocRe Q.SW.A ((e ∘ γ) x) _ from Q.th1 _ trivial)
          simp only [hg₁] at L1
          exact (L1.sub L2).congr isOpen_univ trivial fun u _ => by
            show _ - _ = _ - _ - (_ - _)
            exact (sub_sub_sub_cancel_right _ _ _).symm
        | some p =>
          have L1 := pot_pull CR hy hy' R' hv₀ (fun z hz => fst_mem hz) g₀ i₀ p x
          have L2 := LocRe.comp hπ (show LocRe Q.SW.A ((e ∘ γ) x) _ from Q.th0 p _ trivial)
          simp only [hg₀] at L1
          exact (L1.sub L2).congr isOpen_univ trivial fun u _ => by
            show _ - _ = _ - _ - (_ - _)
            exact (sub_sub_sub_cancel_right _ _ _).symm
      line := fun o t => o.elim (pullHerm hv₁ (CR.Re.line (τ, a) t)) fun p => pullHerm hv₀ (CR.Re.line p t)
      line_deg := fun o t => by
        cases o with
        | none => exact congrArg (pullDeg _) (CR.Re.line_deg _ t)
        | some p => exact congrArg (pullDeg _) (CR.Re.line_deg _ t)
      line_smooth := fun o t h0 h1 => by
        cases o with
        | none =>
          exact SqFirst.isSmoothHerm_of_pull hv₁ (CR.Re.line_smooth _ t h0 (h1.trans Q.t₀_le))
            (isPullHerm_pullHerm hv₁ _)
        | some p =>
          exact SqFirst.isSmoothHerm_of_pull hv₀ (CR.Re.line_smooth _ t h0 (h1.trans Q.t₀_le))
            (isPullHerm_pullHerm hv₀ _)
      line_eq := fun o t h0 h1 x => by
        cases o with
        | none =>
          have := CR.line_pt (τ, a) t h0 (h1.trans Q.t₀_le) _ (m₁ x)
          rw [w₁] at this
          rw [Q.phase_none_eq_comp_second_projection]
          exact this
        | some p =>
          have := CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₀ x)
          rw [w₀] at this
          rw [Q.phase_some_eq_comp_first_projection]
          exact this }
  refine ⟨⟨k₀', Q, mkAlg M' hb hab hk' hca hcb hy' _ hxi g h dg dh hg hh hgn hhn hdeg₁ hdiv, ReW, rfl, ?_,
    fun p t => isPullHerm_pullHerm hv₀ _, fun t => isPullHerm_pullHerm hv₁ _,
    {x | eval (R'.lift x x) (map (Int.castRingHom ℂ) (g * h)) = 0}, ?_, ?_⟩⟩
  · intro p hp t
    refine ⟨by rw [CR.Re.line_deg, CR.ref_deg]; exact hdy' p hp, fun z z' hzz => CR.step p t z z' ?_ ?_⟩
    · exact funext fun q => hzz _ fun e => q.1.2 (τ, a) (hk'.trans (congrArg some e.symm))
    · exact fun k hk m => hzz _ fun e => hp (M'.blk_inj _ _ k hk (hk'.trans (congrArg some e.symm)))
  · exact HilbertSamuel.AnResNullForm.proof HilbertSamuel.NonvanishingDense.full _ _ _ _ _ R'.toAnRes (g * h) _
      (S'.arith hy') (CovMap.isMultiHomog_mul hg hh) fun hm => ((S'.arith hy').2.1.1.mem_or_mem hm).elim hgn hhn
  · intro t h0 h1 x hx
    have hx' : eval (R'.lift x x) (map (Int.castRingHom ℂ) g) * eval (R'.lift x x) (map (Int.castRingHom ℂ) h) ≠ 0 := by
      rw [← map_mul, ← map_mul]; exact hx
    have g0 := left_ne_zero_of_mul hx'
    have h0' := right_ne_zero_of_mul hx'
    obtain ⟨z₀, z₁, F, hm, s, hF, hG, oz₀, oz₁, hmb, hmd, hs, ex₀, ex₁, heq⟩ := norm_pt CR S' hy' hg hh hxi hdeg₂ LC
      (mem x) g0 h0' (fst_mem (RW.mem _ _ (RW.mem_U (γ x)))) (S.snd_mem hy (RW.mem _ _ (RW.mem_U (γ x))))
      (hrel x).1 (hrel x).2
    have hn : _ = normRhs M τ a F z₀ z₁ hm s := hnorm (γ x) z₀ z₁ F hm s hF hG
      (fun x₀ h => orbit_trans (o₀ _ _ h) (orbit_symm oz₀))
      (fun x₀ h => orbit_trans (o₁ _ _ h) (orbit_symm oz₁)) hmb hmd hs ex₀ ex₁
    show Real.log (‖eval (R'.lift x x) (map (Int.castRingHom ℂ) g)‖ / ‖eval (R'.lift x x) (map (Int.castRingHom ℂ) h)‖) +
      (Real.log ((combLine (fun p => CR.Re.line p t) (xiCoef τ a)).h (fstPt k₀' (R'.lift x x))) +
        Real.log ((combLine (fun p => CR.Re.line p t) (xiCoef τ a)).h (sndPt k₀' (R'.lift x x)))) / 2 =
      logNormSec Q.L' Q.v (e (γ x)) + Q.cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) *
        (FA.S.phT (some p) t (Q.q 0 (e (γ x))) + FA.S.phT (some p) t (Q.q 1 (e (γ x))))
    rw [hn, ← heq, lognorm, Real.log_div (norm_ne_zero_iff.2 g0) (norm_ne_zero_iff.2 h0'), log_comb _ _ (m₀ x).1,
      log_comb _ _ (m₁ x).1]
    simp only [fun p => CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₀ x),
      fun p => CR.line_pt p t h0 (h1.trans Q.t₀_le) _ (m₁ x), w₀, w₁, mul_add, Finset.sum_add_distrib]
    ring
