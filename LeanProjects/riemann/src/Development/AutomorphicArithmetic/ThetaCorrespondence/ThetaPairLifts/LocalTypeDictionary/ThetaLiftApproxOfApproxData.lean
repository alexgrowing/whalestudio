import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalOfCuspType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalOfCuspTypeStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.ThetaArrowApprox
theorem theta_lift_approx_of_approx_data (hL1 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε) (hL2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (ε : Bool) (S T : GlobalTheory.Grid.Node D) (U : AddSubgroup (WO S.V T.V)), IsOpen (U : Set (WO S.V T.V)) → ∀ Φ, Φ ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U → ∀ (μ : Measure (WO S.V T.V)) (𝓕 : Set (WO S.V T.V)), IsCovolOne (ratL T.V (GlobalTheory.Grid.sgn ε S.V)) μ 𝓕 → ∀ (d : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO S.V T.V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ ε S T (f l)) ∧ (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) ∈ GlobalTheory.Size.thetaLevel ψ (GlobalTheory.Grid.sgn ε S.V) T.V U ∧ @GlobalTheory.Size.sobO D ψ θ (GlobalTheory.Grid.sgn ε S.V) T.V μ 𝓕 d (Φ - ∑ l, GlobalTheory.Grid.fock ψ θ ε S T (f l) (p l)) < ENNReal.ofReal δ) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  intro hLC hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨hν, hfd⟩ := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hvol := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν hfd
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (G.V i j).V.rank (G.V i (j + 1)).V.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (G.V i j).V (G.V i (j + 1)).V
  obtain ⟨C0, hC0, hK⟩ := (H _ _ rfl rfl).real R.ψ hRB.inf hU
  obtain ⟨Hc, hHc⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact _ hC
  have hrd := GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  obtain ⟨B, hB⟩ := hrd.2.2 Ae
  set M : ℝ := max Hc 1 with hM
  set Kc : ℝ := C0 * M ^ Ae * 2 ^ Ae with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have kb : ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ h ∈ C, ∀ g,
      ‖thetaKO (G.th t i j).ω h g f‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * GlobalTheory.Grow.quotHeight _ g ^ Ae := by
    intro f hf h hh g
    have hM1 : 0 ≤ GlobalTheory.Grow.height _ h := (GlobalTheory.Grow.height_pos _ h).le
    have hMh : GlobalTheory.Grow.height _ h ^ Ae ≤ M ^ Ae := pow_le_pow_left₀ hM1 ((hHc h hh).trans (le_max_left _ _)) Ae
    have h1 : ∀ g', ‖thetaKO (G.th t i j).ω h g' f‖ ≤
        (C0 * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d f).toReal * M ^ Ae) * GlobalTheory.Grow.height _ g' ^ Ae := by
      intro g'
      refine ((hK _ _ _ hω μ 𝓕 hμ f hf).2 h g').trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMh (mul_nonneg hC0 ENNReal.toReal_nonneg))
        (pow_nonneg (GlobalTheory.Grow.height_pos _ g').le _)
    have := GlobalTheory.Grow.norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf.1 h) h1 g
    refine this.trans (le_of_eq ?_)
    rw [hKc]; ring
  set s0 : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d Φ).toReal with hs0
  set Vl : ℝ := (G.meas t i (j + 1)).ν.real (G.meas t i (j + 1)).fd with hVl
  have hVl0 : 0 ≤ Vl := measureReal_nonneg
  have hs00 : 0 ≤ s0 := ENNReal.toReal_nonneg
  set K0 : ℝ := Kc * s0 with hK0
  have hK00 : 0 ≤ K0 := mul_nonneg hKc0 hs00
  set ε1 : ℝ := δ / (3 * (K0 * Vl + 1)) with hε1
  have hε10 : 0 < ε1 := by positivity
  obtain ⟨n1, F, v, hF, happ⟩ := hL1 D R.θ hRB.inf hP (G.V i (j + 1)) φ hφ Ae ε1 hε10
  set B' : ℝ := max B 0 with hB'
  set η : ℝ := δ / (3 * (Kc * (B' + ε1) * Vl + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨n2, f, p, hf, hlev, hsob⟩ :=
    hL2 D R.ψ R.θ hRB.inf hω.std false (G.V i j) (G.V i (j + 1)) U hU Φ hΦU μ 𝓕 hμ d η hη0
  have hsob' : (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d
      (Φ - ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l))).toReal < η :=
    ENNReal.toReal_lt_of_lt_ofReal hsob
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hB0 : ∀ g, ‖φ g‖ * GlobalTheory.Grow.quotHeight _ g ^ Ae ≤ B' := fun g => (hB g).trans (le_max_left _ _)
  let e := (finProdFinEquiv : Fin n1 × Fin n2 ≃ Fin (n1 * n2))
  refine ⟨n1 * n2, fun l => f (e.symm l).2, fun l => p (e.symm l).2, fun l => F (e.symm l).1,
    fun l => v (e.symm l).1, fun l => hf _, fun l => hF _, fun h hh => ?_⟩
  have hLCa := (hLC D hS G₀ Pl0 T A Ks R G hRB hG).th t i j hi hj
  have hintl : ∀ l : Fin (n1 * n2), IntegrableOn (fun g => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν := by
    intro l
    obtain ⟨_, _, hall⟩ := hLCa _ (hf (e.symm l).2) _ (hF (e.symm l).1)
    exact (hall _ _ h).1
  rw [← integral_finset_sum _ (fun l _ => hintl l),
    ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hintl l)]
  set Φ' := ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l) with hΦ'
  have hsum : ∀ g, ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g = thetaKO (G.th t i j).ω h g Φ' * ∑ a, F a (v a) g := by
    intro g
    refine (Equiv.sum_comp e.symm (fun ab : Fin n1 × Fin n2 => thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f ab.2) (p ab.2)) * F ab.1 (v ab.1) g)).trans ?_
    rw [Fintype.sum_prod_type, hΦ']
    unfold thetaKO
    rw [map_sum, Finset.sum_apply, Finset.sum_mul_sum, Finset.sum_comm]
  have hq : ∀ g, 0 < GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := fun g => pow_pos (GlobalTheory.Grow.quotHeight_pos _ g) _
  have bound : ∀ g, ‖thetaKO (G.th t i j).ω h g Φ * φ g - ∑ l : Fin (n1 * n2), thetaKO (G.th t i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f (e.symm l).2) (p (e.symm l).2)) *
      F (e.symm l).1 (v (e.symm l).1) g‖ ≤ K0 * ε1 + Kc * η * (B' + ε1) := by
    intro g
    rw [hsum g]
    have hab : thetaKO (G.th t i j).ω h g Φ - thetaKO (G.th t i j).ω h g Φ' =
        thetaKO (G.th t i j).ω h g (Φ - Φ') := by
      unfold thetaKO; rw [map_sub, Pi.sub_apply]
    have e1 : ∀ a b x y : ℂ, a * x - b * y = a * (x - y) + (a - b) * y := fun a b x y => by ring
    rw [e1, hab]
    have ha : ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := kb Φ hΦU h hh g
    have hxy : ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ ε1 := happ g
    have hd : ‖thetaKO (G.th t i j).ω h g (Φ - Φ')‖ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
      (kb _ hlev h hh g).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsob'.le hKc0) (hq g).le)
    have hy : ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae ≤ B' + ε1 := by
      have h3 : ‖∑ a, F a (v a) g‖ ≤ ‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖ := by
        simpa using norm_sub_le (φ g) (φ g - ∑ a, F a (v a) g)
      calc ‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae
          ≤ (‖φ g‖ + ‖φ g - ∑ a, F a (v a) g‖) * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae :=
            mul_le_mul_of_nonneg_right h3 (hq g).le
        _ = ‖φ g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae +
            ‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae := add_mul _ _ _
        _ ≤ B' + ε1 := add_le_add (hB0 g) hxy
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc _ ≤ K0 * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖φ g - ∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = K0 * (‖φ g - ∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ K0 * ε1 := mul_le_mul_of_nonneg_left hxy hK00
    · rw [norm_mul]
      calc _ ≤ Kc * η * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae * ‖∑ a, F a (v a) g‖ :=
            mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        _ = Kc * η * (‖∑ a, F a (v a) g‖ * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * η * (B' + ε1) := mul_le_mul_of_nonneg_left hy (by positivity)
  refine (norm_setIntegral_le_of_norm_le_const hvol fun g _ => bound g).trans_lt ?_
  have t1 : K0 * ε1 * Vl ≤ δ / 3 := by
    have h0 : K0 * Vl + 1 ≠ 0 := by positivity
    calc K0 * ε1 * Vl = (K0 * Vl) * ε1 := by ring
      _ ≤ (K0 * Vl + 1) * ε1 := mul_le_mul_of_nonneg_right (by linarith) hε10.le
      _ = δ / 3 := by rw [hε1]; field_simp
  have t2 : Kc * η * (B' + ε1) * Vl ≤ δ / 3 := by
    have h0 : Kc * (B' + ε1) * Vl + 1 ≠ 0 := by positivity
    calc Kc * η * (B' + ε1) * Vl = (Kc * (B' + ε1) * Vl) * η := by ring
      _ ≤ (Kc * (B' + ε1) * Vl + 1) * η := mul_le_mul_of_nonneg_right (by linarith) hη0.le
      _ = δ / 3 := by rw [hη]; field_simp
  have : (K0 * ε1 + Kc * η * (B' + ε1)) * Vl = K0 * ε1 * Vl + Kc * η * (B' + ε1) * Vl := by ring
  rw [this]
  linarith
theorem theta_lift_approximates : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ :=
  _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approx_of_approx_data _root_.GlobalTheory.T.twist_cusp_form_approx_weighted GlobalTheory.FockApprox.theta_approx_fock
end GlobalTheory.ThetaArrowApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximation_by_theta_lifts : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ C : Set (GA D (G.V i j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V i j) (G.V i (j + 1))) (F : Fin n → (G.V i (j + 1)).Maps) (v : Fin n → SmT (G.V i (j + 1)).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l)) ∧ (∀ l, F l ∈ (G.V i (j + 1)).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) - ∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν‖ < δ := by
  first | exact @_root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates | exact _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates | (intros; apply _root_.GlobalTheory.ThetaArrowApprox.theta_lift_approximates <;> assumption)
end
