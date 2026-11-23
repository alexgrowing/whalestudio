import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsSectionBoundedByBergmanKernel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunParamsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BergmanKernelThinPartEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BergmanKernelThickPartEstimate

set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovHt.KeySection
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.ThetaConst GlobalTheory.EtaForm
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end Free
theorem theta_function_le_bergman_kernel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C =>
    ∀ u1, Quo p i PP u1 → ∃ β : ℝ, 0 ≤ β ∧ lenT p i PP * β ≤ C * unitE p ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂)
      (xs : Fin ((dat p i).p + (dat p i).q) → LatMod (dat p i) (5 ^ 4)) (f : Rul Y.d.Xo₂ Y.d.c₂),
      Submodule.span (𝓞 (Fm.D x ι).host.E) (Set.range xs) = ⊤ →
      IsTauRule Y.d.Xo₂ Y.d.c₂ 5 (fun _ : Unit => 1) (fun _ => xs) f → ∀ σ, GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X,
      (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z →
        homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩ ≤ Real.exp β ∧
        ENNReal.ofReal (homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩) ^ 3 ≤
          ENNReal.ofReal (Real.exp β) *
            bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  intro hP hH hD hS hF
  refine Closed.imp (Closed.and (_root_.GlobalTheory.T.eta_bound_length_unit_alt hS) (Closed.and (_root_.GlobalTheory.T.bergman_kernel_thin_part_estimate_alt hP hH hD hS hF) (_root_.GlobalTheory.T.exp_neg_B_le_bergOn_of_la1sq_bound hP hH hD hS hF))) ?_
  rintro eps Fm CH - ⟨⟨C₁, c₁, h₁⟩, ⟨_, -, h₂⟩, ⟨C₃, c₃, h₃⟩⟩
  obtain ⟨x0, h⟩ := h₁.and (h₂.and h₃)
  refine ⟨C₁ + C₃, add_nonneg c₁ c₃, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := h x hx hle ι p hp
  obtain ⟨a1, a2, a3, a4⟩ := h₁ i hi Y hY
  obtain ⟨B, b1, b2, b3⟩ := h₃ i hi Y hY u1 hu
  have hb : 1 ≤ (Fm.L x ι).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x ι).sc.one_lt_alt]) _)
  obtain ⟨r1, r2⟩ := a4 1 le_rfl (by push_cast; exact one_le_pow₀ hb)
  refine ⟨_ + B, add_nonneg a2 b1, by rw [mul_add, add_mul]; exact add_le_add a3 b2, fun Z xs f hs hf σ hσ y hy => ?_⟩
  have d := GlobalTheory.T.normSq_thetaConstant_spanning_classes_le_exp _ _ _ _ _ _ σ _ (Y.U σ) (xiR (Fm.D x ι)) hσ (hY.1.unf σ hσ) 5 (by decide) (by norm_num) xs f hs hf
    _ _ _ _ r1 (Or.inr a1) ⟨y.1, y.2.1⟩ y.2.2
  have e2 := h₂ i hi Y hY u1 hu Z σ hσ y hy
  have e3 := b3 Z σ hσ y hy
  have e4 := r2 (((Y.U σ).X y.1).firstMinimumSq y.2.1)
  have ha := homN_nonneg (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD Data.la1 at d
  unfold Data.la1 at e2
  dsimp only at d
  generalize homN (Y.U σ) (xiR (Fm.D x ι)) (wtZ 0 (2 * ((dat p i).p + (dat p i).q))) (f ^ 2) ⟨y.1, y.2.1⟩ = a at d ha ⊢
  generalize bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y = G at e2 e3 ⊢
  generalize GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 = P
    at d a2 ⊢
  generalize hφ : 2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) /
    (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * Real.sqrt (((Y.U σ).X y.1).firstMinimumSq y.2.1) ^ 2) = φ at d e2
  have φ0 : 0 ≤ φ := by rw [← hφ]; positivity
  have key : ∀ s t : ℝ, a ≤ Real.exp s → 3 * s ≤ P + B + t → ENNReal.ofReal (Real.exp t) ≤ G →
      ENNReal.ofReal a ^ 3 ≤ ENNReal.ofReal (Real.exp (P + B)) * G := fun s t h1 h2 h3 => by
    refine le_trans ?_ (mul_le_mul_right h3 _)
    rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ ha h1 3).trans ?_)
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by exact_mod_cast h2)
  have d0 : a ≤ Real.exp (P / 625) := d.trans (Real.exp_le_exp.2 (by split_ifs <;> push_cast <;> linarith))
  refine ⟨d0.trans (Real.exp_le_exp.2 (by linarith)), ?_⟩
  rcases lt_or_ge ((Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1) (Fm.L x ι).sc.b with h | h
  · rw [if_pos (e4 h)] at d
    exact key _ _ d (by push_cast; linarith) (e2 h)
  · exact key _ _ d0 (by linarith) (e3 h)
set_option maxHeartbeats 1000000 in
theorem cover_height_section_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) := by
  intro hP hH hD hS hF
  refine Closed.imp (Closed.and (_root_.GlobalTheory.CovHt.KeySection.theta_function_le_bergman_kernel_alt hP hH hD hS hF) (Closed.and hF (Closed.and hS
    (Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.CovTop.WtShape.wtN_z)))) ?_
  rintro eps Fm CH - ⟨⟨C₁, c₁, h₁⟩, ⟨_, -, h₂⟩, ⟨_, -, h₃⟩, ⟨_, -, h₄⟩, ⟨_, -, h₅⟩⟩
  obtain ⟨x0, h⟩ := h₁.and (h₂.and (h₃.and (h₄.and h₅)))
  refine ⟨C₁ + 10, by linarith, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h x hx hle ι p hp
  obtain ⟨β, b1, b2, b3⟩ := h₁ i hi Y hY u1 hu
  have hN := h₄ i
  have hW := h₅ i
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨by omega, by omega⟩ hY.1
  have hM : 5 ^ 4 ∣ Y.d.l₂.M := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    exact ((pow_dvd_pow_of_dvd (by norm_num : 5 ∣ 15) 4).trans
      (pow_dvd_pow 15 (GlobalTheory.ThetaSteep.four_le_expL hN.big.2.1))).mul_left _
  have hL1 : 1 ≤ (Fm.L x ι).sc.L := by linarith [hN.big.2.1]
  have hf : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast le_trans (by norm_num) hN.f8
  have hr : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hW.sig.2.2 ▸ hL.pos
  have hPP : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hN.ppLow
  have hT : lenT p i (Fm.parT x hx ι).PP * (Fm.parT x hx ι).PP ≤ unitE p := by
    have hD : (1 : ℝ) ≤ dimFlag (dat p i) := by
      rw [hW.dim]
      have m2 := (Fm.D x ι).R.two_le_m
      have k3 := (Fm.D x ι).R.m_add_three_le_k
      have f8 := hN.f8
      exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
    refine le_trans ?_ (hW.what₂.2.trans (h₃ i).2.1)
    rw [mul_comm, mul_assoc _ _ (Fm.L x ι).sc.L]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hL1)
  have hu0 : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * β := by positivity
  refine ⟨β / 2 + 10 * (Fm.parT x hx ι).PP, by positivity, by linarith, fun Z => ?_⟩
  obtain ⟨S, hS⟩ := exists_twist (h₂ i hi Y hY) Z (hasPts Y.U hL.pos hL.good hL.unf Z)
    (12 * (((dat p i).p + (dat p i).q : ℕ) : ℤ))
  obtain ⟨θ, e, t, k1, k2, k3, k4⟩ := exists_section Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict hL hM Z
    S u1 β _ (b3 Z)
  refine ⟨θ, e, t, k1, fun la T io e₀ ho y hy _ => k2 la T io e₀ ho y hy, k3, ?_⟩
  have hc := twist_cost_le hf hr hL1 (Nat.cast_nonneg (dat p i).p) (Nat.cast_nonneg (dat p i).q)
    (by exact_mod_cast hW.sig.2.2) hW.om hN.ppLow
  rw [k4, hS, ← Nat.card_eq_fintype_card, hW.card, hW.sig.2.2]
  push_cast
  linarith
end GlobalTheory.CovHt.KeySection
end
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_bounded_by_bergman_kernel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) := by
  first | exact @_root_.GlobalTheory.CovHt.KeySection.cover_height_section_bound_alt | exact _root_.GlobalTheory.CovHt.KeySection.cover_height_section_bound_alt | (intros; apply _root_.GlobalTheory.CovHt.KeySection.cover_height_section_bound_alt <;> assumption)
end
end
