import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyWeightSectionProducts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyWeightSectionProductsStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CuspMulUnit
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end GlobalTheory.CuspMulUnit
namespace GlobalTheory.CuspMulUnit
set_option maxHeartbeats 800000 in
theorem pow_mul_mem_cusp_of_unit : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
  intro _hP D T j Y e o hY hE la f hf u _u' _t eu hu _ht _huu
  refine ⟨0, fun k _ φ _φ' _t' w hφ _ht' _hφφ _hb a n hDom hF => ?_⟩
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  by_cases hF0 : f ^ (k + 1) * (u * φ) = 0
  · rw [hF0]; exact Submodule.zero_mem _
  set R := f ^ k * (u * φ) with hR
  have hFR : f ^ (k + 1) * (u * φ) = f * R := by rw [hR, pow_succ', mul_assoc]
  have hR0 : R ≠ 0 := fun h => hF0 (by rw [hFR, h, mul_zero])
  have hfsec : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) := GlobalTheory.AllWt.cuspW_le_secZ _ hf
  have hRsec := GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ' hfsec k) (GlobalTheory.AllWt.mul_mem_secZ hu hφ)
  have hFsec' := GlobalTheory.AllWt.mul_mem_secZ hfsec hRsec
  rw [← hR, ← hFR] at hFsec'
  have hFsec : f ^ (k + 1) * (u * φ) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ (T.Q.Dw j) (wtZ a n)) := by
    rw [GlobalTheory.AllWt.exZ_wtZ, GlobalTheory.AllWt.secZ_nat]; exact hF
  have heq := eq_of_mem_secZ hFsec hFsec' hF0
  set G : WTZ D.host.E := wtZ a n - wtOf (T.Q.Dw j) la 0 with hG
  have hexG : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) (wtZ a n) - GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 := by
    funext i; cases i <;> rfl
  have hRG : R ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ (T.Q.Dw j) G) := by
    rw [hexG, heq, add_sub_cancel_left]; exact hRsec
  have hGe : Even G.2 := by
    have h2 : G.2 = (n : ℤ) := by simp [hG, wtZ, GlobalTheory.AllWt.wtOf_snd]
    rw [h2]; exact (Int.even_coe_nat n).2 hDom.2
  have hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ → G.1 (τ, j') ≤ G.1 (τ, i) := by
    have hne : ∀ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ), G.1 (τ, m + 1) ≤ G.1 (τ, m) := by
      intro τ m hm
      by_contra hlt
      push_neg at hlt
      exact hR0 (GlobalTheory.NonDomVanish.eq_zero_of_lt hRG τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt)
    intro τ i j' hij hj'
    revert hj'
    induction j', hij using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ m hm ih => intro hj'; exact (hne τ m hj').trans (ih (by omega))
  rw [← GlobalTheory.AllWt.cuspW_wtZ, GlobalTheory.AllWt.mem_cuspW]
  refine ⟨hFsec, fun σ hσ => ?_⟩
  have hU := hY.unf σ hσ
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hr, -⟩ := hU
    have h1 : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.r
      omega
    omega
  have hK := GlobalTheory.HSApp.VanishingBound.keySec D T j Y e o hY σ hσ
  have hfh := (GlobalTheory.AllWt.mem_cuspW.1 hf).2 σ hσ
  refine holCusp_mem_holSub _ _ fun kk => ?_
  have hRs : ((Y.U σ).X kk).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) G kk) (rdU (Y.U σ) R kk) :=
    GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU _ _ _ _ _ _ σ _ (Y.U σ) hK hσ hU hpq G hGe hdec R hRG kk
  have hfS := (GlobalTheory.FlatTw.mem_holSub_model _ _ _).1 hfh kk
  have hw : GlobalTheory.AllWt.modelWt (Y.U σ) (wtZ a n) kk =
      GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) kk + GlobalTheory.AllWt.modelWt (Y.U σ) G kk := by
    rw [← GlobalTheory.AllWt.modelWt_add (Y.U σ) (GlobalTheory.AllWt.even_wtOf la 0) hGe kk, hG, add_sub_cancel]
  have hsecF : ((Y.U σ).X kk).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtZ a n) kk)
      (rdU (Y.U σ) (f ^ (k + 1) * (u * φ)) kk) := by
    rw [GlobalTheory.AllWt.modelWt_wtZ]; exact hU.2.2.2.2.1 a n hDom _ hF kk
  refine GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ hsecF (GlobalTheory.CuspFrom.isModerate _ hf1 hsecF) fun ξ hξ x hx => ?_
  rw [hFR, GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, hw]
  exact fj_mul_eq_zero _ hf1 hfS hRs ξ hξ x hx
end GlobalTheory.CuspMulUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_unit_mem_cusp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
  first | exact @_root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit | exact _root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit | (intros; apply _root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit <;> assumption)
end
