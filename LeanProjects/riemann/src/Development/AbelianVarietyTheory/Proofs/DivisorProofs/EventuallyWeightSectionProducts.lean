import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OneMemSecAndSecInfEqBot
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnramPtsDefinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
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

theorem pow_mem_secZ' {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (n : ℕ) :
    f ^ n ∈ GlobalTheory.AllWt.secZ Xo c (n • ex) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ n ih => rw [pow_succ, succ_nsmul]; exact GlobalTheory.AllWt.mul_mem_secZ ih hf

theorem eq_of_mem_secZ {e e' : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e)
    (hf' : f ∈ GlobalTheory.AllWt.secZ Xo c e') (h0 : f ≠ 0) : e = e' := by
  classical
  by_contra hne
  apply h0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  funext p y
  let u0 : (c.F)ˣ := Units.mk0 2 two_ne_zero
  let t : Ix Dw → (p.R)ˣ := Pi.mulSingle i (Units.map (algebraMap c.F p.R : c.F →* p.R) u0)
  have hw : ∀ d : Ix Dw → ℤ, ((∏ j, t j ^ d j : (p.R)ˣ) : p.R) = algebraMap c.F p.R ((2 : c.F) ^ d i) := by
    intro d
    rw [Finset.prod_eq_single i]
    · simp only [t, Pi.mulSingle_eq_same, ← map_zpow, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val,
        u0, Units.val_mk0]
    · intro j _ hj
      simp [t, Pi.mulSingle_eq_of_ne hj]
    · simp
  obtain ⟨y', hy'⟩ := GlobalTheory.SecSeparation.exists_frBor y t
  have e1 := hf.2 p t y y' hy'
  have e2 := hf'.2 p t y y' hy'
  rw [hw] at e1 e2
  have hne2 : (2 : c.F) ^ e i - (2 : c.F) ^ e' i ≠ 0 := by
    intro h
    apply hi
    have h1 : algebraMap ℚ c.F ((2 : ℚ) ^ e i) = algebraMap ℚ c.F ((2 : ℚ) ^ e' i) := by
      rw [map_zpow₀, map_zpow₀, map_ofNat]
      exact sub_eq_zero.1 h
    exact zpow_right_injective₀ (by norm_num) (by norm_num) ((algebraMap ℚ c.F).injective h1)
  have hu : IsUnit (algebraMap c.F p.R ((2 : c.F) ^ e i - (2 : c.F) ^ e' i)) := (IsUnit.mk0 _ hne2).map _
  show f p y = 0
  refine hu.mul_right_eq_zero.1 ?_
  rw [map_sub, sub_mul, ← e1, ← e2, sub_self]

end GlobalTheory.CuspMulUnit

namespace GlobalTheory.CuspMulUnit

theorem fj_mul_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (hE : 1 < Module.finrank ℚ E / 2) {la la' : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SS la) (hQ : X.IsSec la' Q) (ξ : Fin r → E) (hξ : X.IsIso ξ) (x) (hx : x ∈ X.dom) :
    X.fj (la + la') ξ 0 (P * Q) x = 0 := by
  have hPs := hP.1.1
  have hm := ReciprocityTheory.ChartRestriction.G.FD.coefficientConvolution_holds (E := E) r X la la' P Q hPs hQ (GlobalTheory.CuspFrom.isModerate _ hE hPs)
    (GlobalTheory.CuspFrom.isModerate _ hE hQ) ξ hξ x hx 0
  have hz : ∀ ν, X.fj la ξ ν P x * X.fj la' ξ (0 - ν) Q x = 0 := by
    intro ν
    by_cases h1 : X.fj la ξ ν P x = 0
    · rw [h1, zero_mul]
    by_cases h2 : X.fj la' ξ (0 - ν) Q x = 0
    · rw [h2, mul_zero]
    exfalso
    have a1 := GlobalTheory.CuspFrom.freqNonneg _ hE hPs ξ hξ ν x hx h1
    have a2 := GlobalTheory.CuspFrom.freqNonneg _ hE hQ ξ hξ (0 - ν) x hx h2
    have hν : ν = 0 := funext fun τ => le_antisymm (by have := a2 τ; simp at this; exact this) (a1 τ)
    subst hν
    exact h1 (hP.2 ξ hξ x hx)
  simp only [hz] at hm
  exact hm.unique hasSum_zero

set_option maxHeartbeats 800000 in

theorem pow_mul_mem_cusp : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
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
