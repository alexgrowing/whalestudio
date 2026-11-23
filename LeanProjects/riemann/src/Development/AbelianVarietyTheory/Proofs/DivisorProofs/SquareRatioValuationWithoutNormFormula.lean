import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSqStOfClaims
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteThetaPairNormNeZeroOfCoordNeZeroStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqNoSmall

theorem oneSqSt_of_claims' : (∀ D, GlobalTheory.NormSum.Inp D) → LNe → TorEx → BotSmall → BotExT → NormBig → BotNe → TriEx → Tower → BotConst → Refl → RhoLow → OneSqSt := by
  intro hInp h1 h2 h3 h4 h5 h5' h6 h7 h8 h9 h10
  obtain ⟨c, hc⟩ := Model.gBig_and h1 (Model.gBig_and h2 (Model.gBig_and h3 (Model.gBig_and h4 (Model.gBig_and h5
    (Model.gBig_and h5' (Model.gBig_and h6 (Model.gBig_and h7 (Model.gBig_and h8 (Model.gBig_and h9 h10)))))))))
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ₀ hL G => ?_⟩
  obtain ⟨H1, H2, H3, H4, H5, H5', H6, H7, H8, H9, H10⟩ := h C hC D large₂ a b r T Lc μ₀ hL G
  clear h hc h1 h2 h3 h4 h5 h5' h6 h7 h8 h9 h10
  intro W S ρ hstd hnum C' μ rq zA zA' zT zTd gT ch N0 Sd Se dl Bw hThA hSq w ij

  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := Model.tower_numbers ij.1 ij.2

  have hN0 : ∀ s : ℤ, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) → ∀ l ∈ Sd, 0 ≤ N0 ij s l := by
    intro s h1 h2 l hl
    obtain ⟨z, -, hz⟩ := (hSq.inside ij s.toNat (by omega) (by omega)).2
    have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
    rw [e] at hz
    rw [hz l ((hSq.den l).1 hl).1]
    positivity
  have hdl : 0 ≤ dl w := by
    obtain ⟨S', del, hE, -, -, e⟩ := hSq.int
    rw [e]; exact wt_nonneg w fun l _ => hE.2.1 l
  have hEr : 0 ≤ wt Se (fun l => 1 / (l : ℝ) ^ 2) w := wt_nonneg w fun l _ => by positivity
  have hlast : 0 ≤ ((D.R.m - 1 - ij.2 : ℕ) : ℝ) * (2 * ∑ q ∈ G.pl.S0, (condExp G.pl q : ℝ) *
      (vw w (Ideal.absNorm q.asIdeal : D.what₂.LL) : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (sum_nonneg fun q _ =>
      mul_nonneg (Nat.cast_nonneg _) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w _)))
  by_cases hne : μ w = μ₀
  · rw [hne, hSq.rq_base ij, Formalism.DivisionValues.ValuationRepresentative.vw_one]
    refine ⟨one_ne_zero, ?_⟩
    have s1 : 0 ≤ ∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|) := sum_nonneg fun _ _ => by positivity
    have s2 : 0 ≤ ∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), wt Sd (N0 ij s) w := sum_nonneg fun s hs => by
      rw [mem_Icc] at hs; exact wt_nonneg w (hN0 s hs.1 hs.2)
    have s3 := mul_nonneg (Nat.cast_nonneg (2 * halfRank D ij.1 ij.2)) hEr
    rw [Int.cast_zero]
    have a1 := abs_nonneg (vw w (zA ij) : ℝ)
    have a2 := abs_nonneg (vw w (zA' ij) : ℝ)
    linarith

  · set t := μ w with ht
    obtain ⟨hQn, hThl⟩ := hThA w hne
    obtain ⟨l, hl, hlw⟩ := exists_prime_mem' w
    obtain ⟨HL1, HL2⟩ := H1 ij.1 ij.2
    obtain ⟨Λ, hΛ, hΛne⟩ := HL1 t
    obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := HL1 μ₀
    obtain ⟨Λd, hΛd, hΛdne⟩ := HL2 (some (ch w))
    have hΛd' : IsHeckeL (nuH G μ₀ ij.1 ij.2 * Lc.C.delAt l) Λd := by
      rw [← hSq.delOf_ch hl hlw]; exact hΛd
    have hTd : ∀ s : ℕ, 1 ≤ s → s ≤ halfRank D ij.1 ij.2 →
        D.what₂.embLL (zTd ij (ch w) s) * Λ₀ s = Λd s ∧ Λd s ≠ 0 := by
      intro s h1' h2'
      obtain ⟨x, hx, hx0, hxc, -⟩ := (hSq.inside ij s h1' h2').1
      obtain ⟨y, hy, hy0, hyΛ, -⟩ := H2 ij.1 ij.2 s h1' h2' none
      obtain ⟨y', hy', hy'0, hy'Λ, -⟩ := H2 ij.1 ij.2 s h1' h2' (some (ch w))
      have e1 : x = y := hx.2.unique hy.2
      have e2 : D.what₂.embLL (zTd ij (ch w) s) * x = y' := (hxc (ch w)).2.unique hy'.2
      rw [← hyΛ Λ₀ hΛ₀, ← hy'Λ Λd hΛd, ← e1]
      exact ⟨e2, e2 ▸ hy'0⟩
    have hzψ : ∀ s : ℤ, ∃ z : D.what₂.LL, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) →
        D.what₂.embLL z * Λ₀ s = Λ s := by
      intro s
      by_cases hs : 1 ≤ s ∧ s ≤ (halfRank D ij.1 ij.2 : ℤ)
      · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        have h0 : Λ₀ s ≠ 0 := hΛ₀ne s (by omega) hs.2
        obtain ⟨z, hz⟩ := hnum.ratios ij.1 ij.2 t Λ Λ₀ hΛ hΛ₀ s.toNat (by omega) (by omega) (by rw [e]; exact h0)
        refine ⟨z, fun _ _ => ?_⟩
        rw [hz, e, div_mul_cancel₀ _ h0]
      · exact ⟨0, fun h1' h2' => absurd ⟨h1', h2'⟩ hs⟩
    choose zψ hzψ using hzψ
    have hEp : ∀ s : ℤ, ∃ E : D.what₂.LL, 1 - (e0 D ij.1 ij.2 : ℤ) ≤ s → s ≤ 0 →
        GlobalTheory.Square.IsAwayUnit (Qn G t) E ∧
          Λ s * Λ₀ ((1 - s : ℤ) : ℂ) = D.what₂.embLL E * (Λ ((1 - s : ℤ) : ℂ) * Λ₀ s) := by
      intro s
      by_cases hs : 1 - (e0 D ij.1 ij.2 : ℤ) ≤ s ∧ s ≤ 0
      · obtain ⟨E, hE⟩ := H9 W S hnum ij.1 ij.2 t Λ Λ₀ hΛ hΛ₀ s hs.1 hs.2
        exact ⟨E, fun _ _ => hE⟩
      · exact ⟨0, fun h1' h2' => absurd ⟨h1', h2'⟩ hs⟩
    choose Ep hEp using hEp
    have hwSd : ∀ s, wt Sd (N0 ij s) w = N0 ij s l * (vw w (l : D.what₂.LL) : ℝ) :=
      fun s => wt_at w (fun l' hl' => ((hSq.den l').1 hl').1) hl hlw fun h => by
        by_contra h'; exact h ((hSq.den l).2 ⟨hl, ij, s, h'⟩)
    have hwSe : wt Se (fun l => 1 / (l : ℝ) ^ 2) w = 1 / (l : ℝ) ^ 2 * (vw w (l : D.what₂.LL) : ℝ) :=
      wt_at w (fun l' hl' => ((hSq.err l').1 hl').1) hl hlw fun h => absurd ((hSq.err l).2 ⟨hl, w, hne, hlw⟩) h
    have hmid : ∀ s : ℤ, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) → zT ij s ≠ 0 ∧ zTd ij (ch w) s ≠ 0 ∧
        D.what₂.embLL (zψ s) * Λ₀ s = D.what₂.embLL (zT ij s) * Λ s ∧
        -(wt Sd (N0 ij s) w) ≤ ((vw w (zψ s) + gT ij s w : ℤ) : ℝ) ∧
        (vw w (zψ s) : ℝ) ≤ (vw w (zTd ij (ch w) s) : ℝ) + wt Se (fun l => 1 / (l : ℝ) ^ 2) w := by
      intro s h1' h2'
      have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
      have eC : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by rw [← Int.cast_natCast, e]
      obtain ⟨hTd1, hTd2⟩ := hTd s.toNat (by omega) (by omega)
      rw [eC, e] at hTd1
      rw [eC] at hTd2
      have hψ := hzψ s h1' h2'
      have hTd0 : zTd ij (ch w) s ≠ 0 := fun h0 => hTd2 (by rw [← hTd1, h0, map_zero, zero_mul])
      have hψ0 : zψ s ≠ 0 := fun h0 => hΛne s (by omega) h2' (by rw [← hψ, h0, map_zero, zero_mul])
      refine ⟨by rw [hSq.base]; exact one_ne_zero, hTd0, by rw [hSq.base, map_one, one_mul]; exact hψ, ?_, ?_⟩
      · have hin := hSq.inside ij s.toNat (by omega) (by omega)
        have := H10 ij.1 ij.2 s.toNat (by omega) (by omega) t Λ Λ₀ (zψ s) _ _ _ hΛ hΛ₀ (by rw [eC]; exact hψ)
          hin.1 hin.2 w l hl hlw hQn
        rw [e] at this
        rw [hwSd]; exact this
      · have hz := hThl l hl hlw ij.1 ij.2 s.toNat Λ Λd (zψ s / zTd ij (ch w) s) (by omega) (by omega) hΛ hΛd' (by
          rw [eC, ← hTd1, ← hψ, map_div₀]; field_simp [(map_ne_zero _).2 hTd0])
        have hv := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (zψ s / zTd ij (ch w) s) (zTd ij (ch w) s) (div_ne_zero hψ0 hTd0) hTd0
        rw [div_mul_cancel₀ _ hTd0] at hv
        rw [hwSe, hv]
        have : (vw w (l : D.what₂.LL) : ℝ) / (l : ℝ) ^ 2 = 1 / (l : ℝ) ^ 2 * (vw w (l : D.what₂.LL) : ℝ) := by ring
        push_cast
        linarith
    obtain ⟨rr, hr1, hr2, hr3⟩ := GlobalTheory.Square.Ratio.exists_ratios D.what₂.LL D.what₂.embLL w (Qn G t) hQn
      (e0 D ij.1 ij.2) (halfRank D ij.1 ij.2) (by omega) (fun s => Λ₀ s) (fun s => Λ s) (zT ij) (zTd ij (ch w)) zψ Ep
      (fun s => gT ij s w) (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w)
      (fun s h1' h2' => ⟨hΛ₀ne s h1' h2', hΛne s h1' h2'⟩) hmid (fun s h1' h2' => hEp s h1' h2')

    have hrat : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D ij.1 ij.2 → Λ (n : ℂ) / Λ₀ (n : ℂ) = D.what₂.embLL (rr n) := by
      intro n h1' h2'
      have := (hr1 n (by omega) (by omega)).2
      have h0 := hΛ₀ne n (by omega) (by omega)
      simp only [Int.cast_natCast] at this h0
      rw [← this, mul_div_cancel_right₀ _ h0]
    obtain ⟨cf, hcf0, hcf⟩ := hSq.ratio ij
    obtain ⟨sn, sc, hrq⟩ := hcf t (Or.inr ⟨w, ht.symm⟩)
    obtain ⟨sn₀, sc₀, -⟩ := hcf μ₀ (Or.inl rfl)
    obtain ⟨A₁, A₁', WW, X, c0, hX, hXc⟩ := H6 W hstd ij.1 ij.2
    obtain ⟨u, hu, ζ, hζ, hT⟩ := H7 W S ρ hstd hnum ij.1 ij.2 t (cf t) (cf μ₀) A₁ A₁' WW X c0 Λ Λ₀ sn sc sn₀ sc₀ hX hXc
      hΛ hΛ₀
    obtain ⟨δ, t0, hN⟩ := hSq.norms
    obtain ⟨P₀, P₀', hB₀, hzA, hzA'⟩ := hN ij
    obtain ⟨P, P', hB⟩ := H4 δ t0 (levQ G.pl) P₀ t ij.1 ij.2
    have hmod : modT G μ₀ = SqNum.condE G.pl := (Model.base_tuple G hL).2.2
    have hB₀' : IsBottom G μ₀ ij.1 ij.2 (modT G μ₀) P₀ P₀' := by rw [hmod]; exact hB₀
    obtain ⟨A, hA, hNA⟩ := H5 δ t0 ij.1 ij.2
    have eP := hNA t _ P P' Λ hB hΛ
    have eP₀ := hNA μ₀ _ P₀ P₀' Λ₀ hB₀' hΛ₀
    have hIcc : ∀ s ∈ Icc (1 - (e0 D ij.1 ij.2 : ℤ)) (h0 D ij.1 ij.2 : ℤ),
        1 - (e0 D ij.1 ij.2 : ℤ) ≤ s ∧ s ≤ (halfRank D ij.1 ij.2 : ℤ) := fun s hs => by
      rw [mem_Icc] at hs; omega
    set z : D.what₂.LL := zA ij * ∏ s ∈ Icc (1 - (e0 D ij.1 ij.2 : ℤ)) (h0 D ij.1 ij.2 : ℤ), rr s with hzdef
    have hz : D.what₂.embLL z = (P.norm : ℂ) := by
      rw [eP, hzdef, map_mul, hzA, eP₀, map_prod, mul_assoc, ← prod_mul_distrib]
      congr 1
      refine prod_congr rfl fun s hs => ?_
      obtain ⟨a1, a2⟩ := hIcc s hs
      rw [mul_comm]; exact (hr1 s a1 a2).2
    have hzne : z ≠ 0 := by
      intro h0
      have : (P.norm : ℂ) = 0 := by rw [← hz, h0, map_zero]
      rw [eP] at this
      refine mul_ne_zero hA (prod_ne_zero_iff.2 fun s hs => ?_) this
      obtain ⟨a1, a2⟩ := hIcc s hs
      exact hΛne s a1 a2
    have hzAne : zA ij ≠ 0 := by
      intro h0
      have : (P₀.norm : ℂ) = 0 := by rw [← hzA, h0, map_zero]
      rw [eP₀] at this
      refine mul_ne_zero hA (prod_ne_zero_iff.2 fun s hs => ?_) this
      obtain ⟨a1, a2⟩ := hIcc s hs
      exact hΛ₀ne s a1 a2
    have hz'ne : zA' ij ≠ 0 := by
      intro h0
      have hne' : P₀'.norm ≠ 0 := GlobalTheory.T.definiteThetaPair_norm_ne_zero_of_coord_ne_zero D (hInp D) δ t0 (levQ G.pl) P₀' (H5' δ t0 (levQ G.pl) P₀ P₀' ij.1 ij.2 hB₀).2
      have : (P₀'.norm : ℂ) = 0 := by rw [← hzA', h0, map_zero]
      exact hne' (by exact_mod_cast this)
    obtain ⟨γ, hγ0, hc00, hγc, hγv⟩ := H8 W S hstd hnum ij.1 ij.2 t A₁ A₁' WW X c0 δ t0 P₀ P₀' P P' z (zA' ij) C' dl
      hX hXc hB₀ hB hz hzA' hzne hz'ne hSq.int
    have hS0 : ∀ v ∈ G.pl.S0, 0 < Ideal.absNorm v.asIdeal := fun v _ =>
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    have htk := fun k => GlobalTheory.Square.stepRatio_vw_bound D.what₂.LL D.what₂.embLL w (Qn G t) hQn _ G.pl.S0
      (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) hS0 (u k) 1 (hu k)
    choose tk htk0 htku htkv using htk
    obtain ⟨hζ0, hζv⟩ := hζ.ne_zero_and_vw w hQn

    have hq' : ∏ k ∈ range (qq D ij.2), Λ ((eTop D ij.1 ij.2 + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D ij.1 ij.2 + k + 1 : ℕ) : ℂ) =
        D.what₂.embLL (∏ k ∈ range (qq D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + k + 1)) := by
      rw [map_prod]
      refine prod_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [hrat _ (by omega) (by omega)]
      push_cast; rfl
    have hp' : ∏ k ∈ range (pp D ij.2), Λ ((eTop D ij.1 ij.2 + qq D ij.2 - k : ℕ) : ℂ) /
        Λ₀ ((eTop D ij.1 ij.2 + qq D ij.2 - k : ℕ) : ℂ) =
        D.what₂.embLL (∏ k ∈ range (pp D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + qq D ij.2 - k)) := by
      rw [map_prod]
      refine prod_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [hrat _ (by omega) (by omega)]
      rw [Nat.cast_sub (by omega)]
      push_cast; rfl
    have hc0 : cf μ₀ ≠ 0 := hcf0
    have e1 : cf t / cf μ₀ = D.what₂.embLL (rq t ij) := by rw [← hrq, mul_div_cancel_right₀ _ hc0]
    have e2 : c0 t / c0 μ₀ = D.what₂.embLL γ := by rw [← hγc, mul_div_cancel_right₀ _ hc00]
    have e3 : ∏ k, u k = D.what₂.embLL (∏ k, tk k) := by
      rw [map_prod]; exact prod_congr rfl fun k _ => by rw [htku k, mul_one]
    rw [e1, e2, e3, hq', hp'] at hT
    have heqLL : rq t ij * ∏ k ∈ range (qq D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + k + 1) =
        ζ * (∏ k, tk k) * γ * ∏ k ∈ range (pp D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + qq D ij.2 - k) := by
      apply D.what₂.embLL.injective
      simp only [map_mul]
      exact hT
    have key := vw_ratio_le w (eTop D ij.1 ij.2) (pp D ij.2) (qq D ij.2) (e0 D ij.1 ij.2) (h0 D ij.1 ij.2) n1 n5.le
      (rq t ij) ζ γ (zA ij) (zA' ij) tk rr
      (fun s => |((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| + |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)
      (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w) (dl w)
      (2 * ∑ v ∈ G.pl.S0, (condExp G.pl v : ℝ) * (vw w (Ideal.absNorm v.asIdeal : D.what₂.LL) : ℝ))
      heqLL (fun s h1' h2' => (hr1 s h1' (by rw [n2]; push_cast; omega)).1) ⟨hζ0, hζv⟩ (fun k => ⟨htk0 k, htkv k⟩)
      hγ0 hzAne (hγv w hQn) hEr (fun s h1' h2' => by
        have h2'' : s ≤ (halfRank D ij.1 ij.2 : ℤ) := by rw [n2]; push_cast; omega
        obtain ⟨b1, b2⟩ := hr2 s h1' h2''
        refine ⟨by positivity, wt_nonneg w (hN0 s h1' h2''), b1, ?_⟩
        have := abs_nonneg ((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)
        linarith) hr3
    rw [n2, ← n3]
    exact key

end GlobalTheory.SqTop.OneSqNoSmall

end
