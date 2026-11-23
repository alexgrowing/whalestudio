import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CostTwoLogBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllNormHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGoodLevelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug.MeanTop

theorem primeFactors_sub (d : ℤ) (M : ℕ) :
    (2 * d * (M : ℤ)).natAbs.primeFactors ⊆ Nat.primeFactors (2 * d.natAbs) ∪ M.primeFactors := by
  have e : (2 * d * (M : ℤ)).natAbs = 2 * d.natAbs * M := by
    simp [Int.natAbs_mul]
  rw [e]
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hp, hd, h0⟩ := hp
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · exact Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hp, h, fun h' => h0 (by rw [h', zero_mul])⟩)
  · exact Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hp, h, fun h' => h0 (by rw [h', mul_zero])⟩)

theorem spread_nonneg {Ψ : Type} [Fintype Ψ] {N : ℕ} (hN : 0 < N) (u : Top.Wt Ψ N) : 0 ≤ Top.spread u := by
  unfold Top.spread
  refine Finset.sum_nonneg fun τ _ => ?_
  have i0 : Fin N := ⟨0, hN⟩
  have h1 := ciInf_le (Set.finite_range (fun i => u τ i)).bddBelow i0
  have h2 := le_ciSup (Set.finite_range (fun i => u τ i)).bddAbove i0
  linarith

theorem errX_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (s : ℝ) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) :
    GlobalTheory.CovHt.errX s u g = (Real.log (GlobalTheory.CovHt.bndB u g) + s) * GlobalTheory.CovHt.l1 u + (Dw.q : ℝ) * Top.spread (reW u) := by
  unfold GlobalTheory.CovHt.errX Top.spread reW
  congr 2
  convert rfl

end GlobalTheory.CompanionTheory.Ar.Plug.MeanTop

namespace GlobalTheory.CompanionTheory.Ar.Plug

open GlobalTheory.CompanionTheory.Ar.Plug.MeanTop in
set_option maxHeartbeats 1000000 in

theorem top_meanAll : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ArithIntersectionSystemStatement → BirationalPullbackPushforwardFormula → Top.GoodTowerExistsX → Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → FnAlgClosed Xo c → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → 2 ≤ Fintype.card (CMType H) → (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → GlobalTheory.CovHt.MeanAll U x (Real.log (hostRd E) + |hostLval H|) C := by
  intro hNef hG hII hG6 hGT hVT
  obtain ⟨II, hII⟩ := hII
  obtain ⟨CT, hCT, hT⟩ := GlobalTheory.T.full_intersection_good_level hG hGT hVT
  refine ⟨CT + 120, by linarith, ?_⟩
  intro E _ _ _ _ H Dw l Xo c r U h e hLaws hUnif hFn hGood hA hq hpq hcardΨ hbad x hx
  classical
  have hqp : Dw.q < Dw.p := by omega
  have hN : 4 ≤ Dw.p + Dw.q := by omega
  have h128 : (128 : ℝ) ≤ 4 * (Fintype.card (CMType H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 := by
    have a : (2 : ℝ) ≤ Fintype.card (CMType H) := by exact_mod_cast hcardΨ
    have b : (4 : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by exact_mod_cast hN
    nlinarith
  have hbadT : (2 * discr E * (l.M' : ℤ)).natAbs.primeFactors.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 :=
    (Finset.card_le_card (primeFactors_sub _ _)).trans hbad
  obtain ⟨Y, T, o, κ, -, hCO, hTbad, hProp, hT1, -, hMS⟩ :=
    hT E H Dw l Xo c II hII hFn hGood hA hq hpq hbadT
  have hj : T.j = Dw.p := o.toTowerOrigin.j_eq
  have hW := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M 0 (Classical.arbitrary T.Comp))
  intro u g hgap
  obtain ⟨-, -, -, -, hl1, -, -, -, hB⟩ := hW u
  obtain ⟨hBeq, hWH⟩ := hB g
  have hWH' : Top.WeightHyp T.j (reW u) g := by rw [hj]; exact hWH hq hqp hgap
  set B := GlobalTheory.CovHt.bndB u g with hBdef
  have hB128 : (128 : ℝ) ≤ B := by
    rw [hBeq]
    unfold Top.bigB0
    have : 0 ≤ ‖reW u‖ / g := div_nonneg (norm_nonneg _) hgap.1.le
    nlinarith
  have hBpos : 0 < B := by linarith
  have hfl128 : 128 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB128)
  have hflt : Top.bigB0 (reW u) g < (⌊B⌋₊ : ℝ) + 1 := by rw [← hBeq]; exact Nat.lt_floor_add_one B
  have hKB : 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 ≤ ⌊B⌋₊ := by
    refine Nat.le_floor ?_
    rw [hBeq]
    unfold Top.bigB0
    have : 0 ≤ ‖reW u‖ / g := div_nonneg (norm_nonneg _) hgap.1.le
    push_cast at h128 ⊢
    nlinarith
  have hTb : T.bad.card ≤ ⌊B⌋₊ := by rw [hTbad]; exact hbadT.trans hKB
  have hM := hMS (reW u) g hWH' ⌊B⌋₊ hfl128 hflt hTb
  have hsl := fun Z => GlobalTheory.T.uniform_all_norm_height_bound hNef hG hG6 E H Dw l Xo c r U h e hLaws hUnif x hx Y T o κ II hCO hII hProp hT1 Z u g B
    hgap.2.1 hWH' (le_of_eq hBeq.symm)
  obtain ⟨hc0, hc⟩ := GlobalTheory.T.cost_two_log_bound E H l B hB128 (hbad.trans hKB)
  refine ⟨fun Z => T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u, hsl, ?_⟩

  have hfin : (∑ᶠ Z, (T.slope II ⌊B⌋₊ (κ Z) (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u)) =
      ∑ c', (T.slope II ⌊B⌋₊ c' (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u) := by
    rw [finsum_comp_equiv κ (f := fun c' => T.slope II ⌊B⌋₊ c' (reW u) - 2 * costTwo l B * GlobalTheory.CovHt.l1 u)]
    exact finsum_eq_sum_of_fintype _
  have hcard : (Nat.card (Comp Xo c) : ℝ) = Fintype.card T.Comp := by
    rw [Nat.card_congr κ, Nat.card_eq_fintype_card]
  have hn : (0 : ℝ) < Fintype.card T.Comp := by exact_mod_cast Fintype.card_pos
  rw [hfin, hcard, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_div,
    mul_div_cancel_left₀ _ hn.ne']
  set S := (∑ c', T.slope II ⌊B⌋₊ c' (reW u)) / (Fintype.card T.Comp : ℝ) with hS
  have hmin : min T.j (Dw.p + Dw.q - T.j) = Dw.q := by rw [hj]; omega
  unfold Top.RootTower.bracket at hM
  rw [hmin, ← hl1] at hM
  have hrd : 0 < hostRd E := by
    unfold hostRd
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero E)) _
  have hfl : (0 : ℝ) < ⌊B⌋₊ := by exact_mod_cast (show 0 < ⌊B⌋₊ by omega)
  have hlog : Top.bigLam ⌊B⌋₊ (hostRd E) (hostLval H) ≤ Real.log B + Real.log (hostRd E) + |hostLval H| := by
    unfold Top.bigLam
    rw [Real.log_mul hfl.ne' hrd.ne']
    have := Real.log_le_log hfl (Nat.floor_le hBpos.le)
    linarith
  have hsp0 := spread_nonneg (by omega) (reW u)
  have hL1 : 0 ≤ GlobalTheory.CovHt.l1 u := by
    unfold GlobalTheory.CovHt.l1
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hq0 : (0 : ℝ) ≤ (Dw.q : ℝ) := Nat.cast_nonneg _
  have a1 := mul_le_mul_of_nonneg_right hlog hL1
  have a2 : 0 ≤ |hostLval H| * GlobalTheory.CovHt.l1 u := mul_nonneg (abs_nonneg _) hL1
  have a3 : 0 ≤ (Dw.q : ℝ) * Top.spread (reW u) := mul_nonneg hq0 hsp0
  have a4 := mul_le_mul_of_nonneg_right hc hL1
  have a5 : CT * (Top.bigLam ⌊B⌋₊ (hostRd E) (hostLval H) * GlobalTheory.CovHt.l1 u + (Dw.q : ℝ) * Top.spread (reW u)) ≤
      CT * ((Real.log B + Real.log (hostRd E) + |hostLval H|) * GlobalTheory.CovHt.l1 u + (Dw.q : ℝ) * Top.spread (reW u)) :=
    mul_le_mul_of_nonneg_left (by linarith) hCT
  have a6 : Real.log B * GlobalTheory.CovHt.l1 u + Real.log (hostRd E) * GlobalTheory.CovHt.l1 u ≤
      (Real.log B + Real.log (hostRd E)) * GlobalTheory.CovHt.l1 u := by ring_nf; rfl
  rw [errX_eq]
  nlinarith

end GlobalTheory.CompanionTheory.Ar.Plug
