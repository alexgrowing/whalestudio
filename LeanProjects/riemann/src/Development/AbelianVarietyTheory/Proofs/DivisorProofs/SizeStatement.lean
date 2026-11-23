import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentMetricFromSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialLogGrowthBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialMinusSmallMultiplePsh
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic

namespace GlobalTheory.HomWtBd

theorem levi_two_mul {ι : Type} [Fintype ι] {f : (ι → ℂ) → ℝ} {z : ι → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (w : ι → ℂ) : levi (fun y => 2 * f y) z w = 2 * levi f z w := by
  have h := levi_add_smul (f := fun _ => (0 : ℝ)) (g := f) 2 contDiffAt_const hf w
  have h0 : levi (fun _ : ι → ℂ => (0 : ℝ)) z w = 0 := by simp [levi]
  simpa [h0] using h

theorem bddAbove_of_ext (hE : Extension) {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (A : FinHolAtlas e X) (Z : Set X) (hZc : IsClosed Z) (r : X → ℝ) (L : LocPot X) (s : X → X → ℂ)
    (hB : IsBdSec A Z r L s) {n : ℕ} (W : Fin n → Set X) (hW : IsSNC A L s (fun _ => 1) W) (Θ : LocPot X)
    (hΘ : IsPotential A Θ) (f : X → ℝ) (hf : A.SmoothOn Zᶜ f) (hpsh : PshOff A Z (Θ + LocPot.ofFun f)) (K : ℝ)
    (hK : ∀ x, x ∉ Z → f x ≤ K * Real.log (r x)) : ∃ B : ℝ, ∀ x, x ∉ Z → f x ≤ B := by
  obtain ⟨hL, hs, hn, hZ, -, hr⟩ := hB
  subst hZ
  have hbd : IsBoundary A L s W := by
    refine ⟨hL, hs, hW, fun y => ?_⟩
    by_contra h
    push_neg at h
    have := Real.log_pos h
    have := hn y
    unfold logNormSec at this
    linarith
  have hsm : A.SmoothOn (opn s) (fun y => 2 * f y) := fun j => contDiffOn_const.mul (hf j)
  have hnn : SumNonnegOn A Θ (fun y => 2 * f y) (opn s) := by
    intro x j z hz w
    obtain ⟨hzt, hzx, hzs⟩ := hz
    set c := A.chart j
    have hzZ : c.symm z ∉ P.bdry s := hzs
    have hp := hpsh j z hzt hzZ w
    have hopen : ∀ {U : Set X}, IsOpen U → c.symm z ∈ U → c.target ∩ c.symm ⁻¹' U ∈ nhds z := fun hU hzU =>
      (c.isOpen_inter_preimage_symm hU).mem_nhds ⟨hzt, hzU⟩
    have hΘx : ContDiffAt ℝ 2 (Θ.φ x ∘ c.symm) z :=
      ((hΘ.1 x j).contDiffAt (hopen (Θ.isOpen_U x) hzx)).of_le (WithTop.coe_le_coe.2 le_top)
    have hΘp : ContDiffAt ℝ 2 (Θ.φ (c.symm z) ∘ c.symm) z :=
      ((hΘ.1 (c.symm z) j).contDiffAt (hopen (Θ.isOpen_U _) (Θ.mem_U _))).of_le (WithTop.coe_le_coe.2 le_top)
    have hfz : ContDiffAt ℝ 2 (f ∘ c.symm) z :=
      ((hf j).contDiffAt (hopen hZc.isOpen_compl hzZ)).of_le (WithTop.coe_le_coe.2 le_top)
    have e1 : leviSum A Θ (fun y => 2 * f y) x j z w = 2 * levi (Θ.φ x ∘ c.symm) z w + 2 * levi (f ∘ c.symm) z w := by
      unfold leviSum
      have := levi_add_smul (f := fun y => 2 * (Θ.φ x ∘ c.symm) y) (g := f ∘ c.symm) 2
        (contDiffAt_const.mul hΘx) hfz w
      rw [levi_two_mul hΘx] at this
      exact this
    have e2 : leviAt A (Θ + LocPot.ofFun f) j z w = levi (Θ.φ (c.symm z) ∘ c.symm) z w + levi (f ∘ c.symm) z w := by
      unfold leviAt
      have := levi_add_smul (f := Θ.φ (c.symm z) ∘ c.symm) (g := f ∘ c.symm) 1 hΘp hfz w
      simp only [one_mul] at this
      exact this
    have e3 := GlobalTheory.PosDom.levi_base_change A Θ hΘ x (c.symm z) j z hzt hzx (Θ.mem_U _) w
    rw [e1]
    rw [e2, ← e3] at hp
    linarith
  have hgr : ∀ y ∈ opn s, 2 * f y ≤ 2 * K * Real.log (rad L s y) := by
    intro y hy
    have h1 := hK y hy
    rw [hr y hy] at h1
    have : rad L s y = P.rW L s y := rfl
    rw [this]
    linarith
  obtain ⟨⟨M, hM⟩, -, -⟩ := hE e X A L s n W hbd Θ (fun y => 2 * f y) (2 * K) hΘ hsm hnn hgr
  exact ⟨M / 2, fun x hx => by have := hM x hx; linarith⟩

end GlobalTheory.HomWtBd

namespace GlobalTheory.HomWtBd

open GlobalTheory.ShFam

theorem mul_le_abs_of_norm_le {V : Type} [SeminormedAddCommGroup V] (C : ℝ) {u : V} (hu : ‖u‖ ≤ 1) :
    C * ‖u‖ ≤ |C| := by
  rcases le_or_gt 0 C with h | h
  · rw [abs_of_nonneg h]; exact mul_le_of_le_one_right h hu
  · rw [abs_of_neg h]; nlinarith [norm_nonneg u]

theorem dom_fund {D : D7} {N : ℕ} (τ : D.what₂.Tau) (i : Fin N) : GlobalTheory.FlagPoly.Dom (fund τ i) := by
  intro τ' a b hab
  unfold fund
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact absurd ⟨h₁.1, hab.trans h₁.2⟩ h₂
  · exact zero_le_one
  · exact le_rfl

theorem norm_fund_le {D : D7} {N : ℕ} (τ : D.what₂.Tau) (i : Fin N) : ‖fund τ i‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ' => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => by
    unfold fund
    split_ifs <;> simp

theorem sizeSt : Hypotheses2 → HypothesesH → SizeSt := by
  intro h1 h2 D O x P hC hf hR
  obtain ⟨A, T, H, ⟨R⟩⟩ := hR
  have hCore : O.Core := ⟨x, P, hC⟩
  have key : ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N), ∃ G : ℝ, 0 ≤ G ∧
      ∀ y ∈ offBd O.Φ c σ, -(G * Real.log (O.met.r c σ y)) ≤ psi O x c σ τ i y ∧ psi O x c σ τ i y ≤ G := by
    intro c σ τ i
    obtain ⟨C₁, hC₁⟩ := GlobalTheory.HodgeLogBd.abs_ph_le_log h1 h2 D O hCore hf A T H R c
    obtain ⟨-, hsm, hpsh, C₂, hC₂⟩ := (GlobalTheory.T.fibre_size_and_range_bound h1 h2 D O hCore hf A T H R c).1
    obtain ⟨a, rfl⟩ := (R.man c).ε.surjective σ
    have hnorm := norm_fund_le (D := D) τ i
    have hre : ∀ z, z ∉ (T.M c).Z a → 0 ≤ Real.log ((T.M c).r a z) := fun z hz =>
      Real.log_nonneg (by linarith [Real.add_one_le_exp 1, ((T.M c).bd a).2.2.2.2.2.1 z hz])
    obtain ⟨-, L, s, hB, n, W, hW⟩ := GlobalTheory.T.component_metric_from_section D O hCore A T H R c a
    obtain ⟨B, hBd⟩ := bddAbove_of_ext GlobalTheory.T.extension_statement ((T.M c).A a) ((T.M c).Z a) ((T.M c).bd a).1 ((T.M c).r a) L s hB
      W hW ((T.F c).th (fund τ i) a) (T.th_pot c _ a) ((T.F c).ph (fund τ i) a) (hsm _ a) (hpsh _ (dom_fund τ i) a)
      |C₂| fun z hz => by
        have l := (hC₂ (fund τ i) a z hz).1
        have l' := (abs_le.1 l).2
        have hz0 := hre z hz
        have : C₂ * ‖fund τ i‖ ≤ |C₂| := mul_le_abs_of_norm_le C₂ hnorm
        calc (T.F c).ph (fund τ i) a z ≤ C₂ * ‖fund τ i‖ * Real.log ((T.M c).r a z) := l.trans' (le_abs_self _)
          _ ≤ |C₂| * Real.log ((T.M c).r a z) := mul_le_mul_of_nonneg_right this hz0
    refine ⟨2 * |C₁| + 2 * |B|, by positivity, fun y hy => ?_⟩
    set z := ((R.man c).pt a).symm y with hzdef
    have hyz : (R.man c).pt a z = y := Homeomorph.apply_symm_apply _ _
    have hz : z ∉ (T.M c).Z a := by
      rw [(R.an c).Z a z, hyz]
      exact hy
    have hph : (T.F c).ph (fund τ i) a z = O.chg c none (fund τ i) _ y := by
      have := (R.an c).ph (fund τ i) a z hz
      rw [hyz] at this
      exact this
    have hr : (T.M c).r a z = O.met.r c _ y := by
      rw [(R.an c).r a z hz, hyz]
    have hpsi : psi O x c ((R.man c).ε a) τ i y = 2 * (T.F c).ph (fund τ i) a z := by
      rw [hph]
      exact (hC.two_mul_chg c _ _ y).symm
    have hz0 := hre z hz
    have k1 : |(T.F c).ph (fund τ i) a z| ≤ |C₁| * Real.log ((T.M c).r a z) :=
      (hC₁ _ a z hz).trans (mul_le_mul_of_nonneg_right (mul_le_abs_of_norm_le C₁ hnorm) hz0)
    have l1 := abs_le.1 k1
    have l4 := hBd z hz
    have hB0 : 0 ≤ |B| * Real.log ((T.M c).r a z) := mul_nonneg (abs_nonneg _) hz0
    rw [hpsi, ← hr]
    constructor
    · linarith [l1.1, hB0]
    · linarith [l4, le_abs_self B, abs_nonneg C₁]
  choose G hG0 hG using key
  refine ⟨∑ k : O.s.Comp × (D.what₂.LL →+* ℂ) × D.what₂.Tau × Fin O.N, G k.1 k.2.1 k.2.2.1 k.2.2.2,
    Finset.sum_nonneg fun _ _ => hG0 _ _ _ _, fun c σ τ i y hy => ?_⟩
  have hle : G c σ τ i ≤ ∑ k : O.s.Comp × (D.what₂.LL →+* ℂ) × D.what₂.Tau × Fin O.N, G k.1 k.2.1 k.2.2.1 k.2.2.2 :=
    Finset.single_le_sum (f := fun k : O.s.Comp × (D.what₂.LL →+* ℂ) × D.what₂.Tau × Fin O.N => G k.1 k.2.1 k.2.2.1 k.2.2.2)
      (fun k _ => hG0 _ _ _ _) (Finset.mem_univ (c, σ, τ, i))
  have hlog : 0 ≤ Real.log (O.met.r c σ y) :=
    Real.log_nonneg (by linarith [Real.add_one_le_exp 1, hCore.exp_le_r c σ y])
  obtain ⟨l, u⟩ := hG c σ τ i y hy
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_right hle hlog], u.trans hle⟩

end GlobalTheory.HomWtBd
