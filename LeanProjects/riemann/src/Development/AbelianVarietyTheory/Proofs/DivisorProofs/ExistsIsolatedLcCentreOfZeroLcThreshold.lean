import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalMultipleOfGloballyKltStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogEqnAddSmulIffOfOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSuppStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenKltOffIsolatedLcCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveQDivisorOffPointAmpleClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivToWeilQDivisorAddOfEffectiveStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem GlobalTheory.PairStep.exists_isolated_of_lcCut_zero : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e ≤ 1 →
      ∀ (A : CartierDiv X) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), IsAmpleLB (toLB A) → 0 < m' → D₀.Eff → 0 < μ →
        (lam : ℝ) < ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e →
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) →
        LcCut p n (Δ + qWeil D₀ m') x 0 →
      ∃ (m : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m ∧ D₀.Eff ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C →
          (interNumRed ℂ C ![toLB D₀] : ℚ) / m = interNumRed ℂ C ![N₀] / r) ∧
        x ∈ U ∧ (∀ y ∈ U, LcAt p n (Δ + qWeil D₀ m) y) ∧
        (∀ y ∈ U, y ≠ x → KltAt p n (Δ + qWeil D₀ m) y) ∧ ¬ KltAt p n (Δ + qWeil D₀ m) x := by
  intro hPr X _ _ _ p n hp hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hcZ hsum A lam μ m' D₀ hA hm' hD₀ hμ hlam hnum hcut
  obtain ⟨m, G, hm, hG⟩ := GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt X p n hp hn Δ hΔ hklt
  have hG' := GlobalTheory.isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG
  obtain ⟨U, hxU, hlc, hkl⟩ := GlobalTheory.T.exists_open_klt_off_isolated_lcCentre hPr X p n hp hn (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) x
    (Nat.mul_pos hm hm') hG' hx hcut
  have hlam1 : lam ≤ 1 := by
    have : (lam : ℝ) ≤ 1 := (hlam.trans_le hsum).le
    exact_mod_cast this
  obtain ⟨M, E, hM, hE, hxE, hEnum⟩ := GlobalTheory.T.exists_effective_QDivisor_offPoint_ampleClass X p hp N₀ A x r lam μ hN₀ hnef hA hr hlam1 hμ
  obtain ⟨hD, hqW, hDnum⟩ := GlobalTheory.T.cartierDivToWeilQDivisor_add_of_effective X p hp D₀ E m' M hm' hM hD₀ hE
  have hoff : ∀ y, y ∉ E.supp → Off (qWeil E M) y := fun y hy =>
    (GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X E M y hE hM).2 hy
  have heq : Δ + qWeil (M • D₀ + m' • E) (m' * M) = (Δ + qWeil D₀ m') + (1 : ℚ) • qWeil E M := by
    rw [hqW, one_smul, add_assoc]
  let V : X.Opens := ⟨(E.supp : Set X)ᶜ, E.supp.isClosed.isOpen_compl⟩
  refine ⟨m' * M, M • D₀ + m' • E, U ⊓ V, Nat.mul_pos hm' hM, hD, ?_, ⟨hxU, hxE⟩, ?_, ?_, ?_⟩
  · intro C hC
    have h1 := hDnum C hC
    have h2 := hnum C hC
    have h3 := hEnum C hC
    push_cast at h1 ⊢
    rw [h1, h2, h3]
    ring
  · intro y hy
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).2.1).2 (hlc y hy.1)
  · intro y hy hyx
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).1).2 (hkl y hy.1 hyx)
  · rw [heq]
    exact fun h => hcut.2.1 (((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 x (hoff x hxE)).1).1 h)
