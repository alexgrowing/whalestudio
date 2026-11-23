import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalMultipleOfGloballyKltStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtOfIsNkltCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuCutLowerCentreDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleEffectiveKltInductionStartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.PairStep

theorem exists_lcCut_induction : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∃ A : CartierDiv X, IsAmpleLB (toLB A) ∧ ∀ j, j < n → ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j' := by
  intro hPr X _ _ _ p n hP hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hZ
  obtain ⟨m, G, hm, hG⟩ := GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt X p n hP hn Δ hΔ hklt
  have hcpos : ∀ e, 1 ≤ e → e ≤ n → 0 < c e := fun e h1 h2 => hc e (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hgen : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hdimX : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [hgen, ← hn]
    exact ((Homeomorph.Set.univ X).isHomeomorph).topologicalKrullDim_eq
  have hcn := hZ (Closeds.closure ({genericPoint X} : Set X)) n isIrreducible_singleton.closure
    (by simpa using specializes_iff_mem_closure.1 (genericPoint_specializes x)) hn1 hdimX
  obtain ⟨c', hc'v, hc'gt⟩ : ∃ c' : ℝ, c' ^ n < (interNumRed ℂ (Closeds.closure ({genericPoint X} : Set X))
      (fun _ : Fin n => N₀) : ℝ) / (r : ℝ) ^ n ∧ c n < c' := by
    have hev := ((continuous_pow n).tendsto (c n)).eventually_lt_const hcn
    exact ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (c n) ∈ nhdsWithin (c n) (Set.Ioi (c n)))).exists
  have hcn0 := hcpos n hn1 le_rfl
  have hc'0 : 0 < c' := hcn0.trans hc'gt
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : (n : ℝ) / c' < n / c n := div_lt_div_of_pos_left hnpos hcn0 hc'gt
  obtain ⟨β, hβ0, hβ⟩ := exists_rat_btwn (sub_pos.2 hlt)
  have hβ0' : (0 : ℚ) < β := by exact_mod_cast hβ0
  obtain ⟨A, F, a, hA, ha, hF, lam₀, μ₀, m₀, D₀, hm₀, hD₀, hμ₀, hlam₀, hnum₀, hklt₀⟩ :=
    GlobalTheory.T.exists_ample_effective_klt_inductionStart hPr X p n hP hn Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ0'
  refine ⟨A, hA, ?_⟩
  have key : ∀ a : WithBot ℕ∞, ∀ j : ℕ, (j : WithBot ℕ∞) < a → a ≤ ((j + 1 : ℕ) : WithBot ℕ∞) →
      a = ((j + 1 : ℕ) : WithBot ℕ∞) := by
    intro a j h1 h2
    induction a using WithBot.recBotCoe with
    | bot => simp at h1
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((j + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h2
        exact absurd (WithBot.coe_le_coe.1 h3) (by simp)
      | coe k =>
        have h1' : j < k := by exact_mod_cast h1
        have h2' : k ≤ j + 1 := by exact_mod_cast h2
        have : k = j + 1 := by omega
        subst this; rfl
  have hsplit : ∀ j, j + 1 ≤ n → ∑ e ∈ Finset.Icc (j + 1) n, (e : ℝ) / c e =
      (j + 1 : ℕ) / c (j + 1) + ∑ e ∈ Finset.Icc (j + 2) n, (e : ℝ) / c e := by
    intro j hj
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hj, Finset.sum_insert (by simp)]
    first | rfl | (push_cast; ring_nf) | simp [add_assoc]
  let S : ℕ → Prop := fun j => ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j'
  have first : S (n - 1) := by
    obtain ⟨lam₁, μ₁, m₁, D₁, hm₁, hD₁, hμ₁, hlam₁, hnum₁, hcut₁⟩ :=
      GlobalTheory.T.angehrnSiu_cut_lower_centre_dimension hPr X p n hP hn Δ m G r N₀ hN₀ A F a x (genericPoint X) n c' lam₀ μ₀ m₀ D₀ hΔ hklt hm hG hr
        hnef hA ha hF hx (genericPoint_specializes x) hn1 hdimX (Or.inl rfl) hc'0 hc'v hm₀ hD₀ hμ₀
        hnum₀ (hklt₀ x).lcAt
    refine ⟨n - 1, lam₁, μ₁, m₁, D₁, le_rfl, hm₁, hD₁, hμ₁, ?_, hnum₁, hcut₁⟩
    rw [Nat.sub_add_cancel hn1, Finset.Icc_self, Finset.sum_singleton]
    have : (lam₀ : ℝ) < β := by exact_mod_cast hlam₀
    linarith
  have step : ∀ j, j + 1 < n → S (j + 1) → S j := by
    intro j hj ⟨j', lam, μ, m', D₁, hj', hm', hD₁, hμ, hlam, hnum, hcut⟩
    by_cases hle : j' ≤ j
    · exact ⟨j', lam, μ, m', D₁, hle, hm', hD₁, hμ, hlam, hnum, hcut⟩
    obtain rfl : j' = j + 1 := by omega
    have hsj := hsplit j (by omega)
    have hcj := hcpos (j + 1) (by omega) (by omega)
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) / c (j + 1) := div_pos (by positivity) hcj
    obtain ⟨hlc, hnk, hdim⟩ := hcut
    by_cases hall : ∀ z, z ⤳ x → ¬ KltAt p n (Δ + qWeil D₁ m') z →
        topologicalKrullDim (closure ({z} : Set X)) ≤ j
    · refine ⟨j, lam, μ, m', D₁, le_rfl, hm', hD₁, hμ, ?_, hnum, hlc, hnk, hall⟩
      rw [hsj]; linarith
    push_neg at hall
    obtain ⟨z, hzx, hzk, hzd⟩ := hall
    have hq : IsQCart (qWeil D₁ m') := ⟨m', D₁, hm', hD₁, rfl⟩
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding X p n hP hn Δ (qWeil D₁ m') z hq (hklt z) hzk
    have hwx : w ⤳ x := hwz.trans hzx
    have hwk : ¬ KltAt p n (Δ + qWeil D₁ m') w :=
      GlobalTheory.PairStep.not_kltAt_of_isNkltCentre X p n hP hn _ w w hw specializes_rfl
    have hsub : closure ({z} : Set X) ⊆ closure ({w} : Set X) := specializes_iff_closure_subset.1 hwz
    have hmono : topologicalKrullDim (closure ({z} : Set X)) ≤ topologicalKrullDim (closure ({w} : Set X)) :=
      (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    have hwd : topologicalKrullDim (closure ({w} : Set X)) = ((j + 1 : ℕ) : WithBot ℕ∞) :=
      key _ j (hzd.trans_le hmono) (hdim w hwx hwk)
    have hZw := hZ (Closeds.closure ({w} : Set X)) (j + 1) isIrreducible_singleton.closure
      (by simpa using specializes_iff_mem_closure.1 hwx) (by omega) hwd
    obtain ⟨lam', μ', m'', D₂, hm'', hD₂, hμ', hlam', hnum', hcut'⟩ :=
      GlobalTheory.T.angehrnSiu_cut_lower_centre_dimension hPr X p n hP hn Δ m G r N₀ hN₀ A F a x w (j + 1) (c (j + 1)) lam μ m' D₁ hΔ hklt hm hG hr
        hnef hA ha hF hx hwx (by omega) hwd (Or.inr hw) hcj hZw hm' hD₁ hμ hnum hlc
    refine ⟨j, lam', μ', m'', D₂, le_rfl, hm'', hD₂, hμ', ?_, hnum', by simpa using hcut'⟩
    rw [hsj]
    push_cast at hlam' ⊢
    linarith
  have hall : ∀ i, i < n → S (n - 1 - i) := by
    intro i
    induction i with
    | zero => intro _; simpa using first
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      rw [show n - 1 - i = (n - 1 - (i + 1)) + 1 by omega] at h
      exact step _ (by omega) h
  intro j hj
  have h := hall (n - 1 - j) (by omega)
  rwa [show n - 1 - (n - 1 - j) = j by omega] at h

end GlobalTheory.PairStep
