import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

set_option autoImplicit false

namespace GlobalTheory.RunDepth

theorem sprime_nonneg_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ), O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → PiSplit (H := H) Dd → LeafPage O → ∀ v : HeightOneSpectrum (𝓞 K), plc v ∈ O.sm → ∀ j, 0 ≤ DepthTie.s1T Xo c Dd O ι v j := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι hT hpr hσ hsp hPg v hv j
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg1p, hg2p, hq1p, hdp, -, -, -, -, -, -, hg1t, hg2t, -, -, -⟩ := hPg
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpr
  have hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime :=
    ⟨h1 ▸ hg1p, h2 ▸ hg2p, h3 ▸ hq1p, h4 ▸ hdp⟩
  have hn1 : plc v ≠ Dd.Q.g1 := by
    rw [← h1]; exact fun h => hg1t (h ▸ hv)
  have hn2 : plc v ≠ Dd.Q.g2 := by
    rw [← h2]; exact fun h => hg2t (h ▸ hv)
  have hs : DepthTie.sWT Xo c Dd ι v j = (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) := by
    unfold DepthTie.sWT DepthTie.nuT DepthTie.nuWT nuStarAt DepPage.nuN DepthTie.e2
    rw [DepthTie.resChar_below (F := c.F) v, if_neg hn1, if_neg hn2]
    ring
  set N := DepthTie.Nsig Dd.Q (DF (Dw (ι j)) (Dd.aL (ι j))) (DF (Dw (ι j)) (Dd.aF (ι j))) with hNdef
  have hN : N ≠ 0 := DepthTie.Nsig_ne_zero Dd.Q hprime _ _
  have : Fact (plc v).Prime := ⟨plc_prime v⟩
  have hdvd : (plc v) ^ ((Dd.Q.T : ℕ) * Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v)) ∣ N := by
    rw [hNdef]
    unfold DepthTie.Nsig DepPage.Z1
    refine Dvd.dvd.mul_left ?_ _
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ (Nat.le_add_right _ _)).trans
      (Finset.dvd_prod_of_mem (fun p => p ^ ((Dd.Q.T : ℕ) * Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) p + Dd.Q.cP (DF (Dw (ι j)) (Dd.aF (ι j))) p))
        (Finset.mem_filter.2 ⟨h5 ▸ hv, plc_prime v⟩))) _) _
  have hle : ((Dd.Q.T : ℕ) : ℝ) * (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) ≤
      (padicValNat (plc v) N : ℝ) := by
    exact_mod_cast (padicValNat_dvd_iff_le hN).1 hdvd
  have hnn0 : (0 : ℝ) ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) := by
    exact_mod_cast DepthTie.vw_nonneg_of_isIntegral v _ (DepthTie.nnK_isIntegral Dd (ι j))
  have he := ramw_pos v
  unfold DepthTie.s1T
  rw [hs, hσ v j, DepthTie.vw_sig Dd hsp hprime v, add_div, mul_div_cancel_right₀ _ he.ne', hT]
  have : 0 ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) / (ramw v : ℝ) := div_nonneg hnn0 he.le
  linarith

end GlobalTheory.RunDepth
