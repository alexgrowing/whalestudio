import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SprimeNonnegTwo
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ContentZeroAtSmallPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthTwo_of_unscaled_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs) (Nd : NumDatum), (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O → ContentEqualsDatumContent N Nd ι → TiePrimes O Nd → (∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∈ O.sm → ∀ j, ∃ B : ℝ, O.T * B ≤ O.sC j ∧ nuWAt (Xo := Xo (ι j)) (c := c) Dd la (ι j) ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal)) → LeafDepth2 N O := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N Nd hE hσ hT hpr hsp hPg tF tP hB
  have hT0 : (0 : ℝ) ≤ O.T := by rw [hT]; positivity
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), plc v ∈ O.sm →
      (1 ≤ DepthTie.e1 c v ∧ 1 ≤ DepthTie.e2 c v ∧ ramw v = (DepthTie.e1 c v : ℤ) * (DepthTie.e2 c v : ℤ) ∧
        ∀ j, (O.E v j : ℤ) ≤ (DepthTie.e1 c v : ℤ) *
          ⌈(DepthTie.e2 c v : ℝ) * O.T * (DepthTie.nuT Xo c Dd ι v j + if plc v ∈ O.Bad then 1 else 0)⌉) →
      O.e0 v j ≤ O.sC j + O.T + 1 := by
    intro v j hv ⟨he1, he2, hram, hEv⟩
    have hbad : plc v ∈ O.Bad := by simp [OnObj.Bad, hv]
    have hEj := hEv j
    rw [if_pos hbad] at hEj
    have hR := rounding_condition_holds (DepthTie.e1 c v) (DepthTie.e2 c v) (O.T * (DepthTie.nuT Xo c Dd ι v j + 1))
      (O.E v j) he1 he2 (by rw [← mul_assoc]; exact hEj)
    have hramR : (ramw v : ℝ) = (DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ) := by simp [hram]
    have he2R : (1 : ℝ) ≤ DepthTie.e2 c v := by exact_mod_cast he2
    have hinv : 1 / (DepthTie.e2 c v : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact he2R
    have hs1 := GlobalTheory.RunDepth.sprime_nonneg_two E H l Dw Xo c Dd K Bs Df S P oc O ι hT hpr hσ hsp hPg v hv j
    obtain ⟨B, hTB, hν⟩ := hB (placeBelow (K := c.F) v) (by rw [DepthTie.resChar_below (F := c.F) v]; exact hv) j
    have hW : DepthTie.nuWT Xo c Dd ι v j ≤ B := by
      have h0 : (0 : EReal) ≤ nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j) := le_max_left _ _
      have ht := EReal.toReal_le_toReal hν (ne_bot_of_le_ne_bot EReal.zero_ne_bot h0) (EReal.coe_ne_top _)
      rw [EReal.toReal_coe] at ht
      unfold DepthTie.nuWT
      rw [div_le_iff₀ (by linarith), mul_comm]
      exact ht
    have hTW := mul_le_mul_of_nonneg_left hW hT0
    have he0 : O.e0 v j = (O.E v j : ℝ) / ((DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ)) -
        (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) := by
      unfold OnObj.e0
      rw [sub_div, hramR]
    unfold DepthTie.s1T DepthTie.sWT at hs1
    rw [he0]
    nlinarith
  intro w hw h2 j
  obtain ⟨h1, h1'⟩ := DepthTie.tieE Xo c Dd O ι hE hT hpr w hw
  exact ⟨key w j h2 h1, key (conjPl w) j (by rw [plc_conjPl]; exact h2) h1', content_zero_at_small_primes N O Nd ι hPg tF tP w h2 j⟩

end GlobalTheory.RunDepth
