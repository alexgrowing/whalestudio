import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRows
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunDepthDataLawsAndFiniteLocalDepth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceB
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem k_le_sub_one_of_lt (R : Ranks) (l : ℕ) (h : 4 * R.t * R.r + 1 < l) : (R.k : ℝ) ≤ (l : ℝ) - 1 := by
  have h1 : R.k ≤ R.r := by have := R.two_le_m; unfold Ranks.r; omega
  have h2 : 1 ≤ R.t := by have := R.three_m_lt_t; omega
  have h3 : R.r ≤ 4 * R.t * R.r := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : R.k + 1 ≤ l := by omega
  have h5 : ((R.k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast h4
  push_cast at h5
  linarith

theorem leafDepthRam_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthRam N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg hSz hx hb tF
  obtain ⟨hPi, hDep, -⟩ := laws_and_nuFinAt D L Pm Tp hK T EX hM hR.star_eq
  obtain ⟨-, hW⟩ := sizes_le_two_mul D L Pm hx hb
  refine DepthTie.leafDepthRam_core_sat T (depOf T EX Tp hK) O ι N (numOf D L) hPi hM.pins hR.inR hR.E_eq hR.σ_eq
    hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.star_eq (fun j => hDep.chartEx _ (hR.inR j)) hPg hSz tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ⟨?_, hR.k_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) 1 ?_ ?_ ?_ ?_
  · rw [hR.f_eq]
    show ((2 * D.R.n : ℕ) : ℝ) = 2 * ((D.R.n : ℕ) : ℝ)
    push_cast
    ring
  · intro j
    have h1 := (GlobalTheory.WeightExponents.weight_exponents D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (mul_rows_lR_le_kaR D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    show O.T * ((DF (T.Q.Dw (ι j)) (wtA (lR Tp hK (ι j))) : ℕ) : ℝ) ≤ (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)
    rw [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h1 := (DF_kaR_le D L Pm Tp hK hx hb (ι j) (hR.inR j)).1
    unfold OnObj.sB OnObj.Se
    rw [one_mul, hR.k_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
    exact h1
  · unfold PageRam
    rw [one_mul, hR.k_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq]
    exact ⟨k_le_sub_one_of_lt D.R _ D.host.qd_big.1, k_le_sub_one_of_lt D.R _ D.host.qd_big.2⟩
  · intro j t
    obtain ⟨h1, h2, h3⟩ := hW (ι j) (hR.inR j)
    rw [h3, h3, hR.bp_eq]
    exact ⟨(h1 _).1, (h1 _).1, (min_le_left _ _).trans (h2 t)⟩

end GlobalTheory.RunDepth
