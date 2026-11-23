import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsIntegralCoeffCof
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefMapRecord

open Formalism.L2.NTheta

lemma floor_toNat_cast {x : ℚ} (z : ℤ) (hz : x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  subst hz
  rw [Int.floor_intCast]
  have h : 0 ≤ z := by exact_mod_cast h0
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

lemma lamAt_b {R : Ranks} (h : HCParam R) (n c : ℕ) (hc : c < R.m) (hn : n = R.k - 1 + c) : lamAt h n = -h.b ⟨c, hc⟩ := by
  subst hn
  unfold lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 3
  omega

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma aPl_cast (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) =
      lamAt (D.hc τ) n + (D.hc τ).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) n
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  rw [aPl, if_pos hn]
  refine floor_toNat_cast (z + e - ((D.R.k + i : ℕ) - (n + 1)) - (s + 1)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hn
    have h1 := lamAt_add_add_le (D.hc τ) d n (by unfold Ranks.r; omega)
    rw [lamAt_b (D.hc τ) (n + d) i hi (by omega)] at h1
    have h2 := (D.hc τ).gap_be i
    rw [hd]
    push_cast
    simp only [Fin.eta] at h1
    linarith

lemma aMi_cast (q n c : ℕ) (hq : i + 1 + q = D.R.m) (hn : n + c + 1 = q) :
    (aMi D i (D.R.k + i) q τ n : ℚ) =
      -((D.hc τ).e i - (D.hc τ).b ⟨i + 1 + c, by omega⟩ + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i + 1 + c, by omega⟩
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have h0 := lamAt_b (D.hc τ) (D.R.k + i + c) (i + 1 + c) (by omega) (by omega)
  rw [aMi, if_pos (by omega), show q - n = c + 1 by omega, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, h0,
    ← sub_eq_add_neg, Nat.cast_succ]
  refine floor_toNat_cast (-(e - z + (c + 1) + s)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · have h1 := lamAt_add_add_le (D.hc τ) c (D.R.k + i) (by unfold Ranks.r; omega)
    rw [h0, lamAt_b (D.hc τ) (D.R.k + i) (i + 1) (by omega) (by omega)] at h1
    have h2 := (D.hc τ).gap_eb i (by omega)
    linarith

lemma lamV_eq : ∃ s : ℤ, ∀ n : Fin (Vc D i).rank, (lamV D i τ).w n =
    s + (if (n : ℕ) < D.R.k + i then (aPl D i (D.R.k + i) τ n : ℤ) else 0) -
      (if (Fin.rev n : ℕ) < D.R.m - (i + 1) then (aMi D i (D.R.k + i) (D.R.m - (i + 1)) τ (Fin.rev n) : ℤ) else 0) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hW⟩ :=
    GlobalTheory.ForcedWeights.lamLForced D (i + 1) (Nat.le_add_left _ _) hi τ
  have hWe' : (W.e : ℚ) = (D.hc τ).e i := hWe
  have hr : (Vc D i).rank = D.R.k + D.R.m - 1 + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) hi
  obtain ⟨q, hq⟩ : ∃ q, i + 1 + q = D.R.m := ⟨D.R.m - (i + 1), by omega⟩
  have hp : W.p = D.R.k + i := by unfold IndefiniteWeightData.WeightData.p; omega
  have hq' : W.q = q := by unfold IndefiniteWeightData.WeightData.q; omega
  have hnV : W.nV = D.R.k + i + q + D.R.t := by unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; omega
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have ha' : (D.R.k : ℚ) = a + a := by exact_mod_cast ha
  have hb' : (q : ℚ) = b + b - i - 1 := by
    have : ((i : ℕ) : ℚ) + 1 + q = b + b := by exact_mod_cast hq.trans hb
    linarith
  have hd : W.dTau = ((a + (i : ℕ) - b - W.e : ℤ) : ℚ) := by
    unfold IndefiniteWeightData.WeightData.dTau
    rw [hp, hq']
    push_cast
    rw [ha', hb']
    ring
  generalize (a + (i : ℕ) - b - W.e : ℤ) = s at hd
  rw [show D.R.m - (i + 1) = q by omega]
  refine ⟨s, fun n => ?_⟩
  have hn := n.2
  rw [← Int.cast_inj (α := ℚ), hW n, IndefiniteWeightData.WeightData.lamPrime, hd, IndefiniteWeightData.WeightData.thetaWt, hp, hq', hWt, Fin.val_rev,
    Int.cast_sub, Int.cast_add]
  by_cases h1 : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega), Int.cast_natCast, aPl_cast D i τ n h1, IndefiniteWeightData.WeightData.aPlus,
      hp, hq', hnV, hWe']
    have hl : (W.lam (n + 1) : ℚ) = lamAt (D.hc τ) n := by
      unfold IndefiniteWeightData.WeightData.lam
      rw [hWk]
      split_ifs with h2
      · rw [lamAt, dif_pos (by omega)]
        exact hWv ⟨n, by omega⟩
      · rw [lamAt_b (D.hc τ) n (n - (D.R.k - 1)) (by omega) (by omega), Int.cast_neg,
          show (n : ℕ) + 1 - (D.R.k - 1) = n - (D.R.k - 1) + 1 by omega]
        exact congrArg _ (hWb ⟨n - (D.R.k - 1), by omega⟩)
    rw [hl]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : (n : ℕ) + 1 ≤ D.R.k + i + D.R.t
    · rw [if_pos h2, if_neg (by omega)]
      push_cast
      ring
    · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + D.R.t + c := ⟨n - (D.R.k + i + D.R.t), by omega⟩
      rw [if_neg h2, if_pos (by omega), Int.cast_natCast, aMi_cast D i τ q _ c hq (by omega), IndefiniteWeightData.WeightData.aMinus,
        hq', hWj, hWt, hWe', show q + 1 - (q + 1 - (n + 1 - (D.R.k + i) - D.R.t)) = c + 1 by omega,
        show (i : ℕ) + 1 + (c + 1) = i + 1 + c + 1 by omega, hWb ⟨i + 1 + c, by omega⟩]
      push_cast
      ring

theorem exists_io_record : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  intro D Q hQ κ hκ i c'
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨-, hinj, hΨ, -, hval⟩ := GlobalTheory.WeightExponents.weight_exponents D Q hQ _ (inR i) (κ i)
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 _ (inR i)
  have hp1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have hq1 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  choose s hs using lamV_eq D i
  refine GlobalTheory.FrameRead.CoefMap.exists_ioLFRec D.host.E Q.H (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank D.what₂.Tau (DV.tauEmb D)
    ⟨hinj, fun τ => (hΨ τ).trans (exists_congr fun _ => eq_comm)⟩ ?_ Q.l c' (wtA (κ i)) s (lamV D i) (dom_wtA (κ i)).1 ?_
  · refine le_trans ?_ (r_le_V i)
    rw [hp, hq, hp1, hq1, Ranks.r]
    omega
  · intro τ n
    have ht := hQ.1.2.2.2 τ
    have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D τ) (Q.H.rt : D.host.E) = Q.H.rt0 :=
      GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 τ
    have hsig : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    obtain ⟨h1, h2, -⟩ := hκ i τ
    rw [hsig] at h1 h2
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos ht, if_neg hc, hp, hq, hs τ n,
      (hval τ _).1, (hval τ _).2]
    congr 1
    · congr 1
      refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dif_pos (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), h1]
      rfl
    · refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dif_pos (show (Fin.rev n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2 from h), h2]
      rfl

end GlobalTheory.CoefMapRecord
