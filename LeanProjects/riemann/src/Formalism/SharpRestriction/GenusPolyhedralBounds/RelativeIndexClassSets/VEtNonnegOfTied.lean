import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem cc_le_cc {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ} {ka : WeightFamilies.Wt D j}
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) (wL : WeightFamilies.Wt D j) :
    cc D large₂ H.Cc H.Ac H.CRc wL ≤ cc D large₂ C2 A2 CR wL := by
  unfold cc
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hP.2.2.2.2.2.2.1 (sq_nonneg _)) (Nat.cast_nonneg _)

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def vEt (Q : LocalPointData G la) (ζ : PtsG G la) : ℝ :=
  if j < D.R.m then (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) else 0

theorem phiC_le_vEt (Q : LocalPointData G la) (ζ : PtsG G la)
    (hfin : j < D.R.m → X.vAt la (Q.y ζ) (X.inc _ G.et) ≠ ⊤)
    (hEt : j < D.R.m → 0 < G.iet ∧
      ∀ y : X.Pt la, ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) :
    X.phiC la (Q.y ζ) ≤ vEt Q ζ := by
  unfold vEt
  split_ifs with hj
  · obtain ⟨hi, h⟩ := hEt hj
    have hi' : (0 : ℝ) < 2 * (G.iet : ℝ) := by positivity
    rw [le_div_iff₀ hi']
    have h1 := h (Q.y ζ)
    rw [← EReal.coe_toReal (hfin hj) (X.vAt_ne_bot la (Q.y ζ) _), EReal.coe_le_coe_iff] at h1
    linarith
  · unfold PJ.phiC
    rw [if_neg hj]

theorem vEt_nonneg (Q : LocalPointData G la) (ζ : PtsG G la)
    (hfin : j < D.R.m → X.vAt la (Q.y ζ) (X.inc _ G.et) ≠ ⊤)
    (hEt : j < D.R.m → 0 < G.iet ∧
      ∀ y : X.Pt la, ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) :
    0 ≤ vEt Q ζ :=
  (Formalism.MainNotions.Gaps.T0.phiC_nonneg X la (Q.y ζ)).trans (phiC_le_vEt Q ζ hfin hEt)

theorem nu_le_of {large₂ : SizeData₂ D} {H : KHyp} {S : Scal B} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH1 : H1 large₂ X H S wL nus) (Q : LocalPointData G la) (ζ : PtsG G la) (c : ℝ) (hc : cc D large₂ H.Cc H.Ac H.CRc wL ≤ c)
    (hd1 : X.depth S.sW wL la (Q.y ζ) ≠ ⊤) (hd2 : X.depth S.sW wL la (Q.y ζ) ≠ ⊥)
    (hfin : j < D.R.m → X.vAt la (Q.y ζ) (X.inc _ G.et) ≠ ⊤)
    (hEt : j < D.R.m → 0 < G.iet ∧
      ∀ y : X.Pt la, ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) :
    Q.nu S ζ ≤ nus la + max 0 c * vEt Q ζ := by
  have h1 := hH1.2.2.2 la (Q.y ζ)
  rw [← EReal.coe_toReal hd1 hd2, EReal.coe_le_coe_iff] at h1
  have h2 := Formalism.MainNotions.Gaps.T0.phiC_nonneg X la (Q.y ζ)
  have h3 := phiC_le_vEt Q ζ hfin hEt
  have h4 : cc D large₂ H.Cc H.Ac H.CRc wL * X.phiC la (Q.y ζ) ≤ max 0 c * X.phiC la (Q.y ζ) :=
    mul_le_mul_of_nonneg_right (hc.trans (le_max_right _ _)) h2
  have h5 : max 0 c * X.phiC la (Q.y ζ) ≤ max 0 c * vEt Q ζ := mul_le_mul_of_nonneg_left h3 (le_max_left _ _)
  unfold LocalPointData.nu
  linarith

theorem tied_et {large₂ : SizeData₂ D} {S : Scal B} {CRm : ℝ} {T : ℕ} {c Gc Prw Ch Ah Cf Af : ℝ}
    (hT : G.Tied large₂ S CRm T c Gc Prw Ch Ah Cf Af) (la : HeightOneSpectrum (𝓞 B.KO)) :
    j < D.R.m → 0 < G.iet ∧
      ∀ y : X.Pt la, ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et) := fun hj =>
  ⟨(hT.2.2.2.2.2.2.2.2.2.2.2.2.2 hj).1, fun y => (hT.2.2.2.2.2.2.2.2.2.2.2.2.2 hj).2.2.2.1 la y⟩

theorem vEt_nonneg_of_tied {large₂ : SizeData₂ D} {S : Scal B} {CRm : ℝ} {T : ℕ} {c Gc Prw Ch Ah Cf Af : ℝ}
    (hT : G.Tied large₂ S CRm T c Gc Prw Ch Ah Cf Af) (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) :
    0 ≤ vEt Q ζ :=
  vEt_nonneg Q ζ (hTie ζ).2.2.1 (tied_et hT la)

theorem nu_le {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {S : Scal B} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd CRm c Cf Af : ℝ} {T : ℕ}
    (hH1 : H1 large₂ X H S wL nus) (hT : G.Tied large₂ S CRm T c Gc Prw Ch Ah Cf Af)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) :
    Q.nu S ζ ≤ nus la + max 0 (cc D large₂ C2 A2 CR wL) * vEt Q ζ :=
  nu_le_of hH1 Q ζ _ (cc_le_cc hP wL) (hTie ζ).1 (hTie ζ).2.1 (hTie ζ).2.2.1 (tied_et hT la)

theorem ep_nu_int {S : Scal B} (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) :
    ∃ n : ℤ, (ep (unifO X la G.N) ζ : ℝ) * Q.nu S ζ = n := (hTie ζ).2.2.2.1

theorem levels_eq [Fintype (PtsG G la)] (Q : LocalPointData G la) (T : ℕ) (c : ℝ) :
    (T : ℝ) * max 0 c * ∑ ζ, ((ep (unifO X la G.N) ζ : ℝ) * (fdeg ζ : ℝ)) * vEt Q ζ =
      if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0 := by
  split_ifs with hj
  · unfold LocalPointData.Net vEt
    rw [finsum_eq_sum_of_fintype]
    simp only [if_pos hj]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    ring
  · unfold vEt
    simp only [if_neg hj, mul_zero, Finset.sum_const_zero]

end Formalism.MainNotions.Gaps.EtaleWeightGaps
