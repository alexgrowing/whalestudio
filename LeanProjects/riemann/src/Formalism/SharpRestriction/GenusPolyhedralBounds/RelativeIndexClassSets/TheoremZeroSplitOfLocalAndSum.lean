import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfLocalAndSum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VEtNonnegOfTied
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsLatticeOfAdmissible
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ModulusPosOfThirdHypothesis

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

section J

variable {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem hypC_of_hyp {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR Bx CT : ℝ} {S : Scal B} {T nP nW : ℕ} {h0 : ℝ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (h : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) :
    HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus := by
  obtain ⟨a1, a2, a3, ⟨b1, b2, b3, -⟩, a5, a6, a7, a8⟩ := h
  exact ⟨a1, a2, a3, ⟨b1, b2, b3⟩, a5, a6, a7, a8⟩

theorem split_of_tied {G : GlobalFamilyData X ka wL wF} {large₂ : SizeData₂ D} {S : Scal B} {CRm : ℝ} {T : ℕ} {c Gc Prw Ch Ah Cf Af : ℝ}
    (hT : G.Tied large₂ S CRm T c Gc Prw Ch Ah Cf Af) :
    G.TiedW S Gc Prw ∧ G.TiedTh S Gc ∧ G.TiedZ S T Gc ∧ G.TiedQ large₂ S CRm T c Ch Ah ∧ G.TiedEt large₂ Cf Af := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hT
  exact ⟨⟨a1, a2, a3, a4, a5⟩, a6, ⟨a7, a8, a9⟩, ⟨a10, a11, a12, a13⟩,
    fun hj => ⟨(a14 hj).1, (a14 hj).2.1, (a14 hj).2.2.1, (a14 hj).2.2.2.2⟩⟩

theorem split_of_deepIn {large₂ : SizeData₂ D} {CG AG Pd : ℝ} (h : DeepIn X ka large₂ CG AG Pd) :
    DeepHerm X ka ∧ DeepSubMul X ∧ DeepLogD X ka Pd ∧ PageGd X ka large₂ CG AG Pd := h

theorem split_of_shares {del rz rq d T : ℕ} {CRm c : ℝ} (h : Shares D wL del rz rq d T CRm c) :
    ShareRd (D := D) (j := j) T del d ∧ ShareRho (D := D) (j := j) T rz d ∧ ShareRhoP (D := D) (j := j) T rq d := h

theorem split_of_inContain {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {S : Scal B} {CRm : ℝ} {T : ℕ} {c : ℝ}
    (h : InContain G la S CRm T c) : InContainZ G la S T ∧ InContainM G la CRm T c := h

theorem combined_bound_of_H1_admissible {large₂ : SizeData₂ D} {H : KHyp} {S : Scal B} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (G : GlobalFamilyData X ka wL wF) (hH1 : H1 large₂ X H S wL nus) (c : ℝ) (hc0 : 0 ≤ c) (hc : cc D large₂ H.Cc H.Ac H.CRc wL ≤ c)
    (hEt : j < D.R.m → 0 < G.iet ∧
      ∀ la (y : X.Pt la), ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) :
    CombBound G S c nus := by
  intro la y
  have hφ := Formalism.MainNotions.Gaps.T0.phiC_nonneg X la y
  have hd := hH1.2.2.2 la y
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · obtain ⟨hi, h⟩ := hEt hj
    have hi' : (0 : ℝ) < 2 * (G.iet : ℝ) := by positivity
    have h1 := h la y
    have h0 : (0 : ℝ) ≤ 2 * G.iet * X.phiC la y := mul_nonneg hi'.le hφ
    refine ⟨le_trans (by exact_mod_cast h0) h1, fun hfin => hd.trans ?_⟩
    rw [← EReal.coe_toReal hfin (X.vAt_ne_bot la y _), EReal.coe_le_coe_iff] at h1
    rw [EReal.coe_le_coe_iff]
    have h2 : X.phiC la y ≤ (X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) := by
      rw [le_div_iff₀ hi']; linarith
    have h3 : cc D large₂ H.Cc H.Ac H.CRc wL * X.phiC la y ≤ c * X.phiC la y := mul_le_mul_of_nonneg_right hc hφ
    have h4 : c * X.phiC la y ≤ c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 hc0
    have h5 : c / (2 * (G.iet : ℝ)) * (X.vAt la y (X.inc _ G.et)).toReal =
        c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) := by ring
    rw [h5]
    linarith
  · have h0 : X.phiC la y = 0 := by
      unfold PJ.phiC
      rw [if_neg (not_lt.2 hj)]
    rw [h0, mul_zero, add_zero] at hd
    exact hd

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem vEt_nonneg_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (Q : LocalPointData G la) (ζ : PtsG G la) : 0 ≤ vEt Q ζ := by
  unfold vEt
  split_ifs with hj
  · exact div_nonneg (EReal.toReal_nonneg ((hB la (Q.y ζ)).1 hj).1) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  · exact le_rfl

theorem nu_le_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) : Q.nu S ζ ≤ nus la + max 0 c * vEt Q ζ := by
  have hv := vEt_nonneg_comb hB Q ζ
  have hm : c * vEt Q ζ ≤ max 0 c * vEt Q ζ := mul_le_mul_of_nonneg_right (le_max_right _ _) hv
  by_cases hj : j < D.R.m
  · have h1 := ((hB la (Q.y ζ)).1 hj).2 ((hTie ζ).2.2.1 hj)
    rw [← EReal.coe_toReal (hTie ζ).1 (hTie ζ).2.1, EReal.coe_le_coe_iff] at h1
    have h2 : c / (2 * (G.iet : ℝ)) * (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal = c * vEt Q ζ := by
      unfold vEt
      rw [if_pos hj]
      ring
    rw [h2] at h1
    unfold LocalPointData.nu
    linarith
  · have h1 := (hB la (Q.y ζ)).2 (not_lt.1 hj)
    rw [← EReal.coe_toReal (hTie ζ).1 (hTie ζ).2.1, EReal.coe_le_coe_iff] at h1
    have h2 : 0 ≤ max 0 c * vEt Q ζ := mul_nonneg (le_max_left _ _) hv
    unfold LocalPointData.nu
    linarith

theorem Net_nonneg_comb {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c nus)
    (hj : j < D.R.m) (Q : LocalPointData G la) : 0 ≤ Q.Net := by
  unfold LocalPointData.Net
  exact finsum_nonneg fun ζ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (EReal.toReal_nonneg ((hB la (Q.y ζ)).1 hj).1)

theorem rLa_nonneg_comb {S : Scal B} {c' : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (hB : CombBound G S c' nus)
    (Q : LocalPointData G la) (CRm : ℝ) (T : ℕ) (c : ℝ) : 0 ≤ rLa Q CRm T c := by
  unfold rLa
  have h1 : (0 : ℝ) ≤ (if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0) := by
    split_ifs with hj
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (le_max_left _ _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))) (Net_nonneg_comb hB hj Q)
    · exact le_rfl
  have h2 : (0 : ℝ) ≤ (Q.Ila.toNat : ℝ) := Nat.cast_nonneg _
  exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg h2 h1)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

theorem theta_le_msup_of_hypC {large₂ : SizeData₂ D} (X : PJ D B P j) {H : KHyp} {C2 A2 CR Bx CT : ℝ} (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (h : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) : X.Theta S ka wL wF T ≤ X.Msup ka :=
  Formalism.MainNotions.Gaps.T0.theta_le_msup_of_setC X S h.2.2.2.2.1 h.2.1

theorem span_Thc_of_hypC {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp} {C2 A2 CR Bx CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) :
    Submodule.span B.KO (X.Thc S.sF wF : Set (B.Cusp j wF)) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.s0 (X.wF0 wL wF) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤ := by
  obtain ⟨-, -, ⟨-, -, -, -, -, po, -, -, PLam, -, -, hF, h0', hK⟩, -⟩ := hH
  exact ⟨span_eq_top_of_shortG hF, span_eq_top_of_shortG h0', span_eq_top_of_shortG hK⟩

end J

def LocalC (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la),
    InBasis G la → Q.InCurve → Q.InTie S → Q.InLift T → InContainZ G la S T → InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL) →
    Q.Ila ≠ ⊤ →
    ∀ e : ℕ, (T : ℝ) * nus la ≤ (e : ℝ) →
    ∀ V' : Submodule ((X j h1 h2).Kl la) ((X j h1 h2).Vl la), V' ≤ (X j h1 h2).locK la ((X j h1 h2).Msup ka) →
      (X j h1 h2).qlen la ((X j h1 h2).loc la ((X j h1 h2).Msup ka) ⊓ (X j h1 h2).ofK la V')
        ((X j h1 h2).loc la ((X j h1 h2).Theta S ka wL wF T) ⊓ (X j h1 h2).ofK la V') ≠ ⊤ ∧
      (((X j h1 h2).qlen la ((X j h1 h2).loc la ((X j h1 h2).Msup ka) ⊓ (X j h1 h2).ofK la V')
          ((X j h1 h2).loc la ((X j h1 h2).Theta S ka wL wF T) ⊓ (X j h1 h2).ofK la V')).toNat : ℝ) ≤
        (e : ℝ) * (Module.finrank ((X j h1 h2).Kl la) V' : ℝ) + rLa Q K.CRm T (cc D large₂ C2 A2 CR wL)

def SumC (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    ∀ Qf : ∀ la, LocalPointData G la, Heights Qf Gc PH Prw Pet →
    Summable (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ∧
    (∑' la, rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ≤
      (X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2

theorem theorem_zero_split_of_local_and_sum (hL : LocalC D B P) (hS : SumC D B P) : Conclusion1OfComb (D := D) (B := B) (P := P) := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd Qf
    tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP iB iC iT iLf iZ iM hB hHt
  obtain ⟨hrs, hrb⟩ := hS large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA
    G Gc PH Prw Pet Pd tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB Qf hHt
  exact concl_of_nat (X j h1 h2) S ka wL wF T nus _ (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL))
    hH.2.2.2.1.1 (fun la => rLa_nonneg_comb hB (Qf la) _ _ _) hrs hrb
    (fun la e he V' hV => hL large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA
      G Gc PH Prw Pet Pd tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB la (Qf la) (iB la) (iC la) (iT la)
      (iLf la tW (iC la) (iT la)) (iZ la) (iM la) (hHt.1 la) e he V' hV)

def LiftAll (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ), Q.Ok S CRm T c → Q.InLift T

theorem theorem_zero_bundled_of_split (hLf : LiftAll D B P) (h : Conclusion1OfComb (D := D) (B := B) (P := P)) :
    Conclusion1Of2 (D := D) (B := B) (P := P) := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT hA hBan hin j h1 h2 S ka wL wF T nP nW h0 nus hH
  obtain ⟨G, Gc, PH, Prw, Pet, Pd, hT, hI, hSh, hP, Qf, hOk, hHt⟩ := hin j h1 h2 S ka wL wF T nP nW h0 nus hH
  obtain ⟨tW, tTh, tZ, tQ, tEt⟩ := split_of_tied hT
  obtain ⟨dH, dS, dL, pG⟩ := split_of_deepIn hI
  obtain ⟨sRd, sRho, sRhoP⟩ := split_of_shares hSh
  exact h large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus (hypC_of_hyp hH)
    (hA.1 j h1 h2 ka) (fun F σ => hA.2.1.2 j h1 h2 ka F σ) (hA.2.2.2.2.1 j h1 h2 ka)
    (fun hj hCR hO hn hLP hsz hT hc hTc => hA.2.2.2.2.2.2 hCR hO j h1 hj ka hn hLP hsz _ _ hT hc hTc)
    G Gc PH Prw Pet Pd Qf tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP (fun la => (hOk la).1)
    (fun la => (hOk la).2.1) (fun la => (hOk la).2.2.1)
    (fun la _ _ _ => hLf j _ ka wL wF G la (Qf la) S _ T _ (hOk la)) (fun la => (split_of_inContain (hOk la).2.2.2).1)
    (fun la => (split_of_inContain (hOk la).2.2.2).2)
    (combined_bound_of_H1_admissible G hH.2.2.2.1 _ (cc_pos_of hH.2.1 hH.2.2.2.2.2.1 hP).le (cc_le_cc hP wL)
      (fun hj => ⟨(hT.2.2.2.2.2.2.2.2.2.2.2.2.2 hj).1, (hT.2.2.2.2.2.2.2.2.2.2.2.2.2 hj).2.2.2.1⟩))
    hHt

end Formalism.MainNotions.Gaps.EtaleWeightGaps
