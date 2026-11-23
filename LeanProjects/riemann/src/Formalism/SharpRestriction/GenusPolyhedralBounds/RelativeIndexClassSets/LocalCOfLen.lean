import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.JWMggWMem
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

def LenPoleL {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} : Prop :=
  ∀ (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → Q.InLift T → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, Q.mm S T e ζ * fdeg ζ : ℕ) : ℕ∞)

theorem localC_of_len
    (hLB : ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenBase (X := X) (ka := ka) (wL := wL) (wF := wF))
    (hLP : ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenPoleL (X := X) (ka := ka) (wL := wL) (wF := wF)) :
    LocalC D B P := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hHyp hLat hSup hLAM hQ
    G Gc PH Prw Pet Pd hTW hTTh hTZ hTQ hTEt hDH hDS hDL hPG hSRd hSRho hSRhoP hPD hCB
    la Q hB hC hTie hLift hCZ hCM hIla e he V' hV'
  have hΘ := theta_le_msup_of_hypC (X j h1 h2) S hHyp
  have hspK := (span_Thc_of_hypC hHyp).2.2
  obtain ⟨-, hSet, -, -, hH2, -⟩ := hHyp
  have hka := ka_eq_addL_of_setC hSet
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT0, hDT, -⟩ := hSet
  have hok : Q.Ok S K.CRm T (cc D large₂ C2 A2 CR wL) := ⟨hB, hC, hTie, hCZ, hCM⟩
  have hw : ∀ k, G.w k ∈ (X j h1 h2).WWc S.sW wL := by
    intro k
    rw [← hTW.1]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hth'M : ∀ i, G.th' i ∈ B.Mlat j wF := fun i => hH2.2.1 (hTTh i).1
  exact localBound G la Q S K.CRm (cc D large₂ C2 A2 CR wL) e (nus la) hka hLat hΘ hspK hT0 hDT hw hTW.2.1
    (fun i => (hTTh i).1) hth'M
    (fun k => (hTZ.1 k).1) (fun k => (hTZ.1 k).2.1) (fun k => (hTZ.1 k).2.2.2) hTZ.2.1 hTZ.2.2
    hTQ.2.1 hTQ.2.2.1 hB hC hTie hCM
    (fun ζ => vEt_nonneg_comb hCB Q ζ) (fun ζ => nu_le_comb hCB Q hTie ζ) he
    (hLB j (X j h1 h2) ka wL wF G la Q S K.CRm T (cc D large₂ C2 A2 CR wL) hok hth'M hw hIla)
    (hLP j (X j h1 h2) ka wL wF G la Q S K.CRm T e (cc D large₂ C2 A2 CR wL) hok hLift hw)
    V' hV'

end Formalism.MainNotions.Gaps.EtaleWeightGaps
