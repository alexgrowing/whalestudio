import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.SizeBoundsAlt

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem deepPacketP (large₂ : SizeData₂ D) (X : PJ D B P j)
    (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (th : Fin ρ → B.Cusp j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ)
    (hal : ∀ k, ∑ i, al k i = a0)
    (z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka)
    (hz : ∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β)
    (c : HeightOneSpectrum (𝓞 B.KO) → ℝ) (hc0 : ∀ la, 0 ≤ c la) (hG : GaussLe (B.Mlat j ka) z c)
    (hW : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, detPoly φ z ≠ 0)
    {dH : ℕ} (Hm : Herm (fun σ => B.l2NormAlt j ka σ) dH)
    (hT : ∀ Ctr, ((finrank B.KO (B.Cusp j ka) * finrank ℚ B.KO : ℕ) : ℝ) < Ctr → Trans (B.Mlat j ka) Hm Ctr)
    (hSM : SubMul X) (tableDegreeThreeBase : ℝ)
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(tableDegreeThreeBase * ka.size) ≤ WeightFamilies.meanLogSup B F) (G Prw Pd : ℝ)
    (hS2 : ∀ σ (F : B.Cusp j ka), B.supN j ka σ F ^ 2 ≤ Real.exp Pd * B.l2NormAlt j ka σ F ^ 2)
    (hG0 : 0 ≤ G) (hPrw : 0 ≤ Prw)
    (mx : (B.KO →+* ℂ) → ℝ) (hmx : ∀ σ k, B.supN j wL σ (w k) ≤ Real.exp (mx σ))
    (hmxm : (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size)
    (hth : ∀ k, WeightFamilies.meanLogSup B (th k) ≤ G * w0.size)
    (ha : (a0 : ℝ) ≤ ka.size) (hrw : Real.log N ≤ Prw * (wL.size - 1))
    (hd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd) (hO : OPO large₂ B) :
    Summable (fun la => c la * X.lN la) ∧
      ∑' la, c la * X.lN la ≤
        ρ * ((2 * G + Prw + tableDegreeThreeBase + (3 / 2) * (Pd + PO D large₂)) * ka.size) := by
  subst hwt
  set d : ℕ := finrank B.KO (B.Cusp j (wtIter wadd wL w0 a0)) with hddef
  have hnK : 1 ≤ finrank ℚ B.KO := Module.finrank_pos (R := ℚ) (M := B.KO)
  have hlognK : 0 ≤ Real.log (finrank ℚ B.KO : ℝ) := Real.log_natCast_nonneg _
  have hPd0 : 0 ≤ Pd := (Real.log_natCast_nonneg _).trans hd
  have hPO0 : 0 ≤ PO D large₂ := hlognK.trans hO.1
  have hE : ∀ σ k, ∑ γ ∈ (z k).support, B.l2NormAlt j _ σ (z k γ) ≤
      Real.exp ((a0 : ℝ) * (Real.log N + mx σ) + Real.log (B.supN j w0 σ (th k))) := by
    intro σ k
    have hk := hal k
    have h3 : ∑ γ ∈ (z k).support, B.supN j _ σ (z k γ) ≤
        (∑ i, B.supN j wL σ (w i)) ^ a0 * B.supN j w0 σ (th k) := by
      have hzk := hz k
      revert hzk
      generalize z k = zk
      revert zk
      rw [← hk]
      intro zk hzk
      exact polynomial_coefficient_l1_bound X hSM w (al k) (th k) σ zk hzk
    refine (Finset.sum_le_sum fun γ _ => B.l2Norm_le_supNorm_alt j _ σ (z k γ)).trans (h3.trans ?_)
    have h4 : ∑ i, B.supN j wL σ (w i) ≤ Real.exp (Real.log N + mx σ) := by
      calc ∑ i, B.supN j wL σ (w i) ≤ ∑ _i : Fin N, Real.exp (mx σ) := Finset.sum_le_sum fun i _ => hmx σ i
        _ = N * Real.exp (mx σ) := by simp
        _ ≤ Real.exp (Real.log N) * Real.exp (mx σ) :=
            mul_le_mul_of_nonneg_right (Real.le_exp_log _) (Real.exp_pos _).le
        _ = _ := (Real.exp_add _ _).symm
    rw [Real.exp_add, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => B.supN_nonneg j wL σ _) h4 _)
      (Real.le_exp_log _) (B.supN_nonneg j w0 σ _) (pow_pos (Real.exp_pos _) _).le
  have hC0 : Real.log (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1) ≤
      1 * (Real.log (d : ℝ) + Real.log (finrank ℚ B.KO : ℝ)) := by
    rw [one_mul]
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h]; simpa using hlognK
    · have h5 : (1 : ℝ) ≤ ((d * finrank ℚ B.KO : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos h hnK
      rw [max_eq_left h5, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have := deepSum (B.Mlat j _) z c hc0 hG hW Hm (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) (fun Ctr h => hT Ctr (lt_of_le_of_lt (le_max_left _ _) h))
    (fun σ => B.supN j _ σ)
    (fun σ f hf => lt_of_le_of_ne (B.supN_nonneg j _ σ f) (fun h => hf ((B.supN_eq_zero j _ σ f).mp h.symm)))
    tableDegreeThreeBase (wtIter wadd wL w0 a0).size Pd
    (fun f hf hf0 => hLAM f hf hf0)
    hS2
    (a0 : ℝ) (Real.log N) mx (fun σ k => Real.log (B.supN j w0 σ (th k))) hE (Nat.cast_nonneg _)
    1 G Prw (PO D large₂) wL.size w0.size (Real.log (d : ℝ)) le_rfl hG0 hPrw hPd0 hPO0
    (WeightFamilies.Wt.one_le_size _) (zero_le_one.trans (WeightFamilies.Wt.one_le_size _)) hmxm hth
    (by rw [size_wtIter]; ring) ha hrw hd hC0 hO.1 hO.2
  have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [e] at this
  exact this

theorem deepFinalP (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (hw : ∀ k, w k ∈ B.Mlat j wL) (th : Fin ρ → B.Cusp j w0)
    (hthM : ∀ k, th k ∈ B.Mlat j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ) (hal : ∀ k, ∑ i, al k i = a0)
    (z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka)
    (hz : ∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β)
    (hW : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, detPoly φ z ≠ 0)
    (hlat : WeightAlgebra.adm1 B) {dH : ℕ} (Hm : Herm (fun σ => B.l2NormAlt j ka σ) dH) (hconj : Hm.Conj)
    (hSM : SubMul X) (tableDegreeThreeBase : ℝ)
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(tableDegreeThreeBase * ka.size) ≤ WeightFamilies.meanLogSup B F) (G Prw Pd : ℝ)
    (hS2 : ∀ σ (F : B.Cusp j ka), B.supN j ka σ F ^ 2 ≤ Real.exp Pd * B.l2NormAlt j ka σ F ^ 2)
    (hG0 : 0 ≤ G) (hPrw : 0 ≤ Prw)
    (mx : (B.KO →+* ℂ) → ℝ) (hmx : ∀ σ k, B.supN j wL σ (w k) ≤ Real.exp (mx σ))
    (hmxm : (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size)
    (hth : ∀ k, WeightFamilies.meanLogSup B (th k) ≤ G * w0.size)
    (ha : (a0 : ℝ) ≤ ka.size) (hrw : Real.log N ≤ Prw * (wL.size - 1))
    (hd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd) (hO : OPO large₂ B) :
    Summable (fun la => (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la) ∧
      ∑' la, (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la ≤
        ρ * ((2 * G + Prw + tableDegreeThreeBase + (3 / 2) * (Pd + PO D large₂)) * ka.size) := by
  obtain ⟨z', hz1, hz2⟩ := exists_zFam X ka wL w0 a0 hwt w hw th hthM al hal
  have hzM : ∀ k β, z k β ∈ B.Mlat j ka := by
    intro k β
    have : z k β = z' k β := X.inc_inj ka ((hz k β).trans (hz1 k β).symm)
    rw [this]; exact hz2 k β
  exact deepPacketP large₂ X ka wL w0 a0 hwt w th al hal z hz _ (fun la => gaussC_nonneg _ z la)
    (gaussC_gaussLe hzM) hW Hm
    (fun Ctr hC => trans_of_minima transference_successive_minima _ (hlat j h1 h2 ka).span_eq_top Hm hconj Ctr hC)
    hSM tableDegreeThreeBase hLAM G Prw Pd hS2 hG0 hPrw mx hmx hmxm hth ha hrw hd hO

theorem deepFinalP_adm (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (hw : ∀ k, w k ∈ B.Mlat j wL) (th : Fin ρ → B.Cusp j w0)
    (hthM : ∀ k, th k ∈ B.Mlat j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ) (hal : ∀ k, ∑ i, al k i = a0)
    (z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka)
    (hz : ∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β)
    (hW : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, detPoly φ z ≠ 0)
    (hlat : WeightAlgebra.adm1 B) {dH : ℕ} (Hm : Herm (fun σ => B.l2NormAlt j ka σ) dH) (hconj : Hm.Conj)
    (hSM : SubMul X) (tableDegreeThreeBase CG AG : ℝ)
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(tableDegreeThreeBase * ka.size) ≤ WeightFamilies.meanLogSup B F)
    (hS2 : WeightFamilies.adm2 large₂ B CG AG)
    (G Prw Pd : ℝ) (hPrw : 0 ≤ Prw)
    (mx : (B.KO →+* ℂ) → ℝ) (hmx : ∀ σ k, Real.log (B.supN j wL σ (w k)) ≤ mx σ)
    (hmxm : (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size)
    (hth : ∀ k, WeightFamilies.meanLogSup B (th k) ≤ G * w0.size)
    (ha : (a0 : ℝ) ≤ ka.size) (hrw : Real.log N ≤ Prw * (wL.size - 1))
    (hd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd)
    (hPd : WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd) (hO : OPO large₂ B) :
    Summable (fun la => (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la) ∧
      ∑' la, (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la ≤
        ρ * ((2 * max G 0 + Prw + tableDegreeThreeBase + (3 / 2) * (Pd + PO D large₂)) * ka.size) := by
  have hsz : ∀ w' : WeightFamilies.Wt D j, G * w'.size ≤ max G 0 * w'.size := fun w' =>
    mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans (WeightFamilies.Wt.one_le_size w'))
  exact deepFinalP large₂ X h1 h2 ka wL w0 a0 hwt w hw th hthM al hal z hz hW hlat Hm hconj hSM tableDegreeThreeBase hLAM
    (max G 0) Prw Pd
    (fun σ F => (hS2 j h1 h2 ka F σ).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hPd) (sq_nonneg _)))
    (le_max_right _ _) hPrw mx
    (fun σ k => (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (hmx σ k)))
    (hmxm.trans (hsz wL)) (fun k => (hth k).trans (hsz w0)) ha hrw hd hO

theorem n_le_sizeW (ka : WeightFamilies.Wt D j) : (ka.n : ℝ) ≤ ka.size := by
  have hf : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 : 0 ≤ ∑ τ, ((∑ i, (ka.aP τ i : ℝ)) + ∑ i, (ka.aM τ i : ℝ)) := by positivity
  have h2 : 1 ≤ D.R.f * max (D.R.sigW j).2 1 * D.R.r :=
    Nat.mul_pos (Nat.mul_pos (by omega) (lt_of_lt_of_le Nat.one_pos (le_max_right _ _))) (by omega)
  have h3 : (1 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) := by exact_mod_cast h2
  have h4 : (ka.n : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) h3
  unfold WeightFamilies.Wt.size
  linarith

theorem vanishingOrder_le_weight_size (ka : WeightFamilies.Wt D j) (T nP nW : ℕ) (hk : ka.n = nP + T * nW) (hW : 0 < nW) :
    (a0 D j T : ℝ) ≤ ka.size := by
  have h1 : a0 D j T ≤ ka.n := by
    rw [hk]
    exact (Nat.sub_le _ _).trans ((Nat.le_mul_of_pos_right T hW).trans (Nat.le_add_left _ _))
  exact (Nat.cast_le.mpr h1).trans (n_le_sizeW ka)

theorem deepGP (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (CRm : ℝ) (T nP nW : ℕ) (c Gc Prw Ch Ah Cf Af CG AG p Pd : ℝ)
    (hF : IsF' ka wL wF T nP) (hn : wL.n = nW) (hk : ka.n = nP + T * nW) (hD : WeightFamilies.dimY D j ≤ T) (hW : 0 < nW)
    (hT : G.Tied large₂ S CRm T c Gc Prw Ch Ah Cf Af) (hI : DeepIn X ka large₂ CG AG Pd) (hG0 : 0 ≤ Gc) (hP0 : 0 ≤ Prw)
    (hlat : WeightAlgebra.adm1 B)
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(p * ka.size) ≤ WeightFamilies.meanLogSup B F)
    (hS2 : WeightFamilies.adm2 large₂ B CG AG) (hO : OPO large₂ B) :
    Summable (fun la => (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) ∧
      ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la ≤
        G.rz * ((2 * Gc + Prw + p + 3 / 2 * (Pd + PO D large₂)) * ka.size) := by
  obtain ⟨-, hwM, hrw, hmx, hmxm, -, h0, hz, hWd, -⟩ := hT
  obtain ⟨⟨dH, Hm, hconj⟩, hSM, hd, hPd⟩ := hI
  have := deepFinalP_adm large₂ X h1 h2 ka wL (X.wF0 wL wF) (a0 D j T) (SizeBoundsAlt.hwt_of X ka wL wF T nP nW hF hn hk hD)
    G.w hwM G.th0 (fun k => (h0 k).2.1) G.alz (fun k => (h0 k).2.2.2) G.zc hz hWd hlat Hm hconj hSM p CG AG
    hLAM hS2 Gc Prw Pd hP0 G.mx hmx hmxm (fun k => (h0 k).2.2.1) (vanishingOrder_le_weight_size ka T nP nW hk hW) hrw hd hPd hO
  rwa [max_eq_left hG0] at this

theorem deepGW (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (CRm : ℝ) (T nP nW : ℕ) (c Gc Prw Ch Ah Cf Af CG AG CL AL Pd : ℝ)
    (hF : IsF' ka wL wF T nP) (hn : wL.n = nW) (hk : ka.n = nP + T * nW) (hD : WeightFamilies.dimY D j ≤ T) (hW : 0 < nW)
    (hT : G.Tied large₂ S CRm T c Gc Prw Ch Ah Cf Af) (hI : DeepIn X ka large₂ CG AG Pd) (hG0 : 0 ≤ Gc) (hP0 : 0 ≤ Prw)
    (hlat : WeightAlgebra.adm1 B) (hLAM : LAMw large₂ B CL AL) (hS2 : WeightFamilies.adm2 large₂ B CG AG) (hO : OPO large₂ B) :
    Summable (fun la => (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) ∧
      ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la ≤
        G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ CL AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) :=
  deepGP large₂ X h1 h2 G S CRm T nP nW c Gc Prw Ch Ah Cf Af CG AG (WeightFamilies.PP0v D large₂ CL AL * (1 + Real.log ka.size)) Pd
    hF hn hk hD hW hT hI hG0 hP0 hlat (fun F hF hF0 => hLAM j h1 h2 ka F hF hF0) hS2 hO

theorem deepGW_of_setC (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (CRm : ℝ) (T nP nW : ℕ) (h0 CK C1 A1 c Gc Prw Ch Ah Cf Af CG AG CL AL Pd : ℝ)
    (hC : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0)
    (hT : G.Tied large₂ S CRm T c Gc Prw Ch Ah Cf Af) (hI : DeepIn X ka large₂ CG AG Pd) (hG0 : 0 ≤ Gc) (hP0 : 0 ≤ Prw)
    (hlat : WeightAlgebra.adm1 B) (hLAM : LAMw large₂ B CL AL) (hS2 : WeightFamilies.adm2 large₂ B CG AG) :
    Summable (fun la => (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) ∧
      ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la ≤
        G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ CL AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, -, -, -, -, hV, hIL, hIF, -, -, hD, -, -, h40, -, -, hO, -⟩ := hC
  exact deepGW large₂ X h1 h2 G S CRm T nP nW c Gc Prw Ch Ah Cf Af CG AG CL AL Pd hIF hIL.1 (hk.trans hV) hD
    (lt_of_lt_of_le (by norm_num) h40) hT hI hG0 hP0 hlat hLAM hS2 hO

theorem deepGW_of_hyp (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR Bx CT : ℝ)
    (hA : AdmW large₂ X K H Ch Ah Cq Aq) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j}
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : Hyp large₂ (X j h1 h2) H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData (X j h1 h2) ka wL wF) (c Gc PH Prw Pet Pd : ℝ)
    (hT : G.Tied large₂ S K.CRm T c Gc Prw Ch Ah K.Cf K.Af) (hI : DeepIn (X j h1 h2) ka large₂ K.CG K.AG Pd)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    Summable (fun la => (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * (X j h1 h2).lN la) ∧
      ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * (X j h1 h2).lN la ≤
        G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) :=
  deepGW_of_setC large₂ (X j h1 h2) h1 h2 G S K.CRm T nP nW h0 H.CK H.C1 H.A1 c Gc Prw Ch Ah K.Cf K.Af K.CG K.AG K.CL K.AL Pd
    hH.2.1 hT hI hP.2.2.1 hP.2.2.2.1 hA.1 hA.2.2.2.2.1 hA.2.1.2

theorem deepGW_of_hyp_PP (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR Bx CT : ℝ)
    (hA : AdmW large₂ X K H Ch Ah Cq Aq) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j}
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : Hyp large₂ (X j h1 h2) H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData (X j h1 h2) ka wL wF) (c Gc PH Prw Pet Pd : ℝ)
    (hT : G.Tied large₂ S K.CRm T c Gc Prw Ch Ah K.Cf K.Af) (hI : DeepIn (X j h1 h2) ka large₂ K.CG K.AG Pd)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * (X j h1 h2).lN la ≤ G.rz * (WeightFamilies.PPv D large₂ C2 A2 * ka.size) :=
  (deepGW_of_hyp large₂ X K H Ch Ah Cq Aq C2 A2 CR Bx CT hA h1 h2 S T nP nW h0 nus hH G c Gc PH Prw Pet Pd hT hI hP).2.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hP.2.2.2.2.2.2.2.2.2.2.2.2.1 (zero_le_one.trans (WeightFamilies.Wt.one_le_size ka)))
      (Nat.cast_nonneg _))

end Formalism.MainNotions.Gaps.EtaleWeightGaps

end
