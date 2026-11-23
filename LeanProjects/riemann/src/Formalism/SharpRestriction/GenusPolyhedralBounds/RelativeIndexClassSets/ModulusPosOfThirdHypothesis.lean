import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem lw_nonneg' (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw K la := by
  simp only [lw]
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

theorem sum_mul_lw (B : WeightFamilies.Prov D) (nn : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ) (s : Finset (HeightOneSpectrum (𝓞 B.KO)))
    (hs : nn.support ⊆ s) :
    ∑ la ∈ s, nn la * lw B.KO la = (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B := by
  rw [Finsupp.sum_of_support_subset nn hs (fun la v => v * WeightFamilies.lnN B la) (fun _ _ => zero_mul _),
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun la _ => ?_)
  simp only [lw, WeightFamilies.lnN, WeightFamilies.degO]
  ring

theorem quotCoreE (large₂ : SizeData₂ D) {CRm Ch Ah Cq Aq : ℝ} (ka : WeightFamilies.Wt D j) (T c : ℝ)
    (hE : ∃ be : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ, (∀ la, 0 ≤ be la) ∧
      (be.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cq Aq * ka.size ∧
      ∀ th : Fin (WeightFamilies.rhoP B CRm T c j ka) → B.Mlat j ka,
        Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
          WeightFamilies.MggK B CRm T c j ka = ⊤ →
        (∀ i, WeightFamilies.meanLogSup B ((th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) →
      ∃ nn : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ,
        (∀ la, ∃ ℓ : ℕ,
          WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
            (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka))) = ℓ ∧
          (ℓ : ℝ) ≤ nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) ∧
        (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤
          (WeightFamilies.rhoP B CRm T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size)
    (rq : ℕ) (hrq : rq = WeightFamilies.rhoP B CRm T c j ka) (th : Fin rq → B.Mlat j ka)
    (hspan : Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
      WeightFamilies.MggK B CRm T c j ka = ⊤)
    (hsup : ∀ i, WeightFamilies.meanLogSup B ((th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    (∀ la, WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka))) ≠ ⊤) ∧
    Summable (fun la => ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ) *
        lw B.KO la) ∧
    (∑' la, ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ) *
        lw B.KO la) ≤ 2 * (rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  classical
  subst hrq
  obtain ⟨be, -, hbeS, hall⟩ := hE
  obtain ⟨nn, hnn, hnnS⟩ := hall th hspan hsup
  choose ℓ hℓeq hℓle using hnn
  have hlw : ∀ la, 0 ≤ lw B.KO la := fun la => lw_nonneg' B.KO la
  have hρ0 : 0 ≤ (WeightFamilies.rhoP B CRm T c j ka : ℝ) := Nat.cast_nonneg _
  have hg0 : ∀ la ∉ nn.support ∪ be.support, (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la = 0 := by
    intro la hla
    have h1 : nn la = 0 := by
      by_contra hne
      exact hla (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne))
    have h2 : be la = 0 := by
      by_contra hne
      exact hla (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hne))
    rw [h1, h2]
    ring
  have hsg : Summable fun la => (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la :=
    summable_of_ne_finset_zero hg0
  have hle : ∀ la, (ℓ la : ℝ) * lw B.KO la ≤ (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la :=
    fun la => mul_le_mul_of_nonneg_right (hℓle la) (hlw la)
  have hsf : Summable fun la => (ℓ la : ℝ) * lw B.KO la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (Nat.cast_nonneg _) (hlw la)) hle hsg
  refine ⟨fun la => ?_, ?_, ?_⟩
  · rw [hℓeq la]
    exact ENat.coe_ne_top _
  · simp only [hℓeq, ENat.toNat_coe]
    exact hsf
  · simp only [hℓeq, ENat.toNat_coe]
    have hsub1 : nn.support ⊆ nn.support ∪ be.support := fun x hx => Finset.mem_union_left _ hx
    have hsub2 : be.support ⊆ nn.support ∪ be.support := fun x hx => Finset.mem_union_right _ hx
    calc ∑' la, (ℓ la : ℝ) * lw B.KO la
        ≤ ∑' la, (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la := Summable.tsum_le_tsum hle hsf hsg
      _ = ∑ la ∈ nn.support ∪ be.support, (nn la + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * be la) * lw B.KO la := tsum_eq_sum hg0
      _ = ∑ la ∈ nn.support ∪ be.support, nn la * lw B.KO la +
            (WeightFamilies.rhoP B CRm T c j ka : ℝ) * ∑ la ∈ nn.support ∪ be.support, be la * lw B.KO la := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun la _ => by ring)
      _ = (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B +
            (WeightFamilies.rhoP B CRm T c j ka : ℝ) * ((be.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B) := by
        rw [sum_mul_lw B nn _ hsub1, sum_mul_lw B be _ hsub2]
      _ ≤ (WeightFamilies.rhoP B CRm T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size + (WeightFamilies.rhoP B CRm T c j ka : ℝ) * (WeightFamilies.PPv D large₂ Cq Aq * ka.size) :=
        add_le_add hnnS (mul_le_mul_of_nonneg_left hbeS hρ0)
      _ = 2 * (WeightFamilies.rhoP B CRm T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by ring

theorem quotCore (large₂ : SizeData₂ D) {CRm Ck Ch Ah Cq Aq : ℝ} (h7 : WeightFamilies.PointsLemma large₂ B CRm Ck Ch Ah Cq Aq)
    (hCR : 0 ≤ CRm) (hO : WeightFamilies.Obound B large₂ Ch Ah) (h1 : 1 ≤ j) (hj : j < D.R.m) (ka : WeightFamilies.Wt D j)
    (hn : ka.n = D.R.nV) (hLP : ka.LastPos) (hsz : ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b)
    (T c : ℝ) (hT : 0 < T) (hc : 0 < c) (hTc : T * c ≤ 1)
    (rq : ℕ) (hrq : rq = WeightFamilies.rhoP B CRm T c j ka) (th : Fin rq → B.Mlat j ka)
    (hspan : Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
      WeightFamilies.MggK B CRm T c j ka = ⊤)
    (hsup : ∀ i, WeightFamilies.meanLogSup B ((th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    (∀ la, WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka))) ≠ ⊤) ∧
    Summable (fun la => ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ) *
        lw B.KO la) ∧
    (∑' la, ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin rq => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ) *
        lw B.KO la) ≤ 2 * (rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  simp only [WeightFamilies.PointsLemma] at h7
  exact quotCoreE large₂ ka T c (h7 hCR hO j h1 hj ka hn hLP hsz T c hT hc hTc) rq hrq th hspan hsup

theorem two_T_sq_le_last {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1)
    (hi : i.1 + 1 = (D.R.sigW j).1) : 2 * T ^ 2 ≤ ka.aP τ i := by
  simp only [SetC] at h
  obtain ⟨-, -, -, h4, -, h6, -⟩ := h
  have h6' := h6 τ i hi
  have key : 2 * (T : ℝ) ^ 2 ≤ (ka.aP τ i : ℝ) := by linarith
  exact_mod_cast key

theorem lastPos_of_SetC {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : ka.LastPos := by
  have hT : 0 < T := by
    have h' := h
    simp only [SetC] at h'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := h'
    exact hT
  simp only [WeightFamilies.Wt.LastPos]
  intro τ i hi
  have h2 := two_T_sq_le_last h τ i hi
  have h3 : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ hT
  linarith

theorem DF_pos_of_SetC {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : 0 < DF wL := by
  have hh := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩ := hh
  have hp : 0 < (D.R.sigW j).1 := by
    have := D.R.m_add_three_le_k
    show 0 < D.R.k + j - 1
    omega
  have hτ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    unfold Ranks.f Ranks.n
    positivity
  obtain ⟨τ⟩ := hτ
  set i : Fin (D.R.sigW j).1 := ⟨(D.R.sigW j).1 - 1, by omega⟩ with hi
  have hi1 : i.1 + 1 = (D.R.sigW j).1 := by simp only [hi]; omega
  have h2 := two_T_sq_le_last h τ i hi1
  have h3 := hL.2.1 τ i
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  rw [if_neg hn] at h3
  unfold gapZ at h3
  rw [dif_neg hn] at h3
  have hTp : (0 : ℤ) < (Tp D j T : ℤ) := by unfold Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hTp.le] at h3
  have h4 : (1 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (Tp D j T : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hTp, one_mul]
    unfold Tp
    have e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast h2
    have e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hnW
    have e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
    push_cast
    nlinarith
  have h5 : 1 ≤ wL.aP τ i := by
    rw [← h3] at h4; exact_mod_cast h4
  unfold DF degP
  calc 0 < wL.aP τ i := h5
    _ ≤ ∑ i, wL.aP τ i := Finset.single_le_sum (f := fun i => wL.aP τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i := Nat.le_add_right _ _
    _ ≤ _ := Finset.single_le_sum (f := fun τ => (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)

theorem RRv_pos' (D : D7) (CR : ℝ) : 0 < WeightFamilies.RRv D CR := by
  simp only [WeightFamilies.RRv]
  apply Real.rpow_pos_of_pos
  simp only [Formalism.BasicNotions.Host.rdE]
  apply Real.rpow_pos_of_pos
  have h := NumberField.discr_ne_zero (K := D.host.E)
  exact abs_pos.mpr (Int.cast_ne_zero.mpr h)

theorem PPv_pos_of_PolyDom {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ} {ka : WeightFamilies.Wt D j}
    (h : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) : 0 < WeightFamilies.PPv D large₂ C2 A2 := by
  simp only [PolyDom] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -, -, h18⟩ := h
  linarith

theorem modulus_pos_of_third_hypothesis {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR Bx : ℝ} {wL : WeightFamilies.Wt D j} {T : ℕ}
    (h : H3 large₂ H C2 A2 CR Bx wL T) : (0 : ℝ) < qq D := by
  simp only [qq]
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  exact Nat.cast_pos.mpr (lt_min h0 h1)

theorem cc_pos_of {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp}
    {C2 A2 CR Bx Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (hS : SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0) (h3 : H3 large₂ H C2 A2 CR Bx wL T)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) : 0 < cc D large₂ C2 A2 CR wL := by
  have hDF := DF_pos_of_SetC hS
  have hRR := RRv_pos' D CR
  have hPP := PPv_pos_of_PolyDom hP
  have hq := modulus_pos_of_third_hypothesis h3
  have hD : (0 : ℝ) < (DF wL : ℝ) := by exact_mod_cast hDF
  simp only [cc]
  exact div_pos (mul_pos (mul_pos hRR hPP) (pow_pos hD 2)) hq

theorem T_mul_cc_le_one {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp}
    {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ} {ka wL : WeightFamilies.Wt D j} {T : ℕ}
    (h3 : H3 large₂ H C2 A2 CR 0 wL T)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    (T : ℝ) * cc D large₂ C2 A2 CR wL ≤ 1 := by
  have hg : (1 : ℝ) ≤ g0 D := by
    simp only [g0]
    have hm := D.R.two_le_m
    have hr : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]
      omega
    have h5 : (2 : ℕ) * 5 ^ 4 = 1250 := by norm_num
    have hr' : 1 ≤ 2 * 5 ^ 4 * D.R.r := by
      rw [h5]
      omega
    exact_mod_cast hr'
  have hq := modulus_pos_of_third_hypothesis h3
  have hRR := RRv_pos' D CR
  have hPP := PPv_pos_of_PolyDom hP
  simp only [H3] at h3
  obtain ⟨-, h2, -⟩ := h3
  simp only [pow_zero, Real.rpow_zero, one_mul] at h2
  have hA : 0 ≤ (T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hRR.le) hPP.le) (sq_nonneg _)
  have key : (T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 ≤ (qq D : ℝ) := by
    calc (T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2
        ≤ ((T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2) * (g0 D : ℝ) :=
          le_mul_of_one_le_right hA hg
      _ = (T : ℝ) * (g0 D : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 := by ring
      _ ≤ (qq D : ℝ) := h2
  simp only [cc]
  calc (T : ℝ) * (WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2 / (qq D : ℝ))
      = ((T : ℝ) * WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 * (DF wL : ℝ) ^ 2) / (qq D : ℝ) := by ring
    _ ≤ 1 := (div_le_one hq).mpr key

theorem quotSum {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    {Gc PH Prw Pet Pd : ℝ} (h1 : 1 ≤ j) (hj : j < D.R.m)
    (h7 : adm7 large₂ B K.CRm H.CK Ch Ah Cq Aq)
    (hH : Hyp large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData X ka wL wF)
    (hG : G.Tied large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Gc Prw Ch Ah K.Cf K.Af)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    (∀ la, WeightFamilies.lenAt B la (WeightFamilies.Qm B K.CRm T (cc D large₂ C2 A2 CR wL) j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin G.rq =>
        (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B K.CRm T (cc D large₂ C2 A2 CR wL) j ka))) ≠ ⊤) ∧
    Summable (fun la => ((WeightFamilies.lenAt B la (WeightFamilies.Qm B K.CRm T (cc D large₂ C2 A2 CR wL) j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin G.rq =>
        (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B K.CRm T (cc D large₂ C2 A2 CR wL) j ka)))).toNat : ℝ) * X.lN la) ∧
    (∑' la, ((WeightFamilies.lenAt B la (WeightFamilies.Qm B K.CRm T (cc D large₂ C2 A2 CR wL) j ka ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin G.rq =>
        (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B K.CRm T (cc D large₂ C2 A2 CR wL) j ka)))).toNat : ℝ) * X.lN la) ≤
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  have e : ∀ la, X.lN la = lw B.KO la := by
    intro la
    simp only [PJ.lN, lw]
  have hH' := hH
  simp only [Hyp] at hH'
  obtain ⟨-, hS, -, -, -, h3, -⟩ := hH'
  have hP' := hP
  simp only [PolyDom] at hP'
  obtain ⟨hCRm, -, -, -, -, hO, -⟩ := hP'
  have hS' := hS
  simp only [SetC] at hS'
  obtain ⟨hn, -, -, -, -, -, -, hsz, -, -, -, -, -, -, -, -, -, hT0, -⟩ := hS'
  simp only [GlobalFamilyData.Tied] at hG
  obtain ⟨-, -, -, -, -, -, -, -, -, hrq, -, hspan, hsup, -⟩ := hG
  have hT : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT0
  have hc := cc_pos_of hS h3 hP
  have hTc := T_mul_cc_le_one h3 hP
  have hLP := lastPos_of_SetC hS
  simp only [adm7] at h7
  have key := quotCore large₂ h7 (by linarith) hO h1 hj ka hn hLP hsz (T : ℝ) (cc D large₂ C2 A2 CR wL)
    hT hc hTc G.rq hrq G.th hspan hsup
  simp only [e]
  exact key

end Formalism.MainNotions.Gaps.EtaleWeightGaps
