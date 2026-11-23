import Mathlib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfRefinedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Module

namespace GlobalTheory.Survey.NumericBoundConstants

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem f_le_r (D : D7) : D.R.f ≤ D.R.r := by
  have h1 := D.R.f_le_k
  have h2 := D.R.two_le_m
  unfold Ranks.f Ranks.n Ranks.r
  omega

theorem row_r (D : D7) : 8 ≤ D.R.r := D.eight_le_f.trans (f_le_r D)

theorem row_rd (D : D7) : (D.R.f : ℝ) ^ 2 ≤ D.host.rdE := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  set a : ℝ := 4 * (D.R.t : ℝ) * D.R.r + 1 with ha
  have ha0 : 0 ≤ a := by positivity
  have hq : a ≤ D.host.q := by
    have := D.host.qd_big.1.le
    rw [ha]; exact_mod_cast this
  have hd : a ≤ D.host.d := by
    have := D.host.qd_big.2.le
    rw [ha]; exact_mod_cast this
  have hs : a ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha0).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by rw [sq]; exact mul_le_mul hq hd ha0 (by positivity))
  have hfr : (D.R.f : ℝ) ≤ D.R.r := by exact_mod_cast f_le_r D
  have hm : (D.R.f : ℝ) ^ 2 ≤ a := by
    have h2 := Num.Pm.r_le_alt_alt D
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have h3 : (D.R.f : ℝ) * D.R.f ≤ (D.R.t : ℝ) * D.R.r :=
      mul_le_mul (hfr.trans h2) hfr hf0 (Nat.cast_nonneg _)
    rw [ha]
    nlinarith
  exact hm.trans (hs.trans h1)

theorem row_DF {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : 3 ≤ DF wL := by
  obtain ⟨-, -, -, hh0, -, hlast, -, -, -, -, -, -, -, -, hL, -, -, -, -, h40, hTm, -⟩ := h
  have hp : 0 < (D.R.sigW j).1 := by
    have := D.R.m_add_three_le_k
    unfold Ranks.sigW; simp only; omega
  have hne : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    have := D.eight_le_f; omega
  obtain ⟨τ⟩ := hne
  let i : Fin (D.R.sigW j).1 := ⟨(D.R.sigW j).1 - 1, by omega⟩
  have hi : i.1 + 1 = (D.R.sigW j).1 := by simp only [i]; omega
  have h1 := hL.2.1 τ i
  rw [if_neg (by omega)] at h1
  unfold gapZ at h1
  rw [dif_neg (by omega)] at h1
  have h2 := hlast τ i hi
  have h3 : 2 * T ^ 2 ≤ ka.aP τ i := by
    have : (2 * (T : ℝ) ^ 2) ≤ (ka.aP τ i : ℝ) := by linarith
    exact_mod_cast this
  have hTp : (0 : ℤ) < (Tp D j T : ℕ) := by unfold Tp; positivity
  have h4 : (3 : ℤ) ≤ wL.aP τ i := by
    rw [h1, Int.fdiv_eq_ediv_of_nonneg _ hTp.le, Int.le_ediv_iff_mul_le hTp]
    unfold Tp
    zify at h3 h40 hTm
    push_cast
    nlinarith [Int.natCast_nonneg (WeightFamilies.dimY D j)]
  have h5 : 3 ≤ wL.aP τ i := by exact_mod_cast h4
  unfold DF degP
  calc 3 ≤ wL.aP τ i := h5
    _ ≤ ∑ i, wL.aP τ i := Finset.single_le_sum (f := fun i => wL.aP τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ ≤ (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i := Nat.le_add_right _ _
    _ ≤ _ := Finset.single_le_sum (f := fun τ => (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)

theorem numeric_bounds_constants_pow_twelve (f m r n Z C : ℝ) (hf : 1 ≤ f) (hm : 1 ≤ m) (hr : 1 ≤ r) (hn0 : 0 ≤ n) (hm4 : m ^ 4 ≤ f) (hZ : f * r ≤ Z)
    (hZ0 : 1000 ≤ Z) (hC : 1 ≤ C) (hn : n ≤ C * Z ^ 4) :
    16200 * Real.pi * n * m ^ 4 * (2 * f * m) ^ 4 ≤ C * Z ^ 12 ∧
    (2 * f * m) ^ 4 * n + 2 * (2 * f * m) ^ 3 ≤ C * Z ^ 12 ∧ r * (2 * f * m) ^ 3 ≤ C * Z ^ 12 := by
  have hfZ : f ≤ Z := le_trans (le_mul_of_one_le_right (by linarith) hr) hZ
  have hrZ : r ≤ Z := le_trans (le_mul_of_one_le_left (by linarith) hf) hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hm4Z : m ^ 4 ≤ Z := hm4.trans hfZ
  have a4 : (2 * f * m) ^ 4 ≤ 16 * Z ^ 5 := by
    calc (2 * f * m) ^ 4 = 16 * (f ^ 4 * m ^ 4) := by ring
      _ ≤ 16 * (Z ^ 4 * Z) := by gcongr
      _ = 16 * Z ^ 5 := by ring
  have a3 : (2 * f * m) ^ 3 ≤ 16 * Z ^ 5 :=
    (pow_le_pow_right₀ (by nlinarith) (by norm_num)).trans a4
  have hZ2 : 1100000 ≤ Z ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hZ0 3)
  have hZ2' : 1000000 ≤ Z ^ 2 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hZ0 2)
  have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
  have hpi0 := Real.pi_pos.le
  have hCZ : Z ^ 9 ≤ C * Z ^ 9 := le_mul_of_one_le_left (by positivity) hC
  have h59 : Z ^ 5 ≤ Z ^ 9 := pow_le_pow_right₀ hZ1 (by norm_num)
  have h69 : Z ^ 6 ≤ Z ^ 9 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hbig : 1100000 * (C * Z ^ 9) ≤ C * Z ^ 12 := by
    calc 1100000 * (C * Z ^ 9) ≤ Z ^ 3 * (C * Z ^ 9) := by gcongr
      _ = _ := by ring
  have h9 : 0 ≤ C * Z ^ 9 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc 16200 * Real.pi * n * m ^ 4 * (2 * f * m) ^ 4 ≤ 16200 * 3.15 * (C * Z ^ 4) * Z * (16 * Z ^ 5) := by gcongr
      _ = 816480 * (C * Z ^ 10) := by ring
      _ ≤ Z ^ 2 * (C * Z ^ 10) := by gcongr; linarith
      _ = _ := by ring
  · have : (2 * f * m) ^ 4 * n ≤ 16 * (C * Z ^ 9) := by
      calc (2 * f * m) ^ 4 * n ≤ 16 * Z ^ 5 * (C * Z ^ 4) := by gcongr
        _ = _ := by ring
    linarith
  · have : r * (2 * f * m) ^ 3 ≤ 16 * Z ^ 6 := by
      calc r * (2 * f * m) ^ 3 ≤ Z * (16 * Z ^ 5) := by gcongr
        _ = _ := by ring
    linarith

theorem page_bound_le_of_constants {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR : ℝ} {nW : ℕ}
    (hPg : PageAt large₂ C2 A2) (ht : TieC K H Ch Ah Cq Aq C2 A2 CR) (hd : DomAt D large₂ j nW H.C1) :
    flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
  rw [ht.1] at hd
  have hA : 12 ≤ A2 := ht.2.2.2.2.2.2.2.1
  have hC : 1000 ≤ C2 := hd.1
  have hZe : Zb D large₂ = zBase large₂ := rfl
  have hZ0 : 1000 ≤ zBase large₂ := by
    rw [← hZe]
    exact hC.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hd.2.1)
  have hn : (nW : ℝ) ≤ C2 * zBase large₂ ^ 4 := by
    refine le_trans ?_ hd.2.2.2.2.2.2.2.2.1
    unfold sizeConstantAtParamsWeight
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  obtain ⟨a, b, c⟩ := numeric_bounds_constants_pow_twelve D.R.f D.R.m D.R.r nW (zBase large₂) C2 (by linarith [Num.Pm.two_le_f D])
    (by linarith [Num.Pm.two_le_m D]) (by linarith [Num.Pm.six_le_r D]) (Nat.cast_nonneg _) (lift_index_pow_four_le_degree hPg)
    (Num.Pm.fr_le_Z large₂) hZ0 (by linarith) hn
  have hP : C2 * zBase large₂ ^ 12 ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hA)
  exact max_le (a.trans hP) (max_le (b.trans hP) (c.trans hP))

theorem pageSupp_iff {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR Bx CT : ℝ}
    {S : Scal B} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) (ht : TieC K H Ch Ah Cq Aq C2 A2 CR)
    (hPg : PageAt large₂ C2 A2) :
    PageSupp D large₂ B C2 A2 nW S wL ↔ ∀ σ : B.KO →+* ℂ,
      (DF wL : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (S.sW : B.KO)‖ := by
  refine ⟨fun h => h.2.1, fun h => ⟨?_, h, row_rd D, row_r D, row_DF hH.2.1⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hH.2.1
  exact page_bound_le_of_constants hPg ht hd

theorem not_pageSupp_min {large₂ : SizeData₂ D} {C2 A2 : ℝ} {nW : ℕ} {S : Scal B} {wL : WeightFamilies.Wt D j}
    (hS : S.sW = ((qq D : ℕ) : 𝓞 B.KO) ^ DF wL) :
    (∀ σ : B.KO →+* ℂ, (DF wL : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (S.sW : B.KO)‖) ∧
      ¬ PageSupp D large₂ B C2 A2 nW S wL := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  have hne := D.host.g_ne
  have hq : 2 ≤ qq D := le_min h0 h1
  have hq' : (1 : ℝ) ≤ qq D := by exact_mod_cast (by omega : 1 ≤ qq D)
  have hlog : ∀ σ : B.KO →+* ℂ, Real.log ‖σ (S.sW : B.KO)‖ = (DF wL : ℝ) * Real.log (qq D) := fun σ => by
    rw [hS]; simp
  refine ⟨fun σ => ?_, ?_⟩
  · rw [hlog]
    have := Real.log_nonneg hq'
    have : (0 : ℝ) ≤ DF wL := Nat.cast_nonneg _
    nlinarith
  · rintro ⟨-, h, -, -, h3⟩
    obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
    have h4 := h σ
    rw [hlog] at h4
    have hlt : qq D * qq D < D.host.g 0 * D.host.g 1 := by
      unfold qq
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le]; nlinarith
      · rw [min_eq_right h.le]; nlinarith
    have hlt' : (qq D : ℝ) * qq D < (D.host.g 0 : ℝ) * D.host.g 1 := by exact_mod_cast hlt
    have h5 := Real.log_lt_log (by positivity) hlt'
    rw [Real.log_mul (by positivity) (by positivity)] at h5
    have h6 : (3 : ℝ) ≤ DF wL := by exact_mod_cast h3
    nlinarith

theorem rhoP_top (hj : D.R.m ≤ j) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) : WeightFamilies.rhoP B CR T c j ka = 0 := by
  have h0 : WeightFamilies.rho D j = 0 := by unfold WeightFamilies.rho Ranks.sigW; simp only; omega
  have ht : WeightFamilies.MggK B CR T c j ka = ⊤ := by
    unfold WeightFamilies.MggK
    simp only [iInf_eq_top]
    rintro cu χ ⟨xi, -, hxi, -⟩
    exact absurd (funext fun i => absurd i.2 (by omega)) hxi
  have : WeightFamilies.MggIn B CR T c j ka = ⊤ := by unfold WeightFamilies.MggIn; rw [ht]; rfl
  have : Subsingleton (WeightFamilies.Qm B CR T c j ka) := Submodule.Quotient.subsingleton_iff.2 this
  exact Module.finrank_zero_of_subsingleton

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem conclAtM_iff {large₂ : SizeData₂ D} {S : Scal B} {T : ℕ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : D.R.m ≤ j) (hD : DepthAtM X S wL nus) : ConclAtM large₂ X S ka wL wF T nus ↔
      Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2) :=
  ⟨fun h => h hj hD, fun h _ _ => h⟩

theorem shareRho_top (hj : D.R.m ≤ j) {large₂ : SizeData₂ D} {S : Scal B} {G : GlobalFamilyData X ka wL wF} {CRm c Ch Ah : ℝ} {T d : ℕ}
    (hQ : G.TiedQ large₂ S CRm T c Ch Ah) (h : ShareRhoT (D := D) (j := j) T G.rz G.rq d) :
    ShareRho (D := D) (j := j) T G.rz d := by
  have : G.rq = 0 := hQ.1.trans (rhoP_top hj _ _ _ _)
  unfold ShareRhoT at h
  rw [this] at h
  simpa [ShareRho] using h

theorem conclAtM_of_local (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (lA : LatAt B j ka) (sA : SupBoundByL2AtWeight large₂ B j ka K.CG K.AG) (mA : LAMwAt large₂ B j ka K.CL K.AL)
    (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (tW : G.TiedW S Gc Prw) (tTh : G.TiedTh S Gc) (tZ : G.TiedZ S T Gc)
    (tQ : G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah)
    (dH : DeepHerm (X j h1 h2) ka) (dS : DeepSubMul (X j h1 h2)) (dL : DeepLogD (X j h1 h2) ka Pd)
    (pG : PageGd4 (X j h1 h2) ka large₂ K.CG K.AG Pd)
    (sRd : ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)))
    (sRho : ShareRhoT (D := D) (j := j) T G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)))
    (hP : PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (iZ : ∀ la, InContainZ G la S T) (iM : ∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL))
    (Qf : ∀ la, LocalPointData G la) (iB : ∀ la, InBasis G la) (iC : ∀ la, (Qf la).InCurve) (iT : ∀ la, (Qf la).InTie S)
    (iL : ∀ la, (Qf la).InLiftC S Gc Prw T) (hHt : Heights Qf Gc PH Prw Pet) :
    ConclAtM large₂ (X j h1 h2) S ka wL wF T nus := by
  intro hj hD
  refine theorem_zero_of_named_inputs large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA
    (fun h => absurd h (by omega)) G Gc PH Prw Pet Pd Qf tW tTh tZ tQ (fun h => absurd h (by omega)) dH dS dL pG sRd
    (shareRho_top hj tQ sRho) ?_ hP iB iC iT iL iZ iM (fun la y => ⟨fun h => absurd h (by omega), fun _ => hD la y⟩) hHt
  unfold ShareRhoP
  have e : G.rq = 0 := tQ.1.trans (rhoP_top hj _ _ _ _)
  rw [e, Nat.cast_zero]
  positivity

theorem not_depthAtM_zero {S : Scal B} (hS : S.sW = 0) {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    {la : HeightOneSpectrum (𝓞 B.KO)} (y : X.Pt la) : ¬ DepthAtM X S wL nus := by
  intro h
  have h1 := h la y
  have : X.depth S.sW wL la y = ⊤ := by
    unfold PJ.depth
    simp only [iInf_eq_top]
    rintro F ⟨F', -, rfl⟩
    simp [hS, X.vAt_zero]
  rw [this] at h1
  exact absurd h1 (by simp)

theorem combBound4_iet_zero {G : GlobalFamilyData X ka wL wF} (hi : G.iet = 0) {Qf : ∀ la, LocalPointData G la} {S : Scal B} {c c' : ℝ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} (h : CombBound4 G Qf S c nus) : CombBound4 G Qf S c' nus := by
  intro la ζ
  refine ⟨(h la ζ).1, fun hne => ?_⟩
  have := (h la ζ).2 hne
  have e : (G.iet : ℝ) = 0 := by exact_mod_cast hi
  simpa [e] using this

end GlobalTheory.Survey.NumericBoundConstants
