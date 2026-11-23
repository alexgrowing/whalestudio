import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.LatticeGerm

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def RateAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b s : ℕ) (w : List C.Letter)
    (h : C.LPt) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ a a', TBB.NP p nn F (b + s - 1) w a a' = ⟪Vec a, Vec a'⟫_ℂ) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ Cst : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖GermRealisation.utOf s (GermFibreKernels.vOf 1 Vec) h x D -
        PBK.mainD s cStd ((-1) ^ (s + 1)) (GermFibreKernels.btOf s ((Real.pi ^ (2 * (s - 1)))⁻¹) Vec h) x D‖ ≤ Cst * ‖x‖⁻¹

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in

theorem slv_congr_group {k r : ℕ} (T : D.LevTower k r Wp Wq) {F F' : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hFF : ∀ g ∈ B.GV k r, F g = F' g) (i : ℕ) (hi : i ≤ r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a i)
    (e : Wd.Ix (Fin w.length)) : ∀ g ∈ B.GV k (r - i), KB.slv T F i hi w a ha.2 e g = KB.slv T F' i hi w a ha.2 e g := by
  intro g hg
  have hp : D.ptSize a ≤ r := by rw [ha.2]; exact hi
  have hd0 : ∀ q, D.ptDiag a q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a ha.1 q q.2
  unfold KB.slv
  simp only [D.castF]
  unfold D.sliceAt
  rw [dif_pos hp, dif_pos hp]
  unfold U.PhiFun
  congr 1
  funext ξ
  congr 1
  simp only [D.castF]
  refine CutEXUw.uwG_congrG _ _ i hi isOpen_univ (fun x _ hx => hFF x hx) w e _ (Set.mem_univ _) ?_
  refine PBE.castM_GV _ ?_
  exact (LeftFubiniLemmas.gaXi_dom _ _ hd0 ξ _ (PBE.castM_GV _ hg)).1

theorem rr_congr_group (p : KB.Pl P Wp Wq) {F F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hFF : ∀ g ∈ B.GV P.k P.r, F g = F' g) (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (a a' : C.LPt) :
    p.RR F i w a a' = p.RR F' i w a a' := by
  by_cases h : D.IsLocPt a i ∧ D.IsLocPt a' i
  · rw [PBL.rr_eq_form p F i hi w a a' h.1 h.2, PBL.rr_eq_form p F' i hi w a a' h.1 h.2]
    exact PBG.formLev_congrGV p.T _ ⟨i, by omega⟩ w _ _ _ _
      (fun e => slv_congr_group p.T hFF i hi w a h.1 e) (fun e => slv_congr_group p.T hFF i hi w a' h.2 e)
  · rw [PBL.rr_zero_of_not p F i w a a' h, PBL.rr_zero_of_not p F' i w a a' h]

theorem exists_cut_rr (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) :
    ∃ (χ : ℝ → ℝ) (ε : ℝ), C6.IsCut0 χ ∧ 0 < ε ∧ ∀ i, i ≤ P.r → ∀ (w : List C.Letter) (a a' : C.LPt),
      p.RR F i w a a' = p.RR (D.cutF p.T.base χ F ε) i w a a' := by
  obtain ⟨ε, hε, hG⟩ := hF.2.2
  have hχ := Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation
  exact ⟨_, ε, hχ, hε, fun i hi w a a' => rr_congr_group p
    (fun g hg => (CutBP.cutF_eq_on_gv p.T.base hχ hG hε le_rfl g hg).symm) i hi w a a'⟩

theorem normC_pos {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y) (w : List C.Letter) : 0 < TBB.normC nn w := by
  unfold TBB.normC
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
  exact hnn _

def lam (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) (a : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) a) / √(TBB.normC nn w)

theorem np_eq (p : KB.Pl P Wp Wq) {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (w : List C.Letter) (a a' : C.LPt) :
    TBB.NP p nn F i w a a' = ((lam p nn w a * lam p nn w a' : ℝ) : ℂ) * p.RR F i w a a' := by
  unfold TBB.NP lam
  rw [div_mul_div_comm, Real.mul_self_sqrt (normC_pos hnn w).le]

def co (s : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
  | some z => -(G.psi cStd ((s : ℂ) * z * x) * ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * Real.pi ^ (s - 1) : ℝ) : ℂ))

theorem inv_sqrt_pi_pow (n : ℕ) : (√((Real.pi ^ (2 * n))⁻¹))⁻¹ = Real.pi ^ n := by
  rw [Real.sqrt_inv, inv_inv, pow_mul', Real.sqrt_sq (pow_nonneg Real.pi_pos.le _)]

theorem root_ne_zero {s : ℕ} (hs : 2 ≤ s) {D z : ℂ} (hD : D ≠ 0) (hz : z ∈ G.rootSet s ((-1) ^ (s + 1) * D)) :
    z ≠ 0 := by
  rintro rfl
  rw [FormNormSumIdentities.mem_rootSet4 (by omega), zero_pow (by omega)] at hz
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hD hz.symm

theorem germ_diff_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : ℕ) (hs : 2 ≤ s) (Vec : C.LPt → H) (h : C.LPt) (x D : ℂ) (hD : D ≠ 0) :
    GermRealisation.utOf s (GermFibreKernels.vOf 1 Vec) h x D -
                   PBK.mainD s cStd ((-1) ^ (s + 1)) (GermFibreKernels.btOf s ((Real.pi ^ (2 * (s - 1)))⁻¹) Vec h) x D =
      ∑ j ∈ Finset.insertNone (G.rootSet s ((-1) ^ (s + 1) * D)), co s x j • Vec (FormNormSumIdentities.PPt s h x D j) := by
  rw [Finset.sum_insertNone]
  unfold GermRealisation.utOf GermFibreKernels.vOf GermRealisation.ptX PBK.mainD
  simp only [co, FormNormSumIdentities.PPt, Real.sqrt_one, inv_one, Complex.ofReal_one, one_smul]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
  · refine Finset.sum_congr rfl fun z hz => ?_
    simp only [GermFibreKernels.btOf, if_neg (root_ne_zero hs hD hz), smul_smul, neg_smul, inv_sqrt_pi_pow]

theorem conj_psi_cStd (w : ℂ) : conj (G.psi cStd w) = G.psi U.betaU w := by
  rw [FormNormSumIdentities.psi_conj]
  unfold G.psi U.betaU
  simp

theorem psi_cStd (σ z : ℂ) : G.psi cStd (σ * z) = P5.fsv σ z := by
  unfold G.psi P5.fsv cStd
  congr 1
  rw [← map_mul, Complex.sub_conj]
  simp [Complex.mul_re]
  ring

theorem isLocPt_germPt (s : ℕ) (hs : 2 ≤ s) (b : ℕ) (hb : 1 ≤ b) (h : C.LPt) (hh : D.IsLocPt h (b - 1))
    (x Dc : ℂ) (hx : x ≠ 0) (hD : Dc ≠ 0) (j : Option ℂ)
    (hj : j ∈ Finset.insertNone (G.rootSet s ((-1) ^ (s + 1) * Dc))) :
    D.IsLocPt (FormNormSumIdentities.PPt s h x Dc j) (b + s - 1) := by
  cases j with
  | none =>
    exact FormNormSumIdentities.isLocPt_PPt s hs b hb h hh.2 hh.1 x Dc hx hD none (by simp)
  | some z =>
    have hz0 : z ≠ 0 := root_ne_zero hs hD (Finset.mem_insertNone.1 hj z rfl)
    exact LastBlockContinuity.isLocPt_app hh.1 (by omega) hz0 (by rw [hh.2]; omega)

def nHead (k r : ℕ) (h : C.LPt) : ℝ := C.nAux k r 0 (fun _ _ => 1) 1 h

theorem nHead_nonneg (k r : ℕ) (h : C.LPt) : 0 ≤ nHead k r h :=
  GermRateSplit.weight_product_nonneg k r _ (fun _ _ => zero_le_one) 1 h

theorem nPt_append (k r : ℕ) (TT : ℝ) (h L : C.LPt) (hh : D.ptSize h ≤ r) :
    TBB.nPt k r TT (h ++ L) =
      nHead k r h * C.nAux k r (D.ptGG TT (h ++ L)) (fun _ _ => 1) (1 + D.ptSize h) L := by
  unfold TBB.nPt nHead
  rw [GermRateSplit.weight_product_append, GermRateSplit.weight_product_germ_indep k r _ 0 _ 1 h (by omega)]

theorem sqrt_nPt_long (k r : ℕ) (TT : ℝ) (h : C.LPt) (m e : ℕ) (z : ℂ) (hh : D.ptSize h + (m + 2) ≤ r + 1)
    (he : (e : ℤ) = C.Mlev k r (D.ptSize h + (m + 2)) + m - 1) :
    √(TBB.nPt k r TT (h ++ [(m + 2, z)])) = √(nHead k r h) * ‖z‖ ^ ((m + 2) * e) := by
  rw [nPt_append k r TT h _ (by omega)]
  simp only [C.nAux]
  rw [if_neg (by omega), show 1 + D.ptSize h + (m + 2) - 1 = D.ptSize h + (m + 2) by omega,
    show 2 * ((m + 2 : ℕ) : ℤ) * (C.Mlev k r (D.ptSize h + (m + 2)) + ((m + 2 : ℕ) : ℤ) - 3) =
      ((2 * ((m + 2) * e) : ℕ) : ℤ) by push_cast; rw [he]; ring, zpow_natCast, one_mul, mul_one,
    Real.sqrt_mul (nHead_nonneg k r h), GermRateSplit.sqrt_pow_two_mul _ (norm_nonneg _)]

theorem sqrt_nPt_pair_low (k r : ℕ) (TT : ℝ) (h : C.LPt) (m M : ℕ) (t c : ℂ) (hh : D.ptSize h + (m + 2) ≤ r)
    (hM : (M : ℤ) = C.Mlev k r (D.ptSize h + (m + 2))) (hM2 : 2 ≤ M) :
    √(TBB.nPt k r TT (h ++ [(m + 1, t), (1, c)])) =
      √(nHead k r h) * (‖t‖ ^ ((m + 1) * (M + m)) * ‖c‖ ^ (M - 2)) := by
  rw [nPt_append k r TT h _ (by omega)]
  simp only [C.nAux]
  rw [if_neg (by omega), if_neg (by omega), show 1 + D.ptSize h + (m + 1) - 1 = D.ptSize h + (m + 1) by omega,
    show 1 + D.ptSize h + (m + 1) + 1 - 1 = D.ptSize h + (m + 2) by omega,
    show 2 * ((m + 1 : ℕ) : ℤ) * (C.Mlev k r (D.ptSize h + (m + 1)) + ((m + 1 : ℕ) : ℤ) - 3) =
      ((2 * ((m + 1) * (M + m)) : ℕ) : ℤ) by push_cast; rw [hM]; unfold C.Mlev; push_cast; ring,
    show 2 * ((1 : ℕ) : ℤ) * (C.Mlev k r (D.ptSize h + (m + 2)) + ((1 : ℕ) : ℤ) - 3) =
      ((2 * (M - 2) : ℕ) : ℤ) by rw [← hM]; push_cast [Nat.cast_sub hM2]; ring,
    zpow_natCast, zpow_natCast, one_mul, one_mul, mul_one,
    Real.sqrt_mul (nHead_nonneg k r h), Real.sqrt_mul (by positivity),
    GermRateSplit.sqrt_pow_two_mul _ (norm_nonneg _), GermRateSplit.sqrt_pow_two_mul _ (norm_nonneg _)]

def qPt (m : ℕ) (x D : ℂ) : Option ℂ → (ℂ × ℂ) ⊕ ℂ
  | none => Sum.inl (x⁻¹, x ^ (m + 1) * D)
  | some z => Sum.inr z

theorem ptG_qPt (h : C.LPt) (m : ℕ) (x D : ℂ) (j : Option ℂ) :
    FormNormSumIdentities.PPt (m + 2) h x D j = FormNormSumIdentities.ptG h m (qPt m x D j) := by
  cases j <;> rfl

theorem rate_low (p : KB.Pl P Wp Wq) {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s) (hi : b + s - 1 ≤ P.r) (w : List C.Letter)
    (h : C.LPt) (hh : D.IsLocPt h (b - 1)) : RateAt p nn F b s w h := by
  intro H _ _ _ Vec hVec K hK hK0
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  obtain ⟨χ, ε, hχ, hε, hcut⟩ := exists_cut_rr p hF
  have hsz : D.ptSize h + (m + 2) = b + (m + 2) - 1 := by rw [hh.2]; omega
  obtain ⟨V, i1, i2, i3, Bf, Φ, Cp, Cst, hCp, hBf, hker, hgerm⟩ :=
    germ_at_place Wp Wq P p.T (M.sgn P p.l0) w F χ ε h m (b + (m + 2) - 1) hi hsz hF.1 hF.2.1 hχ hε
      p.hl.2.2 ⟨hh.1, rfl⟩ K hK hK0
  set M := U.Mlev P.k (P.r - (b + (m + 2) - 1)) with hMdef
  have hM : (M : ℤ) = C.Mlev P.k P.r (D.ptSize h + (m + 2)) := by
    rw [hsz, hMdef]; unfold U.Mlev C.Mlev; push_cast [Nat.cast_sub hi]; ring
  have hM3 : 3 ≤ M := by rw [hMdef]; unfold U.Mlev; omega
  set μ₀ : ℝ := √(nHead P.k P.r h) / √(TBB.normC nn w) * FormNormSumIdentities.kapB m with hμ₀
  refine ⟨Cp * |μ₀| * Cst, fun x hx D hD => ?_⟩
  have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
  have hxp : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
  rw [germ_diff_eq (m + 2) hs Vec h x D hD0]
  have hok : ∀ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D)), FormNormSumIdentities.okG m K (qPt m x D j) := by
    intro j hj
    cases j with
    | none =>
      refine ⟨inv_ne_zero hx, ?_⟩
      have : x ^ (m + 1) * D * x⁻¹ ^ (m + 1) = D := by rw [inv_pow]; field_simp
      simp only [this]; exact hD
    | some z => exact ⟨D, hD, (FormNormSumIdentities.mem_rootSet4 (by omega)).1 (Finset.mem_insertNone.1 hj z rfl)⟩
  have hyy : ∀ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D)),
      ∀ l ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D)),
      TBB.NP p nn F (b + (m + 2) - 1) w (FormNormSumIdentities.PPt (m + 2) h x D j) (FormNormSumIdentities.PPt (m + 2) h x D l) =
        Bf (((lam p nn w (FormNormSumIdentities.PPt (m + 2) h x D j) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qPt m x D j))
          (((lam p nn w (FormNormSumIdentities.PPt (m + 2) h x D l) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qPt m x D l)) := by
    intro j hj l hl
    have hPj := isLocPt_germPt (m + 2) hs b hb h hh x D hx hD0 j hj
    have hPl := isLocPt_germPt (m + 2) hs b hb h hh x D hx hD0 l hl
    rw [np_eq p hnn, hcut _ hi, PBL.rr_eq_form p _ _ hi w _ _ hPj hPl]
    unfold KB.Pl.form
    rw [FormNormSumIdentities.slv_congr _ _ _ _ _ (ptG_qPt h m x D j) _ (by rw [FormNormSumIdentities.ptSize_ptG, hsz]),
      FormNormSumIdentities.slv_congr _ _ _ _ _ (ptG_qPt h m x D l) _ (by rw [FormNormSumIdentities.ptSize_ptG, hsz]),
      hker _ _ (hok j hj) (hok l hl)]
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hle := FormNormSumIdentities.norm_sum_le_of_form (TBB.NP p nn F (b + (m + 2) - 1) w) Vec hVec Bf Cp hCp hBf _
    (co (m + 2) x) (FormNormSumIdentities.PPt (m + 2) h x D) _ hyy
  have hcs : ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D)), conj (co (m + 2) x j) •
      (((lam p nn w (FormNormSumIdentities.PPt (m + 2) h x D j) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qPt m x D j)) =
      (μ₀ : ℂ) • (U.uD U.betaU m M Φ x⁻¹ D - U.aD U.betaU m M Φ x⁻¹ D) := by
    rw [Finset.sum_insertNone, smul_sub, sub_eq_add_neg]
    congr 1
    · show conj (((‖x‖ ^ (m + 1) : ℝ) : ℂ)) • (((lam p nn w (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * D)]) : ℝ) : ℂ) •
        (((FormNormSumIdentities.kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ x⁻¹ (x ^ (m + 1) * D))) = _
      unfold U.uD lam
      have hc : D / x⁻¹ ^ (m + 1) = x ^ (m + 1) * D := by rw [inv_pow]; field_simp
      rw [hc, Complex.conj_ofReal, smul_smul, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, sqrt_nPt_pair_low P.k P.r _ h m M _ _ (by omega) hM (by omega), hμ₀]
      congr 2
      simp only [norm_inv, inv_pow, inv_inv]
      ring
    · unfold U.aD G.mainTerm
      rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := root_ne_zero hs hD0 hz
      have hzs : ‖D‖ = ‖z‖ ^ (m + 2) := by
        rw [← norm_pow, (FormNormSumIdentities.mem_rootSet4 (by omega)).1 hz]; simp
      simp only [co, qPt, FormNormSumIdentities.yG, FormNormSumIdentities.PPt, smul_smul, ← neg_smul]
      congr 1
      obtain ⟨e, he⟩ : ∃ e, M = e + 3 := ⟨M - 3, by omega⟩
      unfold lam
      rw [map_neg, map_mul, Complex.conj_ofReal, conj_psi_cStd,
        sqrt_nPt_long P.k P.r _ h m (e + m + 2) z (by omega) (by rw [← hM, he]; push_cast; ring),
        show m + 2 - 1 = m + 1 from rfl, hzs, hμ₀, he, show e + 3 - 2 = e + 1 from rfl, div_inv_eq_mul]
      have hpi : FormNormSumIdentities.kapB m = Real.pi ^ (m + 1) * Real.pi ^ ((m + 2) * (m + 1) / 2) := by
        unfold FormNormSumIdentities.kapB
        rw [← pow_add]
        congr 1
        rw [show (m + 1) * (m + 4) = (m + 2) * (m + 1) + 2 * (m + 1) by ring, Nat.add_mul_div_left _ _ two_pos]
        ring
      rw [hpi]
      have hzn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
      have hm2 : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
      push_cast
      field_simp
      ring
  rw [hcs, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hle
  have hg' := hgerm x⁻¹ D (inv_ne_zero hx) hD
  rw [norm_inv] at hg'
  refine hle.trans ?_
  calc Cp * (|μ₀| * ‖_‖) ≤ Cp * (|μ₀| * (Cst * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' (abs_nonneg _)) hCp
    _ = _ := by ring

theorem germ_core_std (m q : ℕ) (σh : Equiv.Perm (Fin q)) (dh : Fin q → ℂ) (hdh : ∀ i, dh i ≠ 0)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Φ0 : G.Mat (q + (m + 1 + 1)) → V) (hΦ0 : PBJ.KCls Φ0)
    (K : Set ℂ) (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) (ρ : ℂ → ℂ → ℝ) (R0 L : ℝ)
    (hρ : ∀ x D : ℂ, x ≠ 0 → D ∈ K →
      G.OmBlock U.betaU (m + 1) (U.PhiTop (p := q) (s := m + 1 + 1) U.betaU σh dh Φ0) x⁻¹ (x ^ (m + 1) * D) ≠ 0 →
      |ρ x D| ≤ R0 ∧ |ρ x D - 1| ≤ L * ‖x‖⁻¹ ^ (2 * (m + 1))) :
    ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x D : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := q) (s := m + 1 + 1) U.betaU σh dh Φ0) x⁻¹ (x ^ (m + 1) * D) -
        ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D),
          (((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * G.psi U.betaU (((m : ℂ) + 2) * z * x)) •
            G.OmLong U.betaU (m + 1) (U.PhiTop (p := q) (s := m + 1 + 1) U.betaU σh dh Φ0) z‖ ≤ C * ‖x‖⁻¹ := by
  classical
  set l1 : ℂ := Complex.I ^ m with hl1def
  set l2 : ℂ := Complex.I ^ (m + 1) with hl2def
  have hl1 : l1 ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hl2 : l2 ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hn1 : ‖l1‖ = 1 := by simp [hl1def]
  have hl : l2 ^ (m + 2) = (-1) ^ (m + 3) * l1 ^ (m + 1) := by
    rw [hl2def, hl1def, ← pow_mul, ← pow_mul, show (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) by ring,
      pow_add Complex.I, pow_mul Complex.I 2 (m + 1), Complex.I_sq]
    ring
  have hq : l2 / l1 = Complex.I := by rw [hl2def, hl1def, pow_succ, mul_div_cancel_left₀ _ hl1]
  have hψ : ∀ w : ℂ, G.psi U.betaU (l2 / l1 * w) = conj (G.psi ((2 : ℝ) : ℂ) w) := by
    intro w
    rw [FormNormSumIdentities.psi_conj, hq]
    unfold G.psi U.betaU cStd
    congr 3
    simp [Complex.mul_re, Complex.mul_im]
  have hl1p : l1 ^ (m + 1) ≠ 0 := pow_ne_zero _ hl1
  obtain ⟨C, hC⟩ := GermRateSplit.germ_core m q σh dh hdh Φ0 hΦ0 l1 l2 hl1 hl 2 hψ ((fun D => D / l1 ^ (m + 1)) '' K)
    (hK.image (continuous_id.div_const _))
    (by rintro ⟨D, hD, h0⟩; exact hK0 ((div_eq_zero_iff.1 h0).resolve_right hl1p ▸ hD))
    (fun x D => ρ (x / l1) (l1 ^ (m + 1) * D)) R0 L (by
      rintro x _ hx ⟨D, hD, rfl⟩ hOm
      have e1 : l1 * x⁻¹ = (x / l1)⁻¹ := by field_simp
      have e2 : x ^ (m + 1) * (D / l1 ^ (m + 1)) = (x / l1) ^ (m + 1) * D := by rw [div_pow]; field_simp
      have e3 : l1 ^ (m + 1) * (D / l1 ^ (m + 1)) = D := by field_simp
      simp only [e1, e2] at hOm
      have := hρ (x / l1) D (div_ne_zero hx hl1) hD hOm
      rw [norm_div, hn1, div_one] at this
      simpa only [e3] using this)
  refine ⟨C, fun x hx D hD => ?_⟩
  have h1 := hC (l1 * x) (mul_ne_zero hl1 hx) (D / l1 ^ (m + 1)) ⟨D, hD, rfl⟩
  have e1 : l1 * (l1 * x)⁻¹ = x⁻¹ := by field_simp
  have e2 : (l1 * x) ^ (m + 1) * (D / l1 ^ (m + 1)) = x ^ (m + 1) * D := by rw [mul_pow]; field_simp
  have e3 : l1 ^ (m + 1) * (D / l1 ^ (m + 1)) = D := by field_simp
  have e4 : l1 * x / l1 = x := by field_simp
  have hR : G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D) =
      (G.rootSet (m + 2) (D / l1 ^ (m + 1))).image (fun z => l2 * z) := by
    ext z
    rw [FormNormSumIdentities.mem_rootSet4 (by omega), Finset.mem_image]
    constructor
    · intro hz
      refine ⟨z / l2, ?_, by field_simp⟩
      rw [FormNormSumIdentities.mem_rootSet4 (by omega), div_pow, hz, hl]
      have : ((-1 : ℂ)) ^ (m + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
    · rintro ⟨y, hy, rfl⟩
      rw [FormNormSumIdentities.mem_rootSet4 (by omega)] at hy
      rw [mul_pow, hy, hl]
      field_simp
  rw [e1, e2, e3, e4, norm_mul, hn1, one_mul] at h1
  rw [hR, Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hl2 hab)]
  convert h1 using 6 with z hz
  rw [← hψ]
  congr 1
  field_simp

def omTop (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) (a : C.LPt) : ℝ :=
  lam p nn w a * √(Top.wPt (TBB.TTp p) P.r a ^ w.length)

theorem np_top_gram (p : KB.Pl P Wp Wq) {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (L : I → (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef p.T.base (Fi i)) ∧
      ∀ a a' : C.LPt, D.IsLocPt a (P.r + 1) → D.IsLocPt a' (P.r + 1) → TBB.NP p nn F (P.r + 1) w a a' =
        ∑ i, (c i : ℂ) * ⟪(omTop p nn w a' : ℂ) • L i (p.V (Fi i) a'), (omTop p nn w a : ℂ) • L i (p.V (Fi i) a)⟫_ℂ := by
  classical
  have hTh : ∀ e : Wd.Ix (Fin w.length), ∃ F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      KB.CptCoef p.T.base F' ∧ ∀ Q, p.V (p.Θ.Θ w e F) Q = p.V F' Q := by
    intro e
    obtain ⟨F', hF', -, hV⟩ := theta_compact_support _ _ P p F w e Cb hCb hF hw
    exact ⟨F', hF', hV⟩
  choose Fe hFe hVe using hTh
  refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance,
    fun i => √((Top.cW P p.l0 w i.1 i.2).re) * √((Top.cW P p.l0 w i.1 i.2).re), fun i => Fe i.1,
    fun i => GermRateSplit.hsLE (p.TP.E i.2), fun i => mul_self_nonneg _, fun i => hFe i.1, fun a a' ha ha' => ?_⟩
  rw [np_eq p hnn, PBL.rr_top_eq vector_valued_types p F w _ _ ha ha']
  unfold Top.topOf
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  dsimp only
  have e1 := hVe e a
  have e2 := hVe e a'
  unfold KB.Pl.V at e1 e2
  rw [e1, e2, inner_smul_left, inner_smul_right, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply]
  have hin : ⟪B.hsVec ((p.TP.E ρ).comp (p.V (Fe e) a')), B.hsVec ((p.TP.E ρ).comp (p.V (Fe e) a))⟫_ℂ =
      B.hsInner ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (Fe e) a))
        ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (Fe e) a')) := rfl
  rw [hin]
  unfold omTop TBB.TTp
  set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTTdef
  by_cases h1 : 0 < D.ptG TT P.r a
  · by_cases h2 : 0 < D.ptG TT P.r a'
    · have hw1 : 0 ≤ Top.wPt TT P.r a ^ w.length := pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h1.le) _
      have hw2 : 0 ≤ Top.wPt TT P.r a' ^ w.length := pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h2.le) _
      unfold Top.dH
      rw [Real.sqrt_mul hw1, Real.sqrt_mul hw2]
      simp only [Complex.conj_ofReal]
      push_cast
      ring
    · rw [PBL.vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, PBL.hsInner_zero_right']
      simp
  · rw [PBL.vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, PBD.hsInner_zero_left]
    simp

theorem sqrt_nPt_pair_top (k r : ℕ) (TT : ℝ) (h : C.LPt) (m j : ℕ) (t c : ℂ) (hh : D.ptSize h + (m + 1) = r)
    (hk : k = j + 1) :
    √(TBB.nPt k r TT (h ++ [(m + 1, t), (1, c)])) =
      √(nHead k r h) * (‖t‖ ^ ((m + 1) * (j + m + 2)) * √((Complex.normSq c - TT) ^ j)) := by
  have hGG : D.ptGG TT (h ++ [(m + 1, t), (1, c)]) = Complex.normSq c - TT := by
    unfold D.ptGG D.ptLast
    simp
  rw [nPt_append k r TT h _ (by omega), hGG]
  simp only [C.nAux]
  rw [if_neg (by omega), if_pos ⟨by omega, trivial⟩,
    show 1 + D.ptSize h + (m + 1) - 1 = r by omega,
    show 2 * ((m + 1 : ℕ) : ℤ) * (C.Mlev k r r + ((m + 1 : ℕ) : ℤ) - 3) =
      ((2 * ((m + 1) * (j + m + 2)) : ℕ) : ℤ) by unfold C.Mlev; rw [hk]; push_cast; ring,
    zpow_natCast, one_mul, mul_one, show k - 1 = j by omega,
    Real.sqrt_mul (nHead_nonneg k r h), Real.sqrt_mul (by positivity),
    GermRateSplit.sqrt_pow_two_mul _ (norm_nonneg _)]

theorem top_core (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) {F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF' : KB.CptCoef p.T.base F') (m : ℕ) (H : C.LPt) (hH : ∀ q ∈ H, 1 ≤ q.1 ∧ q.2 ≠ 0)
    (hn : D.ptSize H + (m + 1 + 1) = P.r + 1) (K : Set ℂ) (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D)),
        (conj (co (m + 2) x j) * (omTop p nn w (FormNormSumIdentities.PPt (m + 2) H x D j) : ℂ)) •
          p.V F' (FormNormSumIdentities.PPt (m + 2) H x D j)‖ ≤ C * ‖x‖⁻¹ := by
  obtain ⟨j, hj⟩ : ∃ j, P.k = j + 1 := ⟨P.k - 1, by have := p.hl.2.2; omega⟩
  set TT := TBB.TTp p with hTTdef
  set N := w.length with hN
  have hTT : 0 < TT := mul_pos p.T.base.T_pos p.T.base.T'_pos
  obtain ⟨ε0, hε0, hsupp⟩ := hF'.2.2
  obtain ⟨Φ0, hs0, hc0, hdet0, hV0⟩ := phi_zero_hermitian_curvature _ _ P p F' hF'
  obtain ⟨σh, dh, Ψ0, hdh, hΨ0, hOB, hOL⟩ := GermRateSplit.vec_om (p.V F') Φ0 ⟨hs0, hc0, hdet0⟩ hV0 H hH m hn
  obtain ⟨MK, hMK⟩ := hK.isBounded.exists_norm_le
  obtain ⟨mK, hmK, hmK'⟩ : ∃ mK : ℝ, 0 < mK ∧ ∀ y ∈ K, mK ≤ ‖y‖ := by
    have ho : (Kᶜ : Set ℂ) ∈ 𝓝 (0 : ℂ) := hK.isClosed.isOpen_compl.mem_nhds hK0
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ho
    refine ⟨r, hr, fun y hy => ?_⟩
    by_contra hlt
    exact hball (by simpa [dist_zero_right] using not_le.1 hlt) hy
  set dH0 := Complex.normSq (D.ptMatN H (D.ptSize H)).det with hdH0
  set δ : ℝ := ε0 / (max dH0 1 * ‖(1 : ℂ)‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2) with hδ
  set ρ : ℂ → ℂ → ℝ := fun x y => √((Complex.normSq (x ^ (m + 1) * y) - TT) ^ j) / ‖x ^ (m + 1) * y‖ ^ j *
      √(Top.wPt TT P.r (H ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * y)]) ^ N) with hρdef
  set Ψ := U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0 with hΨ
  have hρ : ∀ x y : ℂ, x ≠ 0 → y ∈ K → G.OmBlock U.betaU (m + 1) Ψ x⁻¹ (x ^ (m + 1) * y) ≠ 0 →
      |ρ x y| ≤ √((δ⁻¹) ^ N) ∧
        |ρ x y - 1| ≤ ((j : ℝ) + N * (δ⁻¹) ^ N) * (TT / mK ^ 2) * ‖x‖⁻¹ ^ (2 * (m + 1)) := by
    intro x y hx hy hOm
    have hy0 : y ≠ 0 := fun h0 => hK0 (h0 ▸ hy)
    have hc0 : x ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hy0
    have ht0 : x⁻¹ ≠ 0 := inv_ne_zero hx
    have hV : p.V F' (H ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * y)]) ≠ 0 := by
      rw [hOB _ _ ht0 hc0]
      refine smul_ne_zero ?_ hOm
      exact Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_ne_zero _ GermRateSplit.qU_pos.ne'))
    have hGe : ε0 ≤ D.ptG TT P.r (H ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * y)]) := by
      by_contra hlt
      exact hV (PBO.vecV_zero_small p.T.base p.ν' p.m₀ hsupp _ (not_le.1 hlt))
    have hr : D.ptSize H + (m + 1) + 1 = P.r + 1 := by omega
    have hptG := GermRateSplit.ptG_Px TT H (m + 1) (by omega) P.r hr x⁻¹ (x ^ (m + 1) * y)
    have hwPt := GermRateSplit.wPt_Px TT H (m + 1) (by omega) P.r hr x⁻¹ (x ^ (m + 1) * y) (lt_of_lt_of_le hε0 hGe).ne'
    have hnc : Complex.normSq (x ^ (m + 1) * y) = ‖x‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm (m + 1) 2]
    have hA : ε0 ≤ dH0 * ‖1 * x⁻¹‖ ^ (2 * (m + 1)) * (Complex.normSq (x ^ (m + 1) * y) - TT) := by
      rw [hptG] at hGe; rw [one_mul]; exact hGe
    simp only [hρdef]
    rw [hwPt]
    exact GermRateSplit.rho_bound TT ε0 dH0 MK mK hTT hε0 (Complex.normSq_nonneg _) hmK j N m 1 x y
      (x ^ (m + 1) * y) one_ne_zero hx hy0 hc0 (hMK y hy) (hmK' y hy) hnc hA
  obtain ⟨Cg, hCg⟩ := germ_core_std m (D.ptSize H) σh dh hdh Ψ0 hΨ0 K hK hK0 ρ _ _ hρ
  set qL : ℝ := GermRateSplit.qU ^ Fintype.card (G.UT (m + 1 + 1)) with hqL
  have hqL0 : 0 < qL := pow_pos GermRateSplit.qU_pos _
  have hqB : GermRateSplit.qU ^ ((m + 1) + (Fintype.card (G.UT (m + 1)) + (m + 1))) = Real.pi⁻¹ ^ (m + 1) * qL := by
    have hcard : Fintype.card (G.UT (m + 1 + 1)) = Fintype.card (G.UT (m + 1)) + (m + 1) := by
      rw [StandardCharacterExists.card_UT, StandardCharacterExists.card_UT, Finset.sum_range_succ]
    rw [hqL, hcard, pow_add, GermRateSplit.qU_eq]
  set Kh : ℝ := √(nHead P.k P.r H) / √(TBB.normC nn w) * (Real.pi ^ (m + 1) * qL⁻¹) with hKh
  refine ⟨|Kh| * (max MK 0) ^ j * Cg, fun x hx y hy => ?_⟩
  have hy0 : y ≠ 0 := fun h0 => hK0 (h0 ▸ hy)
  have hc0 : x ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hy0
  have ht0 : x⁻¹ ≠ 0 := inv_ne_zero hx
  have hnone : (conj (co (m + 2) x none) * (omTop p nn w (FormNormSumIdentities.PPt (m + 2) H x y none) : ℂ)) •
      p.V F' (FormNormSumIdentities.PPt (m + 2) H x y none) =
      ((Kh * ‖y‖ ^ j : ℝ) : ℂ) • (((‖x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x y : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) Ψ x⁻¹ (x ^ (m + 1) * y)) := by
    show (conj (((‖x‖ ^ (m + 1) : ℝ) : ℂ)) * (omTop p nn w (H ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * y)]) : ℂ)) •
      p.V F' (H ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * y)]) = _
    rw [hOB _ _ ht0 hc0, Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul]
    congr 2
    unfold omTop lam
    rw [← hTTdef, ← hN, sqrt_nPt_pair_top P.k P.r TT H m j _ _ (by omega) hj, hqB, hKh]
    simp only [hρdef]
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
    have hpi := Real.pi_ne_zero
    simp only [norm_mul, norm_pow, norm_inv, inv_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  have hLong : ∀ z : ℂ, z ≠ 0 →
      ((√(Top.wPt TT P.r (H ++ [(m + 2, z)]) ^ N) : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Ψ z =
        G.OmLong U.betaU (m + 1) Ψ z := by
    intro z hz
    have hOL2 : p.V F' (H ++ [(m + 2, z)]) = ((qL⁻¹ : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Ψ z := hOL _ hz
    by_cases hG : 0 < D.ptG TT P.r (H ++ [(m + 2, z)])
    · rw [PBL.wPt_big TT H (m + 2) z P.r (by omega) (by omega) hG, one_pow,
        Real.sqrt_one, Complex.ofReal_one, one_smul]
    · have h0 : p.V F' (H ++ [(m + 2, z)]) = 0 := by
        unfold KB.Pl.V D.vecV
        rw [dif_neg]
        rintro ⟨-, hpos⟩
        exact hG hpos
      rw [hOL2] at h0
      have hq : ((qL⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (inv_ne_zero hqL0.ne')
      rw [(smul_eq_zero.1 h0).resolve_left hq, smul_zero]
  have hsome : ∀ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * y),
      (conj (co (m + 2) x (some z)) * (omTop p nn w (FormNormSumIdentities.PPt (m + 2) H x y (some z)) : ℂ)) •
        p.V F' (FormNormSumIdentities.PPt (m + 2) H x y (some z)) =
      -(((Kh * ‖y‖ ^ j : ℝ) : ℂ) • (((m : ℂ) + 2)⁻¹ •
        ((((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * G.psi U.betaU (((m : ℂ) + 2) * z * x)) •
          G.OmLong U.betaU (m + 1) Ψ z))) := by
    intro z hz
    have hz0 : z ≠ 0 := root_ne_zero (by omega) hy0 hz
    have hzs : ‖y‖ = ‖z‖ ^ (m + 2) := by
      rw [← norm_pow, (FormNormSumIdentities.mem_rootSet4 (by omega)).1 hz]; simp
    have hOL2 : p.V F' (H ++ [(m + 2, z)]) = ((qL⁻¹ : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Ψ z := hOL _ hz0
    simp only [co, FormNormSumIdentities.PPt, omTop]
    rw [← hTTdef, ← hN, hOL2, smul_smul, Complex.ofReal_mul (lam p nn w (H ++ [(m + 2, z)])),
      show ∀ a b c d : ℂ, a * (b * c) * d = (a * b * d) * c from fun a b c d => by ring, ← smul_smul,
      hLong z hz0, smul_smul, smul_smul, ← neg_smul]
    congr 1
    unfold lam
    rw [map_neg, map_mul, Complex.conj_ofReal, conj_psi_cStd,
      sqrt_nPt_long P.k P.r _ H m (j + m + 1) z (by omega) (by
        rw [show D.ptSize H + (m + 2) = P.r + 1 by omega]; unfold C.Mlev; rw [hj]; push_cast; ring),
      show m + 2 - 1 = m + 1 from rfl, hzs, hKh]
    have hzn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
    have hm2 : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
    push_cast
    field_simp
    ring
  rw [Finset.sum_insertNone, hnone, Finset.sum_congr rfl hsome, Finset.sum_neg_distrib, ← Finset.smul_sum,
    ← Finset.smul_sum, ← sub_eq_add_neg, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ j)]
  have h1 := hCg x hx y hy
  have h2 : ‖y‖ ^ j ≤ (max MK 0) ^ j :=
    pow_le_pow_left₀ (norm_nonneg _) ((hMK y hy).trans (le_max_left _ _)) _
  have h3 : 0 ≤ Cg * ‖x‖⁻¹ := le_trans (norm_nonneg _) h1
  calc |Kh| * ‖y‖ ^ j * ‖_‖ ≤ |Kh| * ‖y‖ ^ j * (Cg * ‖x‖⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ |Kh| * (max MK 0) ^ j * (Cg * ‖x‖⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) h3
    _ = _ := by ring

theorem rate_top (p : KB.Pl P Wp Wq) {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 2 ≤ s) (hi : b + s - 1 = P.r + 1) (w : List C.Letter) (hw : KB.CutWord P p.l0 w)
    (h : C.LPt) (hh : D.IsLocPt h (b - 1)) : RateAt p nn F b s w h := by
  intro H _ _ _ Vec hVec K hK hK0
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  obtain ⟨I, hI, c, Fi, L, hc, hFi, hgram⟩ := np_top_gram p hnn hF hCb w hw
  choose Ci hCi using fun i => top_core p nn w (hFi i) m h hh.1 (by rw [hh.2]; omega) K hK hK0
  refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx D hD => ?_⟩
  have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
  rw [germ_diff_eq (m + 2) hs Vec h x D hD0]
  have h2 := GermRateSplit.norm_sum_le_of_gram (TBB.NP p nn F (b + (m + 2) - 1) w) Vec hVec c hc
    (fun i a => (omTop p nn w a : ℂ) • L i (p.V (Fi i) a))
    (Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D))) (FormNormSumIdentities.PPt (m + 2) h x D) (by
      intro j hj l hl
      have hPj := isLocPt_germPt (m + 2) hs b hb h hh x D hx hD0 j hj
      have hPl := isLocPt_germPt (m + 2) hs b hb h hh x D hx hD0 l hl
      rw [hi] at hPj hPl ⊢
      exact hgram _ _ hPj hPl) (co (m + 2) x)
  refine h2.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D)), conj (co (m + 2) x j) •
        ((omTop p nn w (FormNormSumIdentities.PPt (m + 2) h x D j) : ℂ) • L i (p.V (Fi i) (FormNormSumIdentities.PPt (m + 2) h x D j))) =
      L i (∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * D)),
        (conj (co (m + 2) x j) * (omTop p nn w (FormNormSumIdentities.PPt (m + 2) h x D j) : ℂ)) •
          p.V (Fi i) (FormNormSumIdentities.PPt (m + 2) h x D j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul]
  rw [e]
  have h3 := hCi i x hx D hD
  have hsq := Real.sqrt_nonneg (c i)
  refine (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))) hsq).trans_eq ?_
  ring

theorem np_psd (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) (i : ℕ) (hi : i ≤ P.r + 1) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (Y : Finset C.LPt) : TB.PSDOn Y (TBB.NP p nn F i w) := by
  classical
  rcases Nat.lt_or_ge i (P.r + 1) with hlt | hge
  · have hj : i ≤ P.r := by omega
    let u : C.LPt → Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp) := fun a =>
      if ha : D.IsLocPt a i then ((lam p nn w a : ℝ) : ℂ) • KB.slv p.T F i hj w a ha.2 else 0
    have hu : ∀ a, PBL.CV (p.T.bs i) (u a) := by
      intro a
      simp only [u]
      split_ifs with ha
      · exact PBL.cv_smul _ fun e => slice_compact_support_coefficient _ _ P p F i hj w a ha hF e
      · exact PBL.cv_zero
    have hsl := PBL.form_slC p i hj w
    have hsr := PBL.form_srC p i hj w
    have hG := PBL.gram_psd (PBL.CV (S := Fin w.length) (p.T.bs i)) (p.form i hj w) PBL.cv_zero
      (fun x y hx hy => PBL.cv_add hx hy) (fun c x hx => PBL.cv_smul c hx) hsl hsr
      (fun x hx => module_form_pos_compact_support hA _ _ P p i hj w hw x hx) Y u hu
    have z1 : ∀ y, PBL.CV (p.T.bs i) y → p.form i hj w 0 y = 0 := by
      intro y hy
      have := hsl 0 0 y 1 PBL.cv_zero PBL.cv_zero hy
      simpa using this
    have z2 : ∀ y, PBL.CV (p.T.bs i) y → p.form i hj w y 0 = 0 := by
      intro y hy
      have := hsr y 0 0 1 hy PBL.cv_zero PBL.cv_zero
      simpa using this
    refine PBL.psd_congr (fun a _ a' _ => ?_) hG
    show p.form i hj w (u a) (u a') = _
    rw [np_eq p hnn]
    by_cases ha : D.IsLocPt a i
    · by_cases ha' : D.IsLocPt a' i
      · have c1 : PBL.CV (p.T.bs i) (KB.slv p.T F i hj w a ha.2) := fun e => slice_compact_support_coefficient _ _ P p F i hj w a ha hF e
        have c2 : PBL.CV (p.T.bs i) (KB.slv p.T F i hj w a' ha'.2) :=
          fun e => slice_compact_support_coefficient _ _ P p F i hj w a' ha' hF e
        have s1 := hsl 0 _ (u a') ((lam p nn w a : ℝ) : ℂ) PBL.cv_zero c1 (hu a')
        have s2 := hsr _ 0 _ ((lam p nn w a' : ℝ) : ℂ) c1 PBL.cv_zero c2
        rw [zero_add, z1 _ (hu a'), zero_add] at s1
        rw [zero_add, z2 _ c1, zero_add, Complex.conj_ofReal] at s2
        rw [PBL.rr_eq_form p F i hj w a a' ha ha']
        simp only [u, dif_pos ha, dif_pos ha'] at s1 ⊢
        rw [s1, s2]
        push_cast
        ring
      · rw [PBL.rr_zero_of_not p F i w a a' (fun h => ha' h.2), mul_zero]
        have : u a' = 0 := by simp only [u, dif_neg ha']
        rw [this, z2 _ (hu a)]
    · rw [PBL.rr_zero_of_not p F i w a a' (fun h => ha h.1), mul_zero]
      have : u a = 0 := by simp only [u, dif_neg ha]
      rw [this, z1 _ (hu a')]
  · have hi' : i = P.r + 1 := by omega
    subst hi'
    obtain ⟨ι, _, U, hU⟩ := PBASM.rr_top_rep p F w
    refine PBASM.psd_of_rep Y (fun k x => ((lam p nn w x : ℝ) : ℂ) • U k x) _ fun x y => ?_
    rw [np_eq p hnn, hU, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    push_cast
    ring

theorem lam_cont (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) (a : C.LPt) (m : ℕ) :
    ContinuousOn (fun c : ℂ => lam p nn w (a ++ [(m, c)])) {0}ᶜ := by
  have h1 := LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) m a 1
  have hmap : Set.MapsTo (fun c : ℂ => ((Complex.normSq c - TBB.TTp p : ℝ), c)) {0}ᶜ (Set.univ ×ˢ {0}ᶜ) :=
    fun c hc => ⟨Set.mem_univ _, hc⟩
  have h2 := h1.comp (Continuous.continuousOn (by fun_prop)) hmap
  refine ContinuousOn.div_const (Real.continuous_sqrt.comp_continuousOn (h2.congr fun c _ => ?_)) _
  simp only [Function.comp, TBB.nPt]
  congr 1
  simp [D.ptGG, D.ptLast]

theorem np_cont (p : KB.Pl P Wp Wq) {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) {Cb : ℝ}
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (i : ℕ) (hi : i ≤ P.r + 1) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (a a' : C.LPt) (m : ℕ) (hm : 1 ≤ m) (hsz : D.ptSize a + m = i)
    (hsz' : D.ptSize a' + m = i) :
    ContinuousOn (fun cc : ℂ × ℂ => TBB.NP p nn F i w (a ++ [(m, cc.1)]) (a' ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
  have hRR : ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (a ++ [(m, cc.1)]) (a' ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
    rcases Nat.lt_or_ge i (P.r + 1) with hlt | hge
    · have hi' : i ≤ P.r := by omega
      obtain ⟨χ, ε, hχ, hε, hcut⟩ := exists_cut_rr p hF
      obtain ⟨Cs, hCs0, hSQ⟩ := LastBlockContinuity.sliceContQ
      obtain ⟨ε1, -, hnice⟩ := PBL.nice_of_cpt hF
      have hS : ∀ (a : C.LPt) (hsz : D.ptSize a + m = i), (∀ b ∈ a, 1 ≤ b.1 ∧ b.2 ≠ 0) → ∀ t0 : ℂ, t0 ≠ 0 →
          LastBlockContinuity.SlcOK p.T χ ε i hi' w w.length P a m hsz F t0 := by
        intro a hsz hh t0 ht0
        obtain ⟨ε', hε', H⟩ := hSQ Cs le_rfl P.k P.r Wp Wq p.T χ _ w.length P rfl rfl p.hl.2.2 hχ le_rfl ε hε i hi'
          w le_rfl a m (LastBlockContinuity.hc_app _ m hsz) hh hm hsz t0 ht0
        obtain ⟨c, hc⟩ := hnice.2.1 (Cs * ((P.r : ℝ) + 1) ^ 4 *
          ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3))
          (3 * (11 * (w.length * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5))
        exact ⟨ε', hε', fun e => H e F c hF.1 hc⟩
      simp only [hcut i hi']
      exact LastBlockContinuity.rrBelow_cont P p χ ε F i hi' w w.length le_rfl a a' m hm hsz hsz' (hS a hsz) (hS a' hsz')
    · have hi1 : i = P.r + 1 := by omega
      subst hi1
      exact LastBlockContinuity.rrTop_cont P p F hF Cb hCb w hw a a' m hm hsz hsz'
  simp only [np_eq p hnn]
  refine ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ ?_)) hRR
  · exact (lam_cont p nn w a m).comp continuousOn_fst (fun cc hcc => hcc.1)
  · exact (lam_cont p nn w a' m).comp continuousOn_snd (fun cc hcc => hcc.2)

theorem nPt_eq_nHead (k r : ℕ) (TT : ℝ) (h : C.LPt) (hh : D.ptSize h ≤ r) : TBB.nPt k r TT h = nHead k r h := by
  have := nPt_append k r TT h [] hh
  simpa [C.nAux] using this

theorem np_succ_eq (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (a a' : C.LPt) (ha : D.ptSize a = j) (ha' : D.ptSize a' = j) (c : ℂ) :
    TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) =
      ((√(nHead P.k P.r a) * √(nHead P.k P.r a') / TBB.normC nn w : ℝ) : ℂ) *
        ((KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) := by
  have hlast : ∀ a : C.LPt, D.ptGG (TBB.TTp p) (a ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
    intro a; simp [D.ptGG, D.ptLast]
  have key : ∀ lv : ℝ, 0 ≤ lv → C.nAux P.k P.r (Complex.normSq c - TBB.TTp p) (fun _ _ => 1) (1 + j) [(1, c)] = lv →
      KB.levW P (j + 1) c = lv → TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) =
      ((√(nHead P.k P.r a) * √(nHead P.k P.r a') / TBB.normC nn w : ℝ) : ℂ) *
        ((KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) := by
    intro lv h0 h1 h2
    unfold TBB.NP
    rw [nPt_append _ _ _ a _ (by omega), nPt_append _ _ _ a' _ (by omega), hlast, hlast, ha, ha', h1, h2,
      Real.sqrt_mul (nHead_nonneg _ _ _), Real.sqrt_mul (nHead_nonneg _ _ _),
      ← mul_assoc (((√(nHead P.k P.r a) * √(nHead P.k P.r a') / TBB.normC nn w : ℝ) : ℂ)), ← Complex.ofReal_mul]
    congr 2
    have := Real.mul_self_sqrt h0
    calc _ = √(nHead P.k P.r a) * √(nHead P.k P.r a') / TBB.normC nn w * (√lv * √lv) := by ring
      _ = _ := by rw [this]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) = 0 :=
        PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w a _ c ha hc2
      unfold TBB.NP
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      rw [hT, hT'] at hc2
      refine key ((Complex.normSq c - P.T * P.T') ^ (P.k - 1)) (pow_nonneg (by linarith) _) ?_ ?_
      · simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩, hTT, mul_one]
      · simp [KB.levW, B2.zWeight, hc2.le]
  · refine key (KB.levW P (j + 1) c) ?_ ?_ rfl
    · simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    · simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring

theorem np_integral (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) {Cb : ℝ}
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (a a' : C.LPt) (ha : D.IsLocPt a j) (ha' : D.IsLocPt a' j) :
    Integrable (fun c : ℂ => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) ∧
      ∫ c : ℂ, TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) = TBB.NP p nn F j w a a' := by
  obtain ⟨φ, -, hφi, hφ, hφs⟩ := PBO.pStdCpt_of_heads hA radial_head head_top Wp Wq P p F j hj w
    a a' ha ha' Cb hCb hF hw
  have hae : (fun c : ℂ => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) =ᵐ[volume]
      fun c => ((√(nHead P.k P.r a) * √(nHead P.k P.r a') / TBB.normC nn w : ℝ) : ℂ) * φ c := by
    filter_upwards [GermRealisation.ae_ne_zero] with c hc
    rw [np_succ_eq p nn F j hj w a a' ha.2 ha'.2, hφ c hc]
  refine ⟨(hφi.const_mul _).congr hae.symm, ?_⟩
  have h0 := hφs 0
  simp only [P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_mul, PBASM.waveG_zero_eq_self] at h0
  rw [integral_congr_ae hae, integral_const_mul, h0, ← PBL.rr_eq_form p F j hj w a a' ha ha']
  unfold TBB.NP
  rw [nPt_eq_nHead _ _ _ a (by rw [ha.2]; exact hj), nPt_eq_nHead _ _ _ a' (by rw [ha'.2]; exact hj)]

theorem fsv_congr {s t s' t' : ℂ} (h : s * t = s' * t') : P5.fsv s t = P5.fsv s' t' := by
  unfold P5.fsv
  rw [← map_mul, ← map_mul, h]

theorem exists_lattice_dual (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) :
    ∃ (Lm : Submodule ℤ (crystallineComparison.V 1)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
      ∀ σ : ℂ, TBB.InDual ω₁ ω₂ σ → (fun _ => σ : crystallineComparison.V 1) ∈ Lm := by
  have hω' : (conj (Complex.I * ω₁) * (Complex.I * ω₂)).im ≠ 0 := by
    have : conj (Complex.I * ω₁) * (Complex.I * ω₂) = conj ω₁ * ω₂ := by
      rw [map_mul, Complex.conj_I]
      linear_combination (-(conj ω₁ * ω₂)) * Complex.I_mul_I
    rwa [this]
  have hg : (-(2 * Real.pi) : ℝ) ≠ 0 := neg_ne_zero.2 (by positivity)
  obtain ⟨Lm, j1, j2, hLm⟩ := PBC.GlobalTheory.dual_smul_mem
    (Submodule.span ℤ (Set.range (TBBx5.lp_b (Complex.I * ω₁) (Complex.I * ω₂) hω'))) (-(2 * Real.pi)) hg
  refine ⟨Lm, j1, j2, fun σ hσ => ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 := hLm (fun _ => σ / (-(2 * Real.pi))) ((TBBx5.lp_dual _ _ hω' _).2 (fun a b => by
    rw [← hσ a b]
    refine fsv_congr ?_
    field_simp
    linear_combination (-(σ * (a * ω₁ + b * ω₂))) * Complex.I_mul_I))
  convert h1 using 1
  funext i
  simp only [Pi.smul_apply, Complex.real_smul]
  push_cast
  field_simp

theorem mean_le_of_eventually {Λ : AddSubgroup (crystallineComparison.V 1)} {LIM : (Λ → ℂ) → ℂ} (hL : crystallineComparison.IsMeanInf Λ LIM)
    (g : Λ → ℂ) (hg : crystallineComparison.Bdd g) (a : ℝ) (ha : 0 ≤ a)
    (hev : ∀ᶠ x in Filter.comap (fun x : Λ => (x : crystallineComparison.V 1)) (crystallineComparison.atInfAll 1), ‖g x‖ ≤ a) : ‖LIM g‖ ≤ a := by
  classical
  obtain ⟨Bd, hB⟩ := hg
  let g1 : Λ → ℂ := fun x => if ‖g x‖ ≤ a then g x else 0
  let g2 : Λ → ℂ := fun x => if ‖g x‖ ≤ a then 0 else g x
  have h1 : ∀ x, ‖g1 x‖ ≤ a := by
    intro x; simp only [g1]; split_ifs with h
    · exact h
    · simpa using ha
  have h2 : crystallineComparison.Bdd g2 := ⟨max Bd 0, fun x => by
    simp only [g2]; split_ifs
    · simp
    · exact (hB x).trans (le_max_left _ _)⟩
  have hsum : g = g1 + g2 := by
    funext x; simp only [g1, g2, Pi.add_apply]; split_ifs <;> simp
  have hz : LIM g2 = 0 := hL.2 g2 h2 (tendsto_const_nhds.congr' (by
    filter_upwards [hev] with x hx
    simp only [g2, if_pos hx]))
  rw [hsum, hL.1.1 g1 g2 ⟨a, h1⟩ h2, hz, add_zero]
  exact mean_bound_estimate _ LIM g1 a hL.1 h1

theorem exists_pd_of_germData {H : Type} (h : H) (U Pm Qm : H × ℂ → H × ℂ → ℂ) (hat : ℂ → H → H → ℂ)
    (hG : PBC.GermData (f := 1) {h} (fun _ => U) (fun _ => Pm) (fun _ => Qm) (fun _ => hat))
    (ω₁ ω₂ : ℂ) (hω : (conj ω₁ * ω₂).im ≠ 0) :
    ∃ A : ℂ → ℂ, CutBP.PDDual ω₁ ω₂ A ∧ ∀ σ : ℂ,
      (‖hat σ h h + A σ‖₊ : ℝ≥0∞) ≤
        limsup (fun t : ℂ => (‖U (h, t⁻¹) (h, t⁻¹ + σ)‖₊ : ℝ≥0∞)) (𝓝[≠] 0) := by
  classical
  obtain ⟨Lm, j1, j2, hLm⟩ := exists_lattice_dual ω₁ ω₂ hω
  obtain ⟨LIM, hL⟩ := invariantMeanExists 1 Lm
  refine ⟨fun σ => PBC.A0 Lm.toAddSubgroup LIM {h} (fun _ _ => 1) (fun _ => U) (fun _ => Pm) (fun _ => Qm)
    (fun _ => σ), ?_, fun σ => ?_⟩
  · intro S c hS
    have hinj : Function.Injective fun σ : ℂ => (fun _ => σ : crystallineComparison.V 1) := fun a b hab => congrFun hab 0
    have := PBC.limit_average_positive_definite Lm.toAddSubgroup LIM hG _ (PBC.psd_single_one h) hL.1
      (S.image fun σ : ℂ => (fun _ => σ : crystallineComparison.V 1))
      (by intro τ hτ; obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hτ; exact hLm σ (hS σ hσ)) (fun τ => c (τ 0))
    rw [Finset.sum_image fun a _ b _ h => hinj h] at this
    simp_rw [Finset.sum_image fun a _ b _ h => hinj h] at this
    exact this
  · have hms := PBC.mean_split Lm.toAddSubgroup LIM hG _ (PBC.psd_single_one h) hL (fun _ => σ)
    have hH : PBC.Hh {h} (fun _ _ => (1 : ℂ)) (fun _ : Fin 1 => hat) (fun _ => σ) = hat σ h h := by simp [PBC.Hh]
    rw [hH] at hms
    rw [← hms, limsup_eq]
    refine le_sInf fun a ha => ?_
    by_cases hat' : a = ⊤
    · rw [hat']; exact le_top
    lift a to NNReal using hat'
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
    obtain ⟨Cst, hC⟩ := hG.phiG_bdd (fun _ _ => 1)
    refine mean_le_of_eventually hL _ ⟨Cst, fun x => (hC _ _).1⟩ a a.2 ?_
    have hT : Tendsto (fun x : crystallineComparison.V 1 => (x 0)⁻¹) (crystallineComparison.atInfAll 1) (𝓝[≠] 0) := by
      refine tendsto_inv₀_cobounded'.comp (tendsto_norm_atTop_iff_cobounded.1 ?_)
      exact tendsto_iff_comap.2 (iInf_le (fun v : Fin 1 => Filter.comap (fun x : crystallineComparison.V 1 => ‖x v‖) atTop) 0)
    filter_upwards [(hT.comp tendsto_comap).eventually ha] with x hx
    simp only [Function.comp, inv_inv, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at hx
    unfold PBC.phiG
    split_ifs
    · simpa [PBC.phi] using hx
    · simp

theorem pdDual_smul {ω₁ ω₂ : ℂ} {A : ℂ → ℂ} (hA : CutBP.PDDual ω₁ ω₂ A) (l : ℝ) (hl : 0 ≤ l) :
    CutBP.PDDual ω₁ ω₂ fun σ => (l : ℂ) * A σ := by
  intro S c hS
  have e : (∑ σ ∈ S, ∑ σ' ∈ S, (l : ℂ) * A (σ - σ') * c σ * conj (c σ')) =
      (l : ℂ) * ∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * conj (c σ') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ' _ => by ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg hl (hA S c hS)

theorem btOf_stronglyMeasurable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : ℕ) (hs0 : s ≠ 0)
    (d : ℝ) (Vec : C.LPt → H) (h : C.LPt) (hc : ContinuousOn (fun c : ℂ => Vec (h ++ [(s, c)])) {0}ᶜ) :
    StronglyMeasurable (GermFibreKernels.btOf s d Vec h) := by
  classical
  let g : ℂ → H := fun z => ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√d)⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])
  have hgc : ContinuousOn g {0}ᶜ := by
    refine ContinuousOn.smul ?_ hc
    refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ continuousOn_const)
    refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
    have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
    have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
    positivity
  have hbt : GermFibreKernels.btOf s d Vec h = ({0}ᶜ : Set ℂ).piecewise g (fun _ => 0) := by
    funext z
    by_cases hz : z = 0
    · simp [GermFibreKernels.btOf, hz]
    · simp [GermFibreKernels.btOf, hz, Set.piecewise, g]
  let _ : MeasurableSpace H := borel H
  have _ : BorelSpace H := ⟨rfl⟩
  rw [stronglyMeasurable_iff_measurable_separable, hbt]
  refine ⟨ContinuousOn.measurable_piecewise hgc continuousOn_const GermFibreKernels.measurableSet_ne_zero, ?_⟩
  refine TopologicalSpace.IsSeparable.mono (s := g '' {0}ᶜ ∪ {0}) ?_ (Set.range_subset_iff.2 fun z => ?_)
  · exact (hgc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace _)).union
      (Set.finite_singleton (0 : H)).isSeparable
  · by_cases hz : z ∈ ({0}ᶜ : Set ℂ)
    · left; rw [Set.piecewise_eq_of_mem _ _ _ hz]; exact ⟨z, hz, rfl⟩
    · right; rw [Set.piecewise_eq_of_notMem _ _ _ hz]; rfl

theorem germAtPD_of_cptCoef (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) {nn : ℝ → ℝ} (hnn : ∀ y, 0 < nn y)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) {Cb : ℝ}
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (Y : Finset ℝ) (K N : ℕ) : CutBP.GermAtPD p nn F Y K N := by
  intro b s hb hs hbs h hh w hw hN hBdd
  have hs0 : s ≠ 0 := by omega
  obtain ⟨SS, hSS⟩ := hBdd w ⟨hw.1, by omega, [], rfl, Nat.zero_le _, by simp⟩
  have hSS' : ∀ t : ℂ, t ≠ 0 → TBB.Ew p nn F (b + s - 2) w (h ++ [(s - 1, t)]) ≤ SS :=
    fun t ht => hSS ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨H, i1, i2, i3, Vec, hVec⟩ := GermFibreKernels.kolmogorov (TBB.NP p nn F (b + s - 1) w)
    (np_psd hA p hnn hF _ hbs w hw.1)
  have hrate : RateAt p nn F b s w h := by
    rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
    · exact rate_low p hnn hF b s hb hs (by omega) w h hh
    · exact rate_top p hnn hF hCb b s hb hs (by omega) w hw.1 h hh
  have hcont : ∀ m, 1 ≤ m → ∀ a : C.LPt, D.ptSize a + m = b + s - 1 →
      ContinuousOn (fun c : ℂ => Vec (a ++ [(m, c)])) {0}ᶜ := fun m hm a ha =>
    GermFibreKernels.vec_continuousOn _ Vec hVec (fun c => a ++ [(m, c)]) {0}ᶜ
      (np_cont p hnn hF hCb _ hbs w hw.1 a a m hm ha ha)
  have hlocX : ∀ x : ℂ, x ≠ 0 → D.IsLocPt (GermRealisation.ptX s h x) (b + s - 2) := fun x hx =>
    LastBlockContinuity.isLocPt_app hh.1 (by omega) (inv_ne_zero hx) (by rw [hh.2]; omega)
  have hV : ∀ a c, GermFibreKernels.vOf 1 Vec a c = Vec (a ++ [(1, c)]) := by
    intro a c; simp [GermFibreKernels.vOf]
  have key : ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      Integrable (fun c => ⟪GermFibreKernels.vOf 1 Vec (GermRealisation.ptX s h x) c, GermFibreKernels.vOf 1 Vec (GermRealisation.ptX s h x') c⟫_ℂ) ∧
      ∫ c, ⟪GermFibreKernels.vOf 1 Vec (GermRealisation.ptX s h x) c, GermFibreKernels.vOf 1 Vec (GermRealisation.ptX s h x') c⟫_ℂ =
        TBB.NP p nn F (b + s - 2) w (GermRealisation.ptX s h x) (GermRealisation.ptX s h x') := by
    intro x x' hx hx'
    have := np_integral hA p nn hF hCb (b + s - 2) (by omega) w hw.1 _ _ (hlocX x hx) (hlocX x' hx')
    rw [show b + s - 2 + 1 = b + s - 1 by omega] at this
    simpa only [hV, hVec] using this
  have memV : ∀ x : ℂ, x ≠ 0 → MemLp (GermFibreKernels.vOf 1 Vec (GermRealisation.ptX s h x)) 2 volume := by
    intro x hx
    have h1 : ContinuousOn (GermFibreKernels.vOf 1 Vec (GermRealisation.ptX s h x)) {0}ᶜ :=
      continuousOn_const.smul (hcont 1 le_rfl (GermRealisation.ptX s h x) (by rw [(hlocX x hx).2]; omega))
    have h2 := h1.aestronglyMeasurable (μ := volume) GermFibreKernels.measurableSet_ne_zero
    rw [Measure.restrict_eq_self_of_ae_mem (by filter_upwards [GermRealisation.ae_ne_zero] with z hz using hz)] at h2
    refine (memLp_two_iff_integrable_sq_norm h2).2 ?_
    refine (key x x hx hx).1.re.congr (Eventually.of_forall fun c => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hdiag : ∀ x : ℂ, x ≠ 0 → TBB.NP p nn F (b + s - 2) w (GermRealisation.ptX s h x) (GermRealisation.ptX s h x) =
      ((∫ D, ‖GermRealisation.utOf s (GermFibreKernels.vOf 1 Vec) h x D‖ ^ 2 : ℝ) : ℂ) := by
    intro x hx
    rw [← (key x x hx hx).2, GermRealisation.integral_inner_self_eq, ← PBK.integral_norm_cvec_sq s _ x hx,
      GermRealisation.cvec_utOf s _ h x hx]
  have hsup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖GermRealisation.utOf s (GermFibreKernels.vOf 1 Vec) h x D‖ ^ 2 ≤ SS := by
    intro x hx
    have h1 := hSS' x⁻¹ (inv_ne_zero hx)
    unfold TBB.Ew at h1
    have h2 := hdiag x hx
    unfold GermRealisation.ptX at h2
    rwa [h2, Complex.ofReal_re] at h1
  set d : ℝ := (Real.pi ^ (2 * (s - 1)))⁻¹ with hd
  have hszs : D.ptSize h + s = b + s - 1 := by rw [hh.2]; omega
  have hGD : PBK.GermD s cStd ((-1) ^ (s + 1)) ({h} : Finset C.LPt) (GermRealisation.utOf s (GermFibreKernels.vOf 1 Vec))
      (GermFibreKernels.btOf s d Vec) SS := by
    refine ⟨hs0, by simp [cStd], by simp, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h' hh' <;>
      rw [Finset.mem_singleton] at hh' <;> subst hh'
    · intro x hx
      exact (PBK.memLp_cvec s _ x hx).2 (by rw [GermRealisation.cvec_utOf s _ h' x hx]; exact memV x hx)
    · exact hsup
    · exact btOf_stronglyMeasurable s hs0 d Vec h' (hcont s (by omega) h' hszs)
    · intro K' hKc hK0
      have hsub : K' ⊆ {0}ᶜ := fun z hz hz0 => hK0 (by rw [Set.mem_singleton_iff.1 hz0] at hz; exact hz)
      have hc : ContinuousOn (fun z => ‖(((√d)⁻¹ : ℝ) : ℂ) • Vec (h' ++ [(s, z)])‖ ^ 2) K' :=
        ((continuousOn_const.smul (hcont s (by omega) h' hszs)).norm.pow 2).mono hsub
      refine (hc.congr fun z hz => ?_).integrableOn_compact hKc
      rw [GermFibreKernels.bz_btOf s hs0 d Vec h' z (fun h0 => hK0 (h0 ▸ hz))]
    · intro K' hKc hK0
      obtain ⟨Cst, hC⟩ := hrate H Vec hVec K' hKc hK0
      exact ⟨Cst, fun x hx => Eventually.of_forall fun D hD => hC x hx D hD⟩
  set Gk : C.LPt × ℂ → C.LPt × ℂ → ℂ := fun q q' =>
    TBB.NP p nn F (b + s - 2) w (GermRealisation.ptX s q.1 q.2) (GermRealisation.ptX s q'.1 q'.2) with hGk
  obtain ⟨hint, Pua, Paa, hblk, ⟨B', hB'⟩, hlim⟩ := hGD.germLoc_tail Gk (by
      intro h1 hh1 h2 hh2 x x' hx hx'
      rw [Finset.mem_singleton] at hh1 hh2
      rw [hh1, hh2]
      simp only [hGk, PBK.gramL, PBK.Uc]
      rw [GermRealisation.cvec_utOf s _ h x hx, GermRealisation.cvec_utOf s _ h x' hx', (key x x' hx hx').2])
    (PBK.Nhat s cStd (GermFibreKernels.btOf s d Vec)) (fun _ _ _ _ _ => rfl)
  have hdata : PBC.GermData (f := 1) {h} (fun _ => Gk) (fun _ => Pua) (fun _ => Paa)
      (fun _ => PBK.Nhat s cStd (GermFibreKernels.btOf s d Vec)) := by
    refine ⟨fun _ Xs hXs => hblk Xs hXs, ⟨max SS B' ⊔ 0, le_max_right _ _, fun _ q hq x hx => ?_⟩,
      fun _ q hq q' hq' σ => (hlim q hq q' hq' σ).1, fun _ q hq q' hq' σ => (hlim q hq q' hq' σ).2.1,
      fun _ q hq q' hq' σ => (hlim q hq q' hq' σ).2.2⟩
    refine ⟨?_, (hB' q hq x hx).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
    rw [Finset.mem_singleton] at hq
    rw [hq]
    simp only [hGk]
    rw [hdiag x hx, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]
    exact (hsup x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hE : ∀ z : ℂ, ((TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) : ℝ) : ℂ) =
      ⟪Vec (h ++ [(s, z)]), Vec (h ++ [(s, z)])⟫_ℂ := by
    intro z
    unfold TBB.Ew
    rw [hVec, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdens : ∀ z : ℂ, z ≠ 0 → ⟪PBK.bz s (GermFibreKernels.btOf s d Vec h) z, PBK.bz s (GermFibreKernels.btOf s d Vec h) z⟫_ℂ =
      ((Real.pi ^ (2 * (s - 1)) : ℝ) : ℂ) * (TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) : ℂ) := by
    intro z hz
    rw [GermFibreKernels.bz_btOf s hs0 d Vec h z hz, GermFibreKernels.inner_real_smul_smul, hE, hd, inv_sqrt_pi_pow, ← pow_add, two_mul]
  have hp0 : ((Real.pi ^ (2 * (s - 1)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  refine ⟨?_, ?_, fun ω₁ ω₂ hω => ?_⟩
  · have h1 := np_cont p hnn hF hCb _ hbs w hw.1 h h s (by omega) hszs hszs
    exact Complex.continuous_re.comp_continuousOn (ContinuousOn.comp
      (g := fun cc : ℂ × ℂ => TBB.NP p nn F (b + s - 1) w (h ++ [(s, cc.1)]) (h ++ [(s, cc.2)]))
      (f := fun z : ℂ => (z, z)) h1 (continuousOn_id.prodMk continuousOn_id) (fun z hz => ⟨hz, hz⟩))
  · have h1 := ((hint h (Finset.mem_singleton_self h) h (Finset.mem_singleton_self h)).const_mul
      ((Real.pi ^ (2 * (s - 1)) : ℝ) : ℂ)⁻¹).re
    refine h1.congr ?_
    filter_upwards [GermRealisation.ae_ne_zero] with z hz
    rw [hdens z hz, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
    simp
  · obtain ⟨A, hApd, hAb⟩ := exists_pd_of_germData h Gk Pua Paa _ hdata ω₁ ω₂ hω
    set l : ℝ := Real.pi⁻¹ * (Real.pi ^ (2 * (s - 1)))⁻¹ with hl
    have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hl0 : 0 ≤ l := by positivity
    have hl1 : l ≤ 1 := mul_le_one₀ (inv_le_one_of_one_le₀ hpi1) (by positivity)
      (inv_le_one_of_one_le₀ (one_le_pow₀ hpi1))
    refine ⟨fun σ => (l : ℂ) * A σ, pdDual_smul hApd l hl0, fun σ _ => ?_⟩
    have hNh : PBK.Nhat s cStd (GermFibreKernels.btOf s d Vec) σ h h = ((Real.pi ^ (2 * (s - 1)) : ℝ) : ℂ) *
        ∫ z : ℂ, P5.fsv σ z * (TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) : ℂ) := by
      unfold PBK.Nhat
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [GermRealisation.ae_ne_zero] with z hz
      rw [hdens z hz, psi_cStd, smul_eq_mul]
      ring
    have h1 := hAb σ
    simp only [hGk, GermRealisation.ptX, inv_inv] at h1
    refine le_trans ?_ h1
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    have e : (Real.pi⁻¹ : ℂ) * (∫ z : ℂ, P5.fsv σ z * (TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) : ℂ)) +
        (l : ℂ) * A σ = (l : ℂ) * (PBK.Nhat s cStd (GermFibreKernels.btOf s d Vec) σ h h + A σ) := by
      have e1 : (l : ℂ) * ((Real.pi ^ (2 * (s - 1)) : ℝ) : ℂ) = (Real.pi⁻¹ : ℂ) := by
        rw [← Complex.ofReal_mul, hl, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one, Complex.ofReal_inv]
      rw [hNh, mul_add, ← mul_assoc, e1]
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0]
    exact mul_le_of_le_one_left (norm_nonneg _) hl1

theorem latticeSum_of_cptCoef : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base G → (∀ y, 0 < nn y) → TBB.BlockGrowthBound p nn G Y K N := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn G Y K N Cb hCb hG hnn
  refine CutBP.block_growth_bound_of_positive_germ p nn G Y K N ?_ (germAtPD_of_cptCoef hA p hnn hG hCb Y K N)
  refine TBBx3.posAt_of_forms p nn G Y N (fun y => (hnn y).le) ?_
  intro j w h hj hw _
  by_cases hh : D.IsLocPt h j
  · rw [PBL.rr_eq_form p G j hj w h h hh hh]
    exact (Complex.nonneg_iff.1 (module_form_pos_compact_support hA Wp Wq P p j hj w hw.1 _
      (fun e => slice_compact_support_coefficient Wp Wq P p G j hj w h hh hG e))).1
  · rw [PBL.rr_zero_of_not p G j w h h (fun h1 => hh h1.1)]
    simp

end GlobalTheory.LatticeGerm
