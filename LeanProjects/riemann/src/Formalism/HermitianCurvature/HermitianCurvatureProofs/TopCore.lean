import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightProductGermIndep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneSubPowLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactRoots
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def ptJ (s : ℕ) (h : C.LPt) (x D : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]
  | some z => h ++ [(s, z)]

section core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def coJ (S : C.HidaSetting E Wp Wq) (b s : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) * (√(KB.dlB S (S.G.r + 1) 1))⁻¹ : ℝ) : ℂ)
  | some z => -(G.psi (GermRealisation.betaL S) ((s : ℂ) * z * x) *
      ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ : ℝ) : ℂ))

variable [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem top_core {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f)
    (F' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hF' : KB.CptCoef (p v).T.base F') (N : ℕ)
    (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s = S.G.r + 2) (h : C.LPt) (hsz : D.ptSize h = b - 1)
    (K : Set ℂ) (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖∑ j ∈ Finset.insertNone (G.rootSet s D), (conj (coJ S b s x j) * (omN S N (ptJ s h x D j) : ℂ)) •
          (p v).V F' (PBL.stdS S (ptJ s h x D j))‖ ≤ C * ‖x‖⁻¹ := by
  have hg : (0 : ℝ) < (S.g : ℝ) := PBL.g_pos_of_built hB
  have hgN : 0 < S.g := by exact_mod_cast hg
  have hk : 1 ≤ S.G.k := by
    obtain ⟨-, -, -, -, -, -, -, hl1, hlk, -⟩ := hB
    omega

  by_cases hgood : ∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0
  swap
  · refine ⟨0, fun x hx y hy => ?_⟩
    have hz : ∀ j, (p v).V F' (PBL.stdS S (ptJ s h x y j)) = 0 := by
      intro j
      unfold KB.Pl.V D.vecV
      rw [dif_neg]
      rintro ⟨hl, -⟩
      have hl' := (PBD.isLocPt_toStd_iff _ _ hg _ 1 _).1 hl
      refine hgood fun q hq => hl'.1 q ?_
      cases j <;> simp [ptJ, hq]
    simp [hz]
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have hTTeq := (PBL.pdG_of_built hB v).2
  have hTT : 0 < S.T * S.T' := by rw [← hTTeq]; exact mul_pos (p v).T.base.T_pos (p v).T.base.T'_pos
  obtain ⟨ε0, hε0, hsupp⟩ := hF'.2.2
  set H := PBL.stdS S h with hHdef
  have hH : ∀ q ∈ H, 1 ≤ q.1 ∧ q.2 ≠ 0 := ((PBD.isLocPt_toStd_iff _ _ hg h 1 (D.ptSize h)).2 ⟨hgood, rfl⟩).1
  have hHs : D.ptSize H = b - 1 := by rw [hHdef, PBL.stdS_size, hsz]
  obtain ⟨Φ0, hs0, hc0, hdet0, hV0⟩ := Formalism.FourierDecayAlt.P.phi_zero_hermitian_curvature _ _ (D.parOf S v) (p v) F' hF'
  have hn : D.ptSize H + (m + 1 + 1) = (D.parOf S v).r + 1 := by
    rw [hHs]; change _ = S.G.r + 1; omega
  obtain ⟨σh, dh, Ψ0, hdh, hΨ0, hOB, hOL⟩ := vec_om ((p v).V F') Φ0 ⟨hs0, hc0, hdet0⟩ hV0 H hH m hn
  obtain ⟨Kh, hKA, hKB⟩ := const_match S hgN b (m + 2) hb hs hbs hk h hsz
  set l1 := lam1 S (m + 2) with hl1def
  set l2 := lam2 S (m + 2) with hl2def
  have hq0 : ((S.g : ℝ) / (2 * Real.pi)) ≠ 0 := (div_pos hg (by positivity)).ne'
  have hl1 : l1 ≠ 0 := by
    rw [hl1def, lam1]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 (pow_ne_zero _ hq0)) (pow_ne_zero _ Complex.I_ne_zero)
  have hl : l2 ^ (m + 2) = (-1) ^ (m + 3) * l1 ^ (m + 1) := by
    rw [hl2def, hl1def, lam1, lam2, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← pow_mul, ← pow_mul]
    have e2 : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
    have e3 : (m + 2) * (m + 1) = (m + 1) * (m + 2) := by ring
    rw [e3, e2, pow_add Complex.I, pow_mul Complex.I 2 (m + 1), Complex.I_sq]
    ring
  have hl2ne : l2 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hl
    exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hl1)) hl.symm
  set βL : ℝ := 4 * Real.pi / (S.g : ℝ) with hβL
  have hq : l2 / l1 = (((2 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * Complex.I := by
    have hgc : ((S.g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hg.ne'
    have hpc : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have hgc' : (S.g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hgN.ne'
    have hcq : (2 * (Real.pi : ℂ) / (S.g : ℂ)) * ((S.g : ℂ) / (2 * (Real.pi : ℂ))) = 1 := by
      field_simp
    have e : l2 = (((2 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * Complex.I * l1 := by
      rw [hl2def, hl1def, lam1, lam2, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
      push_cast
      linear_combination (-(((S.g : ℂ) / (2 * (Real.pi : ℂ))) ^ (m + 1) * Complex.I ^ (m + 1))) * hcq
    rw [e, mul_div_assoc, div_self hl1, mul_one]
  have hψ : ∀ w : ℂ, G.psi U.betaU (l2 / l1 * w) = conj (G.psi (βL : ℂ) w) := by
    intro w
    have hbU : U.betaU = 2 * Complex.I := by
      unfold U.betaU Formalism.QuantumDeterminants.cStd; ring
    unfold G.psi
    rw [← Complex.exp_conj, hq, hbU, hβL]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    have hre : ((2 * Complex.I) * ((((2 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * Complex.I * w)).re =
        -((4 * Real.pi / (S.g : ℝ)) * w.re) := by
      simp [Complex.mul_re, Complex.mul_im]
      ring
    have hre2 : ((((4 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * w).re = (4 * Real.pi / (S.g : ℝ)) * w.re := by
      simp [Complex.mul_re]
    rw [hre, hre2]
    push_cast
    ring
  obtain ⟨MK, hMK⟩ := hK.isBounded.exists_norm_le
  obtain ⟨mK, hmK, hmK'⟩ : ∃ mK : ℝ, 0 < mK ∧ ∀ y ∈ K, mK ≤ ‖y‖ := by
    have ho : (Kᶜ : Set ℂ) ∈ 𝓝 (0 : ℂ) := hK.isClosed.isOpen_compl.mem_nhds hK0
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ho
    refine ⟨r, hr, fun y hy => ?_⟩
    by_contra hlt
    exact hball (by simpa [dist_zero_right] using not_le.1 hlt) hy
  set dH0 := Complex.normSq (D.ptMatN H (D.ptSize H)).det with hdH0
  set δ : ℝ := ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2) with hδ
  set ρ : ℂ → ℂ → ℝ := fun x y => √((Complex.normSq (x ^ (m + 1) * y) - S.T * S.T') ^ (S.G.k - 1)) /
      ‖x ^ (m + 1) * y‖ ^ (S.G.k - 1) *
      √(Top.wPt (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ^ N) with hρdef
  set R0 : ℝ := √((δ⁻¹) ^ N) with hR0
  set L : ℝ := ((S.G.k - 1 : ℕ) + N * (δ⁻¹) ^ N) * (S.T * S.T' / mK ^ 2) with hL
  have hρ : ∀ x y : ℂ, x ≠ 0 → y ∈ K →
      G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l1 * x⁻¹)
        (x ^ (m + 1) * y) ≠ 0 →
      |ρ x y| ≤ R0 ∧ |ρ x y - 1| ≤ L * ‖x‖⁻¹ ^ (2 * (m + 1)) := by
    intro x y hx hy hOm
    have hy0 : y ≠ 0 := fun h0 => hK0 (h0 ▸ hy)
    have hc0 : x ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hy0
    have ht0 : l1 * x⁻¹ ≠ 0 := mul_ne_zero hl1 (inv_ne_zero hx)
    have hV : (p v).V F' (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ≠ 0 := by
      rw [hOB _ _ ht0 hc0]
      refine smul_ne_zero ?_ hOm
      exact Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_ne_zero _ qU_pos.ne'))
    have hGe : ε0 ≤ D.ptG (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) := by
      by_contra hlt
      exact hV (Formalism.FourierDecayAlt.P.PBO.vecV_zero_small (p v).T.base (p v).ν' (p v).m₀ hsupp _
        (lt_of_eq_of_lt (congrArg (fun T => D.ptG T S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)])) hTTeq)
          (not_le.1 hlt)))
    have hr : D.ptSize H + (m + 1) + 1 = S.G.r + 1 := by rw [hHs]; omega
    have hptG := ptG_Px (S.T * S.T') H (m + 1) (by omega) S.G.r hr (l1 * x⁻¹) (x ^ (m + 1) * y)
    have hGne : D.ptG (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ≠ 0 :=
      (lt_of_lt_of_le hε0 hGe).ne'
    have hwPt := wPt_Px (S.T * S.T') H (m + 1) (by omega) S.G.r hr (l1 * x⁻¹) (x ^ (m + 1) * y) hGne
    have hnc : Complex.normSq (x ^ (m + 1) * y) = ‖x‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm (m + 1) 2]
    have hA : ε0 ≤ dH0 * ‖l1 * x⁻¹‖ ^ (2 * (m + 1)) * (Complex.normSq (x ^ (m + 1) * y) - S.T * S.T') := by
      rw [hptG] at hGe; exact hGe
    have hρe : ρ x y = √((Complex.normSq (x ^ (m + 1) * y) - S.T * S.T') ^ (S.G.k - 1)) /
        ‖x ^ (m + 1) * y‖ ^ (S.G.k - 1) *
        √((Complex.normSq (x ^ (m + 1) * y) / (Complex.normSq (x ^ (m + 1) * y) - S.T * S.T')) ^ N) := by
      simp only [hρdef]; rw [hwPt]
    rw [hρe]
    exact rho_bound (S.T * S.T') ε0 dH0 MK mK hTT hε0 (Complex.normSq_nonneg _) hmK (S.G.k - 1) N m l1 x y
      (x ^ (m + 1) * y) hl1 hx hy0 hc0 (hMK y hy) (hmK' y hy) hnc hA
  obtain ⟨Cg, hCg⟩ := germ_core m (D.ptSize H) σh dh hdh Ψ0 hΨ0 l1 l2 hl1 hl βL hψ K hK hK0 ρ R0 L hρ
  refine ⟨|Kh| * (max MK 0) ^ (S.G.k - 1) * Cg, fun x hx y hy => ?_⟩
  have key : ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) y), (conj (coJ S b (m + 2) x j) *
      (omN S N (ptJ (m + 2) h x y j) : ℂ)) • (p v).V F' (PBL.stdS S (ptJ (m + 2) h x y j)) =
      ((Kh * ‖y‖ ^ (S.G.k - 1) : ℝ) : ℂ) •
        (((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x y : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l1 * x⁻¹)
            (x ^ (m + 1) * y) -
        ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) y,
          (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z)) := by
    have hy0 : y ≠ 0 := fun h0 => hK0 (h0 ▸ hy)
    have hc0 : x ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hy0
    have ht0 : l1 * x⁻¹ ≠ 0 := mul_ne_zero hl1 (inv_ne_zero hx)

    have hnone : (conj (coJ S b (m + 2) x none) * (omN S N (ptJ (m + 2) h x y none) : ℂ)) •
        (p v).V F' (PBL.stdS S (ptJ (m + 2) h x y none)) =
        ((Kh * ‖y‖ ^ (S.G.k - 1) : ℝ) : ℂ) •
          (((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x y : ℝ) : ℂ) •
            G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l1 * x⁻¹)
              (x ^ (m + 1) * y)) := by
      have hstd := std_Px S (m + 2) hs h (by omega) x⁻¹ (x ^ (m + 2 - 1) * y)
      have hKA' := hKA x y hx hy0
      simp only [e1] at hstd hKA'
      simp only [coJ, ptJ, omN, e1]
      rw [hstd, hOB _ _ ht0 hc0, Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul]
      congr 2
      simp only [hρdef]
      rw [← hHdef, ← hl1def]
      linear_combination √(Top.wPt (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ^ N) * hKA'

    have hLong : ∀ z : ℂ, z ≠ 0 →
        ((√(Top.wPt (S.T * S.T') S.G.r (H ++ [(m + 2, l2 * z)]) ^ N) : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) =
        G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) := by
      intro z hz
      have hl2z : l2 * z ≠ 0 := mul_ne_zero hl2ne hz
      have hOL2 : (p v).V F' (H ++ [(m + 2, l2 * z)]) = (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) :=
        hOL _ hl2z
      by_cases hG : 0 < D.ptG (S.T * S.T') S.G.r (H ++ [(m + 2, l2 * z)])
      · rw [PBL.wPt_big (S.T * S.T') H (m + 2) (l2 * z) S.G.r (by omega) (by rw [hHs]; omega) hG, one_pow,
          Real.sqrt_one, Complex.ofReal_one, one_smul]
      · have h0 : (p v).V F' (H ++ [(m + 2, l2 * z)]) = 0 := by
          unfold KB.Pl.V D.vecV
          rw [dif_neg]
          rintro ⟨-, hpos⟩
          exact hG (lt_of_lt_of_eq hpos (congrArg (fun T => D.ptG T S.G.r (H ++ [(m + 2, l2 * z)])) hTTeq))
        rw [hOL2] at h0
        have hq : (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_ne_zero _ qU_pos.ne'))
        rw [(smul_eq_zero.1 h0).resolve_left hq, smul_zero]
    have hsome : ∀ z ∈ G.rootSet (m + 2) y,
        (conj (coJ S b (m + 2) x (some z)) * (omN S N (ptJ (m + 2) h x y (some z)) : ℂ)) •
          (p v).V F' (PBL.stdS S (ptJ (m + 2) h x y (some z))) =
        -(((Kh * ‖y‖ ^ (S.G.k - 1) : ℝ) : ℂ) • (((m : ℂ) + 2)⁻¹ •
          ((((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z)))) := by
      intro z hz
      have hzs : z ^ (m + 2) = y := by
        unfold G.rootSet at hz
        exact (Polynomial.mem_nthRoots (by omega)).1 (Multiset.mem_toFinset.1 hz)
      have hz0 : z ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hzs; exact hy0 hzs.symm
      have hl2z : l2 * z ≠ 0 := mul_ne_zero hl2ne hz0
      have hstd := std_Qz S (m + 2) hs h (by omega) z
      have hKB' := hKB z hz0
      rw [hzs] at hKB'
      simp only [e1] at hKB'
      have hOL2 : (p v).V F' (H ++ [(m + 2, l2 * z)]) = (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) :=
        hOL _ hl2z
      simp only [coJ, ptJ, omN, e1]
      rw [hstd, ← hHdef, ← hl2def, hOL2, smul_smul,
        Complex.ofReal_mul (√(PBL.nnS S (h ++ [(m + 2, z)])) / PBL.bS S (h ++ [(m + 2, z)])),
        show ∀ a b c d : ℂ, a * (b * c) * d = (a * b * d) * c from fun a b c d => by ring, ← smul_smul,
        hLong z hz0, smul_smul, smul_smul, ← neg_smul]
      congr 1
      have hβ : GermRealisation.betaL S = (βL : ℂ) := by simp only [GermRealisation.betaL, hβL]
      have hpsi : G.psi (GermRealisation.betaL S) (((m + 2 : ℕ) : ℂ) * z * x) = G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x) := by
        rw [hβ]; congr 1; push_cast; ring
      rw [hpsi, map_neg, map_mul, Complex.conj_ofReal]
      have hKc := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hKB'
      push_cast at hKc ⊢
      linear_combination (-(conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x)))) * hKc
    rw [Finset.sum_insertNone, hnone, Finset.sum_congr rfl hsome, Finset.sum_neg_distrib, smul_sub,
      Finset.smul_sum, Finset.smul_sum, sub_eq_add_neg]
  rw [key, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ (S.G.k - 1))]
  have h1 := hCg x hx y hy
  have h2 : ‖y‖ ^ (S.G.k - 1) ≤ (max MK 0) ^ (S.G.k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ((hMK y hy).trans (le_max_left _ _)) _
  have h3 : 0 ≤ Cg * ‖x‖⁻¹ := le_trans (norm_nonneg _) h1
  calc |Kh| * ‖y‖ ^ (S.G.k - 1) * ‖_‖ ≤ |Kh| * ‖y‖ ^ (S.G.k - 1) * (Cg * ‖x‖⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ |Kh| * (max MK 0) ^ (S.G.k - 1) * (Cg * ‖x‖⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) h3
    _ = |Kh| * (max MK 0) ^ (S.G.k - 1) * Cg * ‖x‖⁻¹ := by ring

end core

end

end Formalism.FourierDecayAlt.P.GermRateSplit
