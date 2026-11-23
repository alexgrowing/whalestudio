import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryBlockLevelUnitBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixCongrAdelicMatrixModNatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewLatticeMoverWithDeterminantStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetMove

theorem wd_wd_norm (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  have hn : ∀ x : VC D N N', ‖wdPh D T x‖ = 1 := fun x => by
    simp [wdPh, ee, Complex.norm_exp]
  have hc : Hf D T b a = (starRingEnd ℂ) (Hf D T a b) := by
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩
  · rw [norm_mul, norm_div, norm_mul, hn, hn, hn, Complex.norm_exp, hc]
    have : (((Real.pi : ℂ) * ((starRingEnd ℂ) (Hf D T a b) - Hf D T a b) / 2)).re = 0 := by
      simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.div_re]
    rw [this]; simp
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this

set_option maxHeartbeats 1000000 in

theorem om_cosetV_block : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ k ∈ intG D a, W.Om 1 h (cosetV D δ 𝔪 0 a d e0) = c • W.Om k 1 (cosetV D δ 𝔪 0 a d e0) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hcop _ h hh hblk
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨G, hGdef⟩ : ∃ G, G = Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := ⟨_, rfl⟩

  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd, hcen⟩ := GlobalTheory.T.exists_skew_lattice_mover_with_determinant D 𝔪 h𝔪 hcop d
  have hsd : SD D (skewLat D 𝔪 d) := VacMove.sd_of_moves hg'm
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hJ : W.Om 1 g' e0 = χ • G := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (FixKey.suppSplit_one D a) hg's
      (fun q hq hi => ⟨by simpa using FixKey.zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm, hχ, hGdef]
    rfl
  have hc0 : χ ≠ 0 := by rw [hχ]; exact Units.ne_zero _
  have hJe : G = χ⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hgT : W.Om 1 g' e0 ∈ TT D (tor0 D ⊤ δ) a d := W.maps 1 g' e0 hT
  have hJT : G ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hJe]; exact FixKey.TT_smul _ hgT

  obtain ⟨xh, -, hxh⟩ := VacInt.om_vac_right he hT W ((mem_intG h).1 hh)
  obtain ⟨uh, huh⟩ : ∃ u : ℂ, u = ((W.chV.f xh ^ W.ep : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huh] at hxh
  have hhG : W.Om 1 h G = uh • G := by
    have e1 := W.mul 1 1 h g' e0 hT
    have e2 := W.mul 1 1 g' h e0 hT
    rw [mul_one] at e1 e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, hcen, e2, hxh, W.smul _ _ _ _ hT, smul_comm]
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.T.exists_integralUnitary_blockLevel_unitBlock D 𝔪 h𝔪 hcop had h hh hblk
  obtain ⟨xk, -, hxk⟩ := VacInt.om_vac_left he hT W ((mem_intG k).1 hk)
  obtain ⟨uk, huk⟩ : ∃ u : ℂ, u = ((W.chV'.f xk ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huk] at hxk
  have hkG : W.Om k 1 G = uk • G := by
    have e1 := W.mul k 1 1 g' e0 hT
    have e2 := W.mul 1 k g' 1 e0 hT
    rw [mul_one, one_mul] at e1
    rw [one_mul, mul_one] at e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, e2, hxk, W.smul _ _ _ _ hT, smul_comm]
  have nuh : ‖uh‖ = 1 := by
    rw [huh, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV.unitary, one_zpow]
  have nuk : ‖uk‖ = 1 := by
    rw [huk, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV'.unitary, one_zpow]

  obtain ⟨x₀, hx₀⟩ : ∃ x, x = unitBlock D 0 a d := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁, hl₁⟩ := W.lift 1 h x₀ G hJT
  obtain ⟨m₂, hm₂, hl₂⟩ := W.lift k 1 x₀ G hJT
  obtain ⟨Y₁, hY₁⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y = ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * x₀.map (inc D) := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y =
    x₀.map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) := ⟨_, rfl⟩
  have hkx' : ∀ i j, (Y₁ - Y₂) i j ∈ hatId D 𝔪 := by rw [hY₁, hY₂, hx₀]; exact hkx
  obtain ⟨z, hz⟩ := VacMove.MI_approx (cc := ⊤) top_ne_bot Y₂ (m₁ * m₂) (Nat.mul_pos hm₁ hm₂)
  obtain ⟨w, hw𝔪, hw⟩ := GlobalTheory.T.exists_ideal_matrix_congr_adelicMatrix_mod_nat D 𝔪 (Y₁ - Y₂) hkx' m₁ hm₁
  have hc2 : CloseTo D ⊤ m₂ (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ z := by
    have := hz.of_dvd (m := m₂) (dvd_mul_left _ _)
    intro i j
    obtain ⟨y, hy, e⟩ := this i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₂]; simp
  have hc1 : CloseTo D ⊤ m₁ ((1 : GA D a) : GL (Fin a) (AE D)) (h : GL (Fin d) (AE D)) x₀ (z + w) := by
    have h3 := (hz.of_dvd (m := m₁) (dvd_mul_right _ _)).add hw
    have key : z.map (inc D) - Y₂ + (w.map (inc D) - (Y₁ - Y₂)) = (z + w).map (inc D) - Y₁ := by
      ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_add]; abel
    rw [key] at h3
    intro i j
    obtain ⟨y, hy, e⟩ := h3 i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₁]; simp
  have hWh := hl₁ (z + w) hc1
  have hWk := hl₂ z hc2
  rw [hhG, FixKey.wd_smul, VacMove.pt_add] at hWh
  rw [hkG, FixKey.wd_smul] at hWk

  obtain ⟨φ, hφ1, hφ⟩ := wd_wd_norm D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    VacMove.klat _ (VacMove.moves_one D a) hg'm
  have hJB := GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace D δ hc e0 he 𝔪 hsd
  rw [← hGdef] at hJB
  have hwB := (GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪).2
  have hfix : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ w) G = G := VacMove.wd_fix h1 hc hBk hJB hwB
  have hφ0 : φ ≠ 0 := by intro h0; rw [h0, norm_zero] at hφ1; exact zero_ne_one hφ1
  have hsum := hφ G
  rw [hfix] at hsum
  have hzw : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z + pt D (tor0 D ⊤ δ) δ w) G =
      φ⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) G := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hφ0, one_smul]
  have huk0 : uk ≠ 0 := by rw [huk]; exact Units.ne_zero _
  refine ⟨uh * φ⁻¹ * uk⁻¹, by rw [norm_mul, norm_mul, norm_inv, norm_inv, nuh, hφ1, nuk]; simp, k, hk, ?_⟩
  have hWT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G ∈ TT D (tor0 D ⊤ δ) a d :=
    GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT
  unfold cosetV
  rw [← hx₀, ← hGdef]
  rw [W.smul _ _ _ _ hWT, W.smul _ _ _ _ hWT]
  change _ • W.Om 1 h (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G) = _ • _ • W.Om k 1 (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G)
  rw [hWh, hWk, hzw, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FunObj.CosetMove
