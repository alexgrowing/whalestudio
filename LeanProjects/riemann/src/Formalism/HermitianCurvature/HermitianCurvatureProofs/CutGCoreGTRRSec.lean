import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.GTRRSecH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section block

variable {k : ℕ}

theorem phase_star_mul (φ : ℝ) :
    star (Complex.exp ((φ : ℂ) * Complex.I)) * Complex.exp ((φ : ℂ) * Complex.I) = 1 := by
  rw [show star (Complex.exp ((φ : ℂ) * Complex.I)) = (starRingEnd ℂ) (Complex.exp ((φ : ℂ) * Complex.I)) from rfl,
    ← Complex.exp_conj, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

theorem Hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem inv_of_UH {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g ∈ UH (Hb k)) :
    g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 := by
  have hg' : gᴴ * Hb k * g = Hb k := hg
  have hl : (Hb k * gᴴ * Hb k) * g = 1 := by
    calc (Hb k * gᴴ * Hb k) * g = Hb k * (gᴴ * Hb k * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', Hb_mul_self]
  rw [Matrix.inv_eq_left_inv hl]
  exact ⟨hl, mul_eq_one_comm.1 hl⟩

theorem UH_mul {g h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g ∈ UH (Hb k)) (hh : h ∈ UH (Hb k)) :
    g * h ∈ UH (Hb k) := by
  have e1 : gᴴ * Hb k * g = Hb k := hg
  have e2 : hᴴ * Hb k * h = Hb k := hh
  show (g * h)ᴴ * Hb k * (g * h) = Hb k
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hb k * (g * h) = hᴴ * (gᴴ * Hb k * g) * h := by simp only [Matrix.mul_assoc]
    _ = Hb k := by rw [e1, e2]

theorem UH_inv {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g ∈ UH (Hb k)) : g⁻¹ ∈ UH (Hb k) := by
  have hg' : gᴴ * Hb k * g = Hb k := hg
  obtain ⟨_, h2⟩ := inv_of_UH hg
  show (g⁻¹)ᴴ * Hb k * g⁻¹ = Hb k
  calc (g⁻¹)ᴴ * Hb k * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hb k * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hb k * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hb k := by rw [h2]; simp

theorem diag_phase_UH (d : Fin (k + 1) → ℂ) (hd : ∀ j, star (d j) * d j = 1) : diagonal d ∈ UH (Hb k) := by
  show (diagonal d)ᴴ * Hb k * diagonal d = Hb k
  rw [diagonal_conjTranspose]
  simp only [Hb, diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.star_apply]
  rw [mul_comm (star (d j)) _, mul_assoc, hd j, mul_one]

theorem dOne_UH (φ : ℝ) : dOne k φ ∈ UH (Hb k) := by
  refine diag_phase_UH _ fun j => ?_
  split_ifs
  · simp
  · exact phase_star_mul φ

theorem dTwo_UH (φ : ℝ) : dTwo k φ ∈ UH (Hb k) := by
  refine diag_phase_UH _ fun j => ?_
  split_ifs
  · exact phase_star_mul φ
  · simp

theorem smul_one_UH (φ : ℝ) :
    (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) ∈ UH (Hb k) := by
  have e : Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) =
      diagonal (fun _ => Complex.exp ((φ : ℂ) * Complex.I)) := by
    ext i j
    simp [Matrix.one_apply, diagonal_apply]
  rw [e]
  exact diag_phase_UH _ (fun _ => phase_star_mul φ)

theorem exp_zero_I : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp

theorem exp_two_pi_I : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
  push_cast
  exact Complex.exp_two_pi_mul_I

theorem exp_add_I (φ ψ : ℝ) : Complex.exp (((φ + ψ : ℝ) : ℂ) * Complex.I) =
    Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((ψ : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem dOne_eq_one {φ : ℝ} (h : Complex.exp ((φ : ℂ) * Complex.I) = 1) : dOne k φ = 1 := by
  simp [dOne, h]

theorem dTwo_eq_one {φ : ℝ} (h : Complex.exp ((φ : ℂ) * Complex.I) = 1) : dTwo k φ = 1 := by
  simp [dTwo, h]

theorem dOne_add (φ ψ : ℝ) : dOne k (φ + ψ) = dOne k φ * dOne k ψ := by
  simp only [dOne, diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs
  · simp
  · rw [exp_add_I]

theorem dTwo_add (φ ψ : ℝ) : dTwo k (φ + ψ) = dTwo k φ * dTwo k ψ := by
  simp only [dTwo, diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs
  · rw [exp_add_I]
  · simp

end block

end Formalism.FourierDecayAlt.P.GTRRSecH

namespace Formalism.FourierDecayAlt.P.GTRRSecH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section block2

variable {k : ℕ}

theorem nu_rot (hk : 1 ≤ k) (w s : ℂ) (φ : ℝ) :
    nu k w s * (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) =
      dOne k φ * nu k (w * Complex.exp ((φ : ℂ) * Complex.I)) s * dTwo k φ := by
  have hl : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have he := phase_star_mul φ
  rw [Complex.star_def] at he
  rw [Matrix.mul_smul, Matrix.mul_one]
  ext i j
  simp only [dOne, dTwo, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  rcases eq_or_ne i 0 with rfl | hi0 <;> rcases eq_or_ne j 0 with rfl | hj0
  · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
    linear_combination (-(Complex.exp (↑φ * Complex.I) * (starRingEnd ℂ) w)) * he
  · rcases eq_or_ne j (Fin.last k) with rfl | hjl
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hj0, hjl, Ne.symm hj0, Ne.symm hjl]
  · rcases eq_or_ne i (Fin.last k) with rfl | hil
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
      ring
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hi0, hil, Ne.symm hi0, Ne.symm hil]
  · rcases eq_or_ne i (Fin.last k) with rfl | hil <;> rcases eq_or_ne j (Fin.last k) with rfl | hjl
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm]
      ring
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hj0, hjl, Ne.symm hj0, Ne.symm hjl]
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hl, hl.symm, hi0, hil, Ne.symm hi0, Ne.symm hil]
    · simp [nu, vecMulVec, Matrix.one_apply, Pi.single_apply, hi0, hil, hj0, hjl, Ne.symm hi0, Ne.symm hil, Ne.symm hj0, Ne.symm hjl]

theorem wZ_rot (T T' : ℝ) (ζ e : ℂ) : wZ T T' (ζ * e) = wZ T T' ζ * e := by
  unfold wZ; ring

theorem sZ_rot (T T' : ℝ) (ζ : ℂ) (φ : ℝ) : sZ T T' (ζ * Complex.exp ((φ : ℂ) * Complex.I)) = sZ T T' ζ := by
  have h1 : Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  simp only [sZ, Complex.normSq_mul, h1, mul_one]

theorem secB_rot (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ}
    (hA : gA k a T ∈ UH (Hb k)) (hB : gB k b T' ∈ UH (Hb k)) (ζ : ℂ) (φ : ℝ) :
    theSecB k a b T T' ζ * (Complex.exp ((φ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) =
      (gA k a T * dOne k φ * (gA k a T)⁻¹) * theSecB k a b T T' (ζ * Complex.exp ((φ : ℂ) * Complex.I)) *
        ((gB k b T')⁻¹ * dTwo k φ * gB k b T') := by
  obtain ⟨hA1, _⟩ := inv_of_UH hA
  obtain ⟨_, hB2⟩ := inv_of_UH hB
  set e := Complex.exp ((φ : ℂ) * Complex.I)
  set A := gA k a T
  set B := gB k b T'
  have hsc : B * (e • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) = (e • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) * B := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  simp only [theSecB]
  rw [wZ_rot, sZ_rot]
  have hn := nu_rot hk (wZ T T' ζ) (sZ T T' ζ) φ
  calc A * nu k (wZ T T' ζ) (sZ T T' ζ) * B * (e • 1)
      = A * (nu k (wZ T T' ζ) (sZ T T' ζ) * (e • 1)) * B := by
        rw [Matrix.mul_assoc _ B, hsc]
        simp only [Matrix.mul_assoc]
    _ = A * (dOne k φ * nu k (wZ T T' ζ * e) (sZ T T' ζ) * dTwo k φ) * B := by rw [hn]
    _ = A * dOne k φ * (A⁻¹ * A) * nu k (wZ T T' ζ * e) (sZ T T' ζ) * (B * B⁻¹) * dTwo k φ * B := by
        rw [hA1, hB2]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rfl

theorem dOne_fix_last (φ : ℝ) (c : ℂ) :
    dOne k φ *ᵥ (c • Pi.single (Fin.last k) 1) = c • Pi.single (Fin.last k) 1 := by
  ext j
  simp only [dOne]
  rw [mulVec_diagonal]
  by_cases hj : j = Fin.last k
  · simp [dOne, hj]
  · simp [dOne, hj, Pi.single_apply]

theorem dTwo_fix_last (hk : 1 ≤ k) (φ : ℝ) (c : ℂ) :
    dTwo k φ *ᵥ (c • Pi.single (Fin.last k) 1) = c • Pi.single (Fin.last k) 1 := by
  ext j
  simp only [dTwo]
  rw [mulVec_diagonal]
  by_cases hj : j = Fin.last k
  · have h0 : (Fin.last k) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [dTwo, hj, h0]
  · simp [dTwo, hj, Pi.single_apply]

end block2

end Formalism.FourierDecayAlt.P.GTRRSecH

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
open Formalism.FourierDecayAlt.P.GTRRSecH

theorem jV_smul' {k r : ℕ} (c : ℂ) (u : Fin (k + 1) → ℂ) : jV k r (c • u) = c • jV k r u := by
  ext i
  simp only [jV, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem smul_one_mulVec' {k : ℕ} (c : ℂ) (u : Fin (k + 1) → ℂ) :
    (c • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) *ᵥ u = c • u := by
  rw [smul_mulVec, one_mulVec]

theorem herm_smul_left' {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) :
    herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

private theorem herm_Hb_self_eq_ofReal_re {k : ℕ} (u : Fin (k + 1) → ℂ) :
    herm (Hb k) u u = ((herm (Hb k) u u).re : ℂ) := by
  have h : herm (Hb k) u u =
      ∑ j, (((if j = Fin.last k then (-1 : ℝ) else 1) * Complex.normSq (u j) : ℝ) : ℂ) := by
    simp only [herm, Hb, dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    split_ifs <;> push_cast <;> ring
  rw [h, ← Complex.ofReal_sum, Complex.ofReal_re]

theorem rotation_section_holds : GTRRSec := by
  intro k r z z' hk hz hz' hT hT'
  have hzj : jV k r (wbPart k r z) = z := jV_wbPart hz
  have hzj' : jV k r (wbPart k r z') = z' := jV_wbPart hz'
  have haa : herm (Hb k) (wbPart k r z) (wbPart k r z) = -↑(Tz k r z) := by
    rw [herm_Hb_self_eq_ofReal_re]
    simp only [Tz]
    conv_rhs => rw [← hzj, herm_jV]
    push_cast
    ring
  have hbb : herm (Hb k) (wbPart k r z') (wbPart k r z') = -↑(Tz k r z') := by
    rw [herm_Hb_self_eq_ofReal_re]
    simp only [Tz]
    conv_rhs => rw [← hzj', herm_jV]
    push_cast
    ring
  obtain ⟨hAU, hAv⟩ := gA_spec k hT haa
  obtain ⟨hBU, hBv⟩ := gB_spec k hT' hbb
  have hA : gA k (wbPart k r z) (Tz k r z) ∈ UH (Hb k) := hAU
  have hB : gB k (wbPart k r z') (Tz k r z') ∈ UH (Hb k) := hBU
  obtain ⟨hA1, hA2⟩ := inv_of_UH hA
  obtain ⟨hB1, hB2⟩ := inv_of_UH hB
  have hsec := theSection_isSection k r z z' hk hz hz' hT hT'
  refine ⟨fun φ => ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, fun φ ψ => ⟨?_, ?_⟩, ?_, ?_⟩
  · refine (UWset_iff hz _).2 ⟨_, Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul (Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul hA (dOne_UH φ)) (UH_inv hA), ?_, rfl⟩
    have hinv : (gA k (wbPart k r z) (Tz k r z))⁻¹ *ᵥ wbPart k r z =
        (↑√(Tz k r z) : ℂ) • Pi.single (Fin.last k) 1 := by
      calc (gA k (wbPart k r z) (Tz k r z))⁻¹ *ᵥ wbPart k r z
          = (gA k (wbPart k r z) (Tz k r z))⁻¹ *ᵥ (gA k (wbPart k r z) (Tz k r z) *ᵥ
              ((↑√(Tz k r z) : ℂ) • Pi.single (Fin.last k) 1)) := by rw [hAv]
        _ = (↑√(Tz k r z) : ℂ) • Pi.single (Fin.last k) 1 := by rw [mulVec_mulVec, hA1, one_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hinv, dOne_fix_last, hAv]
  · refine (UWset_iff hz' _).2 ⟨_, Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul (Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul (UH_inv hB) (dTwo_UH φ)) hB, ?_, rfl⟩
    rw [← mulVec_mulVec, ← mulVec_mulVec, hBv, dTwo_fix_last hk, ← hBv, mulVec_mulVec, hB1, one_mulVec]
  · simp only [hL]
    rw [dOne_eq_one exp_zero_I, Matrix.mul_one, hA2, emb_one]
  · simp only [hR]
    rw [dTwo_eq_one exp_zero_I, Matrix.mul_one, hB1, emb_one]
  · simp only [hL]
    rw [dOne_eq_one exp_two_pi_I, Matrix.mul_one, hA2, emb_one]
  · simp only [hR]
    rw [dTwo_eq_one exp_two_pi_I, Matrix.mul_one, hB1, emb_one]
  · simp only [hL]
    rw [← emb_mul, dOne_add]
    congr 1
    set A := gA k (wbPart k r z) (Tz k r z)
    calc A * (dOne k φ * dOne k ψ) * A⁻¹ = A * dOne k φ * (A⁻¹ * A) * dOne k ψ * A⁻¹ := by
          rw [hA1]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = A * dOne k φ * A⁻¹ * (A * dOne k ψ * A⁻¹) := by simp only [Matrix.mul_assoc]
  · simp only [hR]
    rw [← emb_mul, dTwo_add]
    congr 1
    set B := gB k (wbPart k r z') (Tz k r z')
    calc B⁻¹ * (dTwo k φ * dTwo k ψ) * B = B⁻¹ * dTwo k φ * (B * B⁻¹) * dTwo k ψ * B := by
          rw [hB2]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = B⁻¹ * dTwo k φ * B * (B⁻¹ * dTwo k ψ * B) := by simp only [Matrix.mul_assoc]
  · intro φ g hg
    obtain ⟨μ, _, _, rfl⟩ := (UWset_iff hz' g).1 hg
    simp only [zc]
    rw [← emb_mul, ← emb_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · intro ζ hζ φ
    have hSU : theSection k r z z' ζ ∈ UH (Hb k) := (hsec.2 ζ hζ).1
    refine ⟨?_, ?_⟩
    · simp only [NF.muZ, zc, hL, hR]
      rw [← emb_mul, show theSection k r z z' ζ = theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ from rfl,
        secB_rot hk hA hB ζ φ, emb_mul, emb_mul]
      rfl
    · intro c hc
      have hprod : NF.muZ k r (theSection k r z z') ζ * zc k r φ =
          embWb k r (theSection k r z z' ζ * (Complex.exp ((φ : ℂ) * Complex.I) • 1)) := by
        simp only [NF.muZ, zc]
        rw [emb_mul]
      refine ⟨hc, ?_, ?_⟩
      · rw [hprod]
        obtain ⟨hU, hfix⟩ := emb_mem_UWb (r := r) (Formalism.FourierDecayAlt.P.GTRRSecH.UH_mul hSU (smul_one_UH φ))
        exact ⟨hU, fun a _ => hfix a⟩
      · show 0 < Q.GGl k r z z' _
        simp only [Q.GGl]
        rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last]
        have hv : (NF.muZ k r (theSection k r z z') ζ * zc k r φ) *ᵥ z' =
            Complex.exp ((φ : ℂ) * Complex.I) • (embWb k r (theSection k r z z' ζ) *ᵥ z') := by
          rw [← mulVec_mulVec]
          simp only [NF.muZ, zc]
          conv_lhs => rw [← hzj', emb_mulVec_jV, smul_one_mulVec', jV_smul', hzj']
          rw [mulVec_smul]
        rw [hv, herm_smul_left', (sec_vec hz hz' hsec hζ).2.2, Complex.normSq_mul]
        have h1 : Complex.normSq (Complex.exp ((φ : ℂ) * Complex.I)) = 1 := by
          rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
          norm_num
        rw [h1, one_mul]
        linarith

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
