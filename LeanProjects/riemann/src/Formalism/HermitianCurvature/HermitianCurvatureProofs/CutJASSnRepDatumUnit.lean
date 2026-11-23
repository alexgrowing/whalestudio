import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

namespace DU

variable {k r : ℕ}

theorem hadd_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x y w : Fin m → ℂ) :
    herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, Matrix.mulVec_add]

theorem hadd_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x w w' : Fin m → ℂ) :
    herm H x (w + w') = herm H x w + herm H x w' := by
  simp [herm, add_dotProduct]

theorem hsmul_l {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H (c • x) w = c * herm H x w := by
  simp [herm, Matrix.mulVec_smul]

theorem hsmul_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (x w : Fin m → ℂ) :
    herm H x (c • w) = conj c * herm H x w := by
  simp [herm, smul_dotProduct, Complex.star_def]

private theorem herm_swap_eq_zero_of_eq_zero {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : ∀ i j, H i j = star (H j i))
    (v w : Fin m → ℂ) : herm H w v = conj (herm H v w) := by
  simp only [herm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hH b a]
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

private theorem Hpk_apply_eq_star_apply_swap : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j = star (Hpk k r j i) := by
  intro i j
  simp only [Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | (simp; done) | (exfalso; omega)

theorem hswap (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) w v = conj (herm (Hpk k r) v w) := by
  exact herm_swap_eq_zero_of_eq_zero _ Hpk_apply_eq_star_apply_swap v w

theorem blockProjection_of_mem_block {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : SSn.wbP k r v = v := by
  funext i
  simp only [SSn.wbP]
  split_ifs with h
  · rfl
  · exact (hv i (by omega)).symm

theorem prWv_of {z v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    SSn.prWv k r z v = v + (herm (Hpk k r) v z / (Tz k r z : ℂ)) • z := by
  simp only [SSn.prWv, blockProjection_of_mem_block hv]

theorem prWv_fix {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) :
    SSn.prWv k r z x = x := by
  rw [prWv_of hx, h0]
  simp

private theorem herm_Hpk_self_eq_neg_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_perp {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) :
    herm (Hpk k r) (SSn.prWv k r z y) z = 0 := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy, hadd_l, hsmul_l, herm_Hpk_self_eq_neg_Tz]
  have h1 : herm (Hpk k r) y z / (Tz k r z : ℂ) * -(Tz k r z : ℂ) = -herm (Hpk k r) y z := by
    rw [div_mul_eq_mul_div, mul_neg, neg_div, mul_div_assoc, div_self hT0, mul_one]
  rw [h1]
  ring

theorem prWv_inWb {z y : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hy : inWb k r y) :
    inWb k r (SSn.prWv k r z y) := by
  intro i hi
  have h1 : SSn.wbP k r y i = 0 := by
    simp only [SSn.wbP]
    rw [if_neg]
    omega
  simp only [SSn.prWv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz i hi, h1, mul_zero, add_zero]

private theorem herm_Hpk_self_self_eq_neg_ofReal_Tz (z : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := hswap (k := k) (r := r) z z
  apply Complex.ext
  · simp [Tz]
  · have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    simp
    linarith

theorem prWv_norm {z y : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hy : inWb k r y) {ζ : ℂ} {T' : ℝ}
    (hyy : herm (Hpk k r) y y = -(T' : ℂ)) (hyz : herm (Hpk k r) y z = ζ) :
    herm (Hpk k r) (SSn.prWv k r z y) (SSn.prWv k r z y) =
      ((Complex.normSq ζ / Tz k r z - T' : ℝ) : ℂ) := by
  have hT0 : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [prWv_of hy]
  simp only [hadd_l, hadd_r, hsmul_l, hsmul_r, herm_Hpk_self_self_eq_neg_ofReal_Tz, hyy, hyz]
  rw [hswap y z, hyz, map_div₀, Complex.conj_ofReal]
  push_cast
  rw [← Complex.mul_conj]
  field_simp
  ring

theorem unitH_facts {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) {s : ℝ}
    (hs : 0 < s) (hxx : herm (Hpk k r) x x = (s : ℂ)) :
    SSn.prWv k r z (SSn.unitH k r x) = SSn.unitH k r x ∧ herm (Hpk k r) (SSn.unitH k r x) (SSn.unitH k r x) = 1 := by
  have hu : SSn.unitH k r x = (((Real.sqrt s)⁻¹ : ℝ) : ℂ) • x := by
    simp only [SSn.unitH, hxx, Complex.ofReal_re]
  have hin : inWb k r (SSn.unitH k r x) := by
    intro i hi
    rw [hu]
    simp [hx i hi]
  refine ⟨prWv_fix hin ?_, ?_⟩
  · rw [hu, hsmul_l, h0, mul_zero]
  · rw [hu, hsmul_l, hsmul_r, hxx, Complex.conj_ofReal]
    have key : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
    exact_mod_cast key

theorem base {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
      SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ ∧
      herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 := by
  have hm := NFRadRedA.muZ_uwb hsec hζ
  have hG := NFRadRedA.uwb_glev hm
  have hU : NF.muZ k r μsec ζ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : (NF.muZ k r μsec ζ)⁻¹ ∈ UH (Hpk k r) := hGi.1
  have hyz : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' hsec hζ
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hyy : herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ z') (NF.muZ k r μsec ζ *ᵥ z') = -((Tz k r z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hyyi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) =
      -((Tz k r z : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hUi, FrameEntries.herm_self]
  have hyzi : herm (Hpk k r) ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) z' = conj ζ := by
    rw [hswap, ← FrameEntries.herm_inv hU, hyz]
  have hpos : 0 < Complex.normSq ζ / Tz k r z - Tz k r z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  have hposi : 0 < Complex.normSq (conj ζ) / Tz k r z' - Tz k r z := by
    rw [Complex.normSq_conj, sub_pos, lt_div_iff₀ hT']; linarith
  obtain ⟨h1, h2⟩ := unitH_facts (prWv_inWb hz hy) (prWv_perp hT hy) hpos (prWv_norm hT hy hyy hyz)
  obtain ⟨h3, h4⟩ := unitH_facts (prWv_inWb hz' hyi) (prWv_perp hT' hyi) hposi (prWv_norm hT' hyi hyyi hyzi)
  exact ⟨h1, h2, h3, h4⟩

end DU

theorem datum_unit_norm_holds : DatumUnit := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ζ hζ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hζ' : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' < Complex.normSq ζ := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; exact hζ
  exact DU.base hPl.2.1 hPl.2.2.1 (T v).base.T_pos (T v).base.T'_pos (T v).base.sec hζ'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
