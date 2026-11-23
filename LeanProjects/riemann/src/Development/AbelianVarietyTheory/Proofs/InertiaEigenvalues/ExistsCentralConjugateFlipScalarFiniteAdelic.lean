import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

open GlobalTheory.IdemSupport

theorem idempotentFlip_mul_conjFlip_eq_one {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0)
    (hxy : x * y = 1) : (e * x + c * y + (1 - e - c)) * (c * x + e * y + (1 - c - e)) = 1 := by
  linear_combination (x*y - x - y + 1) * he + (x*y - x - y + 1) * hc + (x^2 + y^2 - 2*x - 2*y + 2) * hec + (e + c) * hxy

theorem complementIdempotent_mul_idempotentFlip {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0) :
    (1 - (e + c)) * (e * x + c * y + (1 - e - c)) = 1 - (e + c) := by
  linear_combination (1 - x) * he + (1 - y) * hc + (2 - x - y) * hec

theorem orthogonal_mul_idempotentFlip_sub_one_eq_zero {R : Type} [CommRing R] {e x y c f : R} (h1 : f * e = 0) (h2 : f * c = 0) :
    f * (e * x + c * y + (1 - e - c) - 1) = 0 := by
  linear_combination (x - 1) * h1 + (y - 1) * h2

theorem natCast_mul_incA_inv {D : D7} {m : ℕ} (hm : m ≠ 0) : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
  rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hm), map_one]

theorem cA_incA_natCast_inv {D : D7} (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [cA_incA, star_inv₀, star_natCast]

theorem cA_flipElt {D : D7} (e : AE D) (m : ℕ) :
    cA D (flipElt e m) = cA D e * (m : AE D) + e * incA D ((m : D.host.E)⁻¹) + (1 - cA D e - e) := by
  unfold flipElt
  rw [map_add, map_add, map_mul, map_mul, map_sub, map_sub, map_one, map_natCast, cA_incA_natCast_inv, cA_cA]

theorem flipElt_mul_cA {D : D7} {e : AE D} (he : e * e = e) (hec : e * cA D e = 0) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * cA D (flipElt e m) = 1 := by
  rw [cA_flipElt]
  exact idempotentFlip_mul_conjFlip_eq_one he (by rw [← map_mul, he]) hec (natCast_mul_incA_inv hm)

theorem flipElt_sub_one_mul {D : D7} {e f : AE D} (m : ℕ) (h1 : f * e = 0) (h2 : f * cA D e = 0) :
    f * (flipElt e m - 1) = 0 := by
  unfold flipElt
  exact orthogonal_mul_idempotentFlip_sub_one_eq_zero h1 h2

def scalGL {R : Type} [CommRing R] (n : ℕ) (a b : R) (h : a * b = 1) : GL (Fin n) R :=
  ⟨a • (1 : Matrix (Fin n) (Fin n) R), b • (1 : Matrix (Fin n) (Fin n) R),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, mul_comm, h, one_smul]⟩

theorem cT_scalar {R : Type} [CommRing R] (σ : R →+* R) (n : ℕ) (a : R) :
    Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) = σ a • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp only [if_true, mul_one]
  · simp only [if_neg (Ne.symm hij), if_neg hij, mul_zero, map_zero]

theorem scalGL_mem_UJ {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b : R)
    (h : a * b = 1) (hb : σ a = b) : scalGL n a b h ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) * J * (a • (1 : Matrix (Fin n) (Fin n) R)) = J
  rw [cT_scalar, hb, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, h, one_smul]

def scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) : GA D V :=
  ⟨scalGL V.rank a (cA D a) ha, scalGL_mem_UJ _ _ a (cA D a) ha rfl⟩

theorem mt_scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (scalU V a ha) = a • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

theorem scalar_sub_one_entry {R : Type} [CommRing R] {n : ℕ} {f a : R} (h : f * (a - 1) = 0) (i j : Fin n) :
    f * (a • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, mul_one]; exact h
  · rw [if_neg hij, mul_zero, sub_zero, mul_zero]

theorem oneAt_scalU {D : D7} (V : HSp D) {a : AE D} (ha : a * cA D a = 1) (l : ℕ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → algebraMap (AF D.host.F) (AE D) ε * (a - 1) = 0) :
    OneAt V l (scalU V a ha) := by
  intro v ε hε hlv i j
  rw [mt_scalU]
  exact scalar_sub_one_entry (h v ε hε hlv) i j

theorem flip_central_exists : ∀ (D : D7) (V : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → m ≠ 0 → ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V T m eT hT hm
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have he : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset hT hT subset_rfl
  have hec : eT * cA D eT = 0 := hT.2
  have hcc : cA D eT * cA D eT = cA D eT := by rw [← map_mul, he]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hT
  have hinv := flipElt_mul_cA he hec hm
  refine ⟨scalU V _ hinv, ?_, ?_, mt_scalU V _ hinv⟩
  · have hinf : infPart D eT = 0 := by
      rw [hsum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (delta_of_isIdemAt hΦ (hes PP hPP)).1
    refine mem_GfC_of_suppF V (f := eT + cA D eT) ?_ ((suppF_iff V _ _).2 ?_)
    · rw [map_add, hinf, (parts_cA eT).1, hinf, map_zero, add_zero]
    · rw [mt_scalU, smul_smul]
      unfold flipElt
      rw [complementIdempotent_mul_idempotentFlip he hcc hec]
  · intro l hl
    refine oneAt_scalU V hinv l fun v ε hε hlv => ?_
    have h0 : algebraMap (AF D.host.F) (AE D) ε * eT = 0 := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun PP hPP => ?_
      have hd := delta_of_isIdemAt hΦ (hes PP hPP)
      refine hΦ.ext' (by rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_zero]) fun Q => ?_
      rw [ev_mul, ev_zero]
      by_cases hQ : Q = PP
      · subst hQ
        by_cases hQv : Q.under (𝓞 D.host.F) = v
        · exfalso
          apply hl Q hPP
          have h1 := hlv
          rw [← hQv] at h1
          change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal at h1
          rwa [map_natCast] at h1
        · rw [(place_comp hΦ hε).2.2 Q hQv, zero_mul]
      · rw [hd.2.2 Q hQ, mul_zero]
    have h0' : algebraMap (AF D.host.F) (AE D) ε * cA D eT = 0 := by
      rw [← cA_algebraMap ε, ← map_mul, h0, map_zero]
    exact flipElt_sub_one_mul m h0 h0'

end GlobalTheory.LevelSeries

end
