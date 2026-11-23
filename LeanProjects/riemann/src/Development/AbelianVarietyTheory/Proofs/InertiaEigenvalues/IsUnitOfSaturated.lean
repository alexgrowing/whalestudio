import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelVectorMemOEOfFrobeniusStableStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SatInvUnit

theorem perfectRing_tilt_fraction_field (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ l fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
  obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
  exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
    simp [frobenius_def, div_pow, map_pow]⟩

theorem constantCoeff_frobW (l : ℕ) [Fact l.Prime] (x : WCb l) :
    WittVector.constantCoeff (frobW l x) = frobenius (Cb l) l (WittVector.constantCoeff x) :=
  WittVector.map_coeff (frobenius (Cb l) l) x 0

theorem constantCoeff_galW (l : ℕ) [Fact l.Prime] (g : GQ l) (x : WCb l) :
    WittVector.constantCoeff (galW l g x) = autCb l (galTilt l g) (WittVector.constantCoeff x) :=
  WittVector.map_coeff (autCb l (galTilt l g)).toRingHom x 0

end GlobalTheory.SatInvUnit

namespace GlobalTheory.SatInvUnit

theorem isUnit_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (Y A : Matrix (Fin d) (Fin d) (WCb l)), Y.det ≠ 0 → (∀ i j, A i j ∈ bk.OE) → Y.map (frobW l) = Y * A →
    (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧ R * Y.map (galW l (g : GQ l)) = Y) →
    (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → (∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i) → ∀ i, ((l : ℕ) : WCb l) ∣ v i) →
    IsUnit Y := by
  intro l _ K bk d Y A hY hA hφ hg hsat
  haveI : PerfectRing (Cb l) l := perfectRing_tilt_fraction_field l
  set c : WCb l →+* Cb l := WittVector.constantCoeff (p := l) (R := Cb l) with hc

  have hdetA : IsUnit A.det := by
    obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y.det hY
    have h1 : frobW l Y.det = Y.det * A.det := by
      rw [← Matrix.det_mul, ← hφ]
      simpa using RingHom.map_det (frobW l).toRingHom Y
    have hlm : ((l : WCb l)) ^ m ≠ 0 := left_ne_zero_of_mul (hu ▸ hY)
    rw [hu, map_mul, map_pow, map_natCast, mul_assoc] at h1
    have h2 := mul_left_cancel₀ hlm h1
    have hfu : IsUnit (frobW l (u : WCb l)) := u.isUnit.map (frobW l)
    rw [h2] at hfu
    exact isUnit_of_mul_isUnit_right hfu
  have hcA : (A.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdetA.map c).ne_zero
  by_cases h0 : (Y.map c).det = 0
  · exfalso
    have hAm : ∀ i j, (A.map c) i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) :=
      fun i j => Subring.mem_map.2 ⟨A i j, hA i j, rfl⟩
    have hφ' : (Y.map c).map (frobenius (Cb l) l) = Y.map c * A.map c := by
      have : (Y.map (frobW l)).map c = (Y.map c).map (frobenius (Cb l) l) := by
        ext i j
        exact constantCoeff_frobW l (Y i j)
      rw [← this, hφ, Matrix.map_mul]
    have hg' : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧
        R * (Y.map c).map (autCb l (galTilt l (g : GQ l))) = Y.map c := by
      intro g hfix
      obtain ⟨R, hR, hRY⟩ := hg g hfix
      refine ⟨R.map c, hR.map c.mapMatrix, ?_⟩
      have : (Y.map (galW l (g : GQ l))).map c = (Y.map c).map (autCb l (galTilt l (g : GQ l))) := by
        ext i j
        exact constantCoeff_galW l (g : GQ l) (Y i j)
      rw [← this, ← Matrix.map_mul, hRY]
    obtain ⟨vb, hv0, hvm, hYv⟩ := GlobalTheory.T.exists_kernel_vector_mem_OE_of_frobenius_stable l K bk d (Y.map c) (A.map c) hcA hAm hφ' hg' h0
    choose v hv hvc using fun i => Subring.mem_map.1 (hvm i)
    have hdiv : ∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i := by
      intro i
      rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
      change c (Y.mulVec v i) = 0
      rw [RingHom.map_mulVec]
      have : (c ∘ v) = vb := funext fun j => hvc j
      rw [this, hYv]
      rfl
    apply hv0
    funext i
    obtain ⟨r, hr⟩ := hsat v hv hdiv i
    rw [← hvc i, hr, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
    rfl
  · have hu : IsUnit Y.det := by
      apply WittVector.isUnit_of_coeff_zero_ne_zero
      intro h
      apply h0
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact h
    exact (Matrix.isUnit_iff_isUnit_det Y).2 hu

end GlobalTheory.SatInvUnit
