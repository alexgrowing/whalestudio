import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.EtaleLattice

theorem exists_frob_matrix {R : Type} [CommRing R] [IsDomain R] (O : Subring R) (φ : R →+* R) (p : R) (hp : p ≠ 0)
    (hφp : φ p = p) (hφO : ∀ w ∈ O, φ w ∈ O) {d : ℕ} (Y A P Y' : Matrix (Fin d) (Fin d) R) (k m : ℕ) (u u' : R)
    (hu' : u' ∈ O) (huu : u * u' = 1) (hA : ∀ i j, A i j ∈ O) (hP : ∀ i j, P i j ∈ O)
    (hφ : (p ^ k * u) • Y.map φ = Y * A) (hY' : p ^ m • Y' = Y * P)
    (hlat : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, p ^ n ∣ (Y *ᵥ v) i) →
      ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • v = p ^ n • (P *ᵥ w)) :
    ∃ B : Matrix (Fin d) (Fin d) R, (∀ i j, B i j ∈ O) ∧ Y'.map φ = Y' * B := by
  have cancel : ∀ (n : ℕ) (M N : Matrix (Fin d) (Fin d) R), p ^ n • M = p ^ n • N → M = N := by
    intro n M N h
    refine Matrix.ext fun i j => ?_
    exact mul_left_cancel₀ (pow_ne_zero n hp) (congrFun (congrFun h i) j)
  have h1 : p ^ m • Y'.map φ = Y.map φ * P.map φ := by
    rw [← Matrix.map_mul, ← hY']
    refine Matrix.ext fun i j => ?_
    simp [hφp]
  set V : Matrix (Fin d) (Fin d) R := u' • (A * P.map φ) with hV
  have hVO : ∀ i j, V i j ∈ O := by
    intro i j
    rw [hV, Matrix.smul_apply, Matrix.mul_apply]
    exact O.mul_mem hu' (O.sum_mem fun c _ => O.mul_mem (hA i c) (hφO _ (hP c j)))
  have h2 : Y * V = p ^ (k + m) • Y'.map φ := by
    rw [hV, Matrix.mul_smul, ← Matrix.mul_assoc, ← hφ, Matrix.smul_mul, ← h1, smul_smul, smul_smul]
    congr 1
    linear_combination (p ^ k * p ^ m) * huu
  have h3 : ∀ j, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • (fun i => V i j) = p ^ (k + m) • (P *ᵥ w) := by
    intro j
    refine hlat _ (fun i => hVO i j) _ fun i => ⟨φ (Y' i j), ?_⟩
    exact congrFun (congrFun h2 i) j
  choose w hwO hw using h3
  refine ⟨Matrix.of fun i j => w j i, fun i j => hwO j i, ?_⟩
  have h4 : p ^ m • V = p ^ (k + m) • (P * Matrix.of fun i j => w j i) := by
    refine Matrix.ext fun i j => ?_
    exact congrFun (hw j) i
  apply cancel (k + m)
  apply cancel m
  rw [← h2, ← Matrix.mul_smul, h4, Matrix.mul_smul, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul, smul_comm]

theorem isUnit_saturated_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  intro l hl K bk τ hτ d N ρ hρ Y1 δ A1 hdet hδ hφ hg m P Y' hP hPdet hY' hlat hsat
  obtain ⟨-, -, h3, -, -, h6, h7⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨ht1, -, -, ht4⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  haveI : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have hlu : ¬ IsUnit (l : bk.S) := fun h => by
    have := h.map bk.evW
    rw [map_natCast] at this
    exact (WittVector.irreducible l (k := Cb l)).not_isUnit this
  have hev : ∀ s, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨k, δ', hnd, rfl⟩ := WfDvdMonoid.max_power_factor' hδ hlu
  obtain ⟨u', hu', huu⟩ := h3 δ' hnd
  have hφW : ((l : WCb l) ^ k * bk.evW δ') • (Y1.map (inclW l)).map (frobW l).toRingHom =
      Y1.map (inclW l) * A1.map bk.evW := by
    have := congrArg (fun M => Matrix.map M (inclW l)) hφ
    simp only [Matrix.map_mul] at this
    rw [show A1.map bk.evW = (A1.map bk.ev).map (inclW l) from rfl, ← this]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [BK.evW, RingHom.comp_apply, ← GlobalTheory.Prism.frobW_inclW]
    rfl
  obtain ⟨B, hB, hBφ⟩ := exists_frob_matrix bk.OE (frobW l).toRingHom (l : WCb l) hl0 (map_natCast _ _) h7
    (Y1.map (inclW l)) (A1.map bk.evW) P Y' k m (bk.evW δ') u' hu' huu (fun i j => hev _) hP hφW hY' hlat
  refine GlobalTheory.T.isUnit_of_saturated' l K bk d Y' B ?_ hB hBφ ?_ hsat
  · intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hdet hPdet this.symm
  · intro g hfix
    obtain ⟨t, ht⟩ := ht1
    obtain ⟨s, hs⟩ := ht4 (g : GQ l)
    set Z : Matrix (Fin d) (Fin d) (WCb l) := ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) with hZ
    have hZu : IsUnit Z := ((hρ g).map (algebraMap ℤ_[l] (Ainf l)).mapMatrix).map (inclW l).mapMatrix
    have e1 : (t : WCb l) ^ N • (Z * (Y1.map (inclW l)).map (galW l (g : GQ l))) =
        (s : WCb l) ^ N • Y1.map (inclW l) := by
      have := congrArg (fun M => Matrix.map M (inclW l)) (hg g hfix)
      have e : (Y1.map (inclW l)).map (galW l (g : GQ l)) = (Y1.map (Per.σA (g : GQ l))).map (inclW l) := by
        refine Matrix.ext fun i j => ?_
        exact GlobalTheory.Prism.galW_inclW _ _
      rw [e, hZ, ← Matrix.map_mul, ht, hs]
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun this i) j
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow] using this
    have e2 : (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) = (Y1.map (inclW l)).map (galW l (g : GQ l)) * P := by
      have eP : P.map (galW l (g : GQ l)) = P := by
        refine Matrix.ext fun i j => ?_
        exact h6 g hfix _ (hP i j)
      rw [← eP, ← Matrix.map_mul, ← hY']
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    refine ⟨((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z, ?_, ?_⟩
    · exact hZu.smul _
    · have e3 : (l : WCb l) ^ m • ((((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z) * Y'.map (galW l (g : GQ l))) =
          (l : WCb l) ^ m • Y' := by
        rw [← Matrix.mul_smul, e2, hY', ← Matrix.mul_assoc, Units.smul_def, Matrix.smul_mul, Units.val_pow_eq_pow_val,
          Units.val_mul, mul_pow, mul_smul, e1, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      refine Matrix.ext fun i j => ?_
      exact mul_left_cancel₀ (pow_ne_zero m hl0) (congrFun (congrFun e3 i) j)

end GlobalTheory.EtaleLattice
