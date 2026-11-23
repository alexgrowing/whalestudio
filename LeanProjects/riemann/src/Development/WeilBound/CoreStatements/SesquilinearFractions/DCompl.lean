import Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def orthogonalFamilyAlt (D : Datum H) {p : ℕ} (x' : Fin p → D.La) : Submodule (𝓞 E) D.La where
  carrier := {y | ∀ a, sesq D (x' a) y = 0}
  add_mem' := by
    intro y y' hy hy' a
    rw [(sesq_sesquilinear_properties D).2.2.1, hy a, hy' a, add_zero]
  zero_mem' := by
    intro a
    have := (sesq_sesquilinear_properties D).2.2.2.2.1 0 (x' a) 0
    simpa using this
  smul_mem' := by
    intro c y hy a
    rw [(sesq_sesquilinear_properties D).2.2.2.2.1, hy a, mul_zero]

theorem nsmul_injective_lattice (D : Datum H) {m : ℕ} (hm : m ≠ 0) {y y' : D.La} (h : m • y = m • y') : y = y' := by
  haveI := D.fin
  haveI := D.proj
  have hm' : (m : 𝓞 E) ≠ 0 := by exact_mod_cast hm
  have h' : (m : 𝓞 E) • y = (m : 𝓞 E) • y' := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h
  exact smul_right_injective _ hm' h'

theorem padic_norm_sesq_le (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) (y y' : D.La) :
    ‖j (sesq D y y')‖ ≤ Real.exp (-logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := by
  have hinj : Function.Injective (j.comp (algebraMap (𝓞 E) E)) :=
    j.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨a, ha, ha0, -, hL⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) _ hinj hne
  have hca : (j.comp (algebraMap (𝓞 E) E)) a = j (a : E) := rfl
  have hja : 0 < ‖j (a : E)‖ := by
    rw [← hca]
    exact norm_pos_iff.mpr ((map_ne_zero_iff _ hinj).mpr ha0)
  rw [hL, hca, Real.exp_neg, Real.exp_log hja]
  obtain ⟨b, hb⟩ := (sesq_sesquilinear_properties D).2.2.2.2.2.2 a ha y y'
  have hb1 : ‖j (b : E)‖ ≤ 1 :=
    (GlobalTheory.T.padic_integral_iff_denominator E ℓ (b : E)).mpr ⟨1, b, Nat.Prime.not_dvd_one ℓ.prop, by simp⟩ j
  have hm : ‖j (a : E)‖ * ‖j (sesq D y y')‖ ≤ 1 := by
    rw [← norm_mul, ← map_mul, hb]
    exact hb1
  calc ‖j (sesq D y y')‖ = ‖j (a : E)‖⁻¹ * (‖j (a : E)‖ * ‖j (sesq D y y')‖) := by
        field_simp
    _ ≤ ‖j (a : E)‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hja.le)
    _ = ‖j (a : E)‖⁻¹ := mul_one _

def pairingVector (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y : D.La) : Fin p → E := fun b => sesq D (x' b) y

def projectionCoeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y : D.La) : Fin p → E :=
  (gramE D x')⁻¹ *ᵥ pairingVector D x' y

theorem padic_norm_projectionCoeffs_le (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hdet : (gramE D x').det ≠ 0)
    (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) (y : D.La) (a : Fin p)
    (j : E →+* ℂ_[ℓ]) : ‖j (projectionCoeffs D x' y a)‖ ≤ 1 := by
  classical
  set R := Real.exp (-logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hdetn : ‖j (gramE D x').det‖ = R ^ p := by
    have h0 : 0 < ‖j (gramE D x').det‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hdet)
    rw [← Real.exp_log h0, hlog j, hR, ← Real.exp_nat_mul]
    congr 1
    ring
  have he : projectionCoeffs D x' y a =
      (gramE D x').det⁻¹ * ((gramE D x').updateCol a (pairingVector D x' y)).det := by
    rw [projectionCoeffs, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec,
      ← Matrix.cramer_eq_adjugate_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
  have hb : ‖j ((gramE D x').updateCol a (pairingVector D x' y)).det‖ ≤ R ^ p := by
    rw [RingHom.map_det]
    have := GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] (Fin p) (j.mapMatrix ((gramE D x').updateCol a (pairingVector D x' y)))
      R hR0.le (fun b c => by
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        split_ifs
        · exact padic_norm_sesq_le D ℓ j _ _
        · simpa [gramE] using padic_norm_sesq_le D ℓ j (x' b) (x' c))
    simpa using this
  rw [he, map_mul, norm_mul, map_inv₀, norm_inv, hdetn]
  calc (R ^ p)⁻¹ * ‖j ((gramE D x').updateCol a (pairingVector D x' y)).det‖ ≤ (R ^ p)⁻¹ * R ^ p :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := inv_mul_cancel₀ (pow_pos hR0 p).ne'

theorem projectionCoeffs_add (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y y' : D.La) :
    projectionCoeffs D x' (y + y') = projectionCoeffs D x' y + projectionCoeffs D x' y' := by
  have : pairingVector D x' (y + y') = pairingVector D x' y + pairingVector D x' y' := by
    funext b; simp [pairingVector, (sesq_sesquilinear_properties D).2.2.1]
  simp [projectionCoeffs, this, Matrix.mulVec_add]

theorem projectionCoeffs_smul (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (c : 𝓞 E) (y : D.La) :
    projectionCoeffs D x' (c • y) = IsCMField.complexConj E (c : E) • projectionCoeffs D x' y := by
  have : pairingVector D x' (c • y) = IsCMField.complexConj E (c : E) • pairingVector D x' y := by
    funext b; simp [pairingVector, (sesq_sesquilinear_properties D).2.2.2.2.1]
  simp [projectionCoeffs, this, Matrix.mulVec_smul]

theorem gram_mulVec_projection_coeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (hdet : (gramE D x').det ≠ 0) (y : D.La) :
    gramE D x' *ᵥ projectionCoeffs D x' y = pairingVector D x' y := by
  rw [projectionCoeffs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]

theorem sesq_integral_combination (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (d : Fin p → 𝓞 E) (b : Fin p) :
    sesq D (x' b) (∑ a, d a • x' a) = ∑ a, gramE D x' b a * IsCMField.complexConj E (d a : E) := by
  let f : D.La →+ E := AddMonoidHom.mk' (sesq D (x' b)) (fun y y' => (sesq_sesquilinear_properties D).2.2.1 _ _ _)
  have hf : sesq D (x' b) (∑ a, d a • x' a) = f (∑ a, d a • x' a) := rfl
  rw [hf, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  show sesq D (x' b) (d a • x' a) = _
  rw [(sesq_sesquilinear_properties D).2.2.2.2.1, mul_comm]
  simp [gramE]

end GlobalTheory.CompanionTheory.Ar.Fl

end
