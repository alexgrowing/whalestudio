import Mathlib
import Formalism.PeriodIntegrals.ChiExCM
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharExtend

namespace PI.UnitaryGroupMassFormula.ChiExCM

open NumberField

section

variable {E : Type} [Field E] [NumberField E]

noncomputable def spanHom : E →* Submodule (𝓞 E) E where
  toFun x := Submodule.span (𝓞 E) {x}
  map_one' := Submodule.one_eq_span.symm
  map_mul' x y := by
    show Submodule.span (𝓞 E) {x * y} = Submodule.span (𝓞 E) {x} * Submodule.span (𝓞 E) {y}
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

def normOne (c : E →+* E) : Subgroup Eˣ where
  carrier := {u | (u : E) * c u = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at *
    calc (a : E) * b * (c a * c b) = ((a : E) * c a) * ((b : E) * c b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at *
    rw [← mul_inv, ha, inv_one]

theorem mem_normOne (c : E →+* E) (u : Eˣ) : u ∈ normOne c ↔ (u : E) * c u = 1 := Iff.rfl

noncomputable def iota (c : E →+* E) : normOne c →* (Submodule (𝓞 E) E)ˣ :=
  (Units.map spanHom).comp (normOne c).subtype

theorem iota_val (c : E →+* E) (u : normOne c) :
    ((iota c u : (Submodule (𝓞 E) E)ˣ) : Submodule (𝓞 E) E) = Submodule.span (𝓞 E) {((u : Eˣ) : E)} := rfl

noncomputable def lam (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ) : normOne c →* ℂˣ :=
  (∏ s, (Units.map (emb s).toMonoidHom).comp (normOne c).subtype)⁻¹

theorem lam_apply (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ) (u : normOne c) :
    ((lam c S emb u : ℂˣ) : ℂ) = ∏ s, (emb s ((u : Eˣ) : E))⁻¹ := by
  simp [lam, Units.coe_prod, Finset.prod_inv_distrib]

theorem kron_step (c : E →+* E) (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x))
    (u : E) (hu : u * c u = 1) (h1 : Submodule.span (𝓞 E) {u} = 1) : ∃ m : ℕ, 0 < m ∧ u ^ m = 1 := by
  rw [Submodule.one_eq_span, Submodule.span_singleton_eq_span_singleton] at h1
  obtain ⟨a, ha⟩ := h1
  rw [Units.smul_def, Algebra.smul_def] at ha
  have h3 : algebraMap (𝓞 E) E (a : 𝓞 E) * algebraMap (𝓞 E) E ((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hu' : u = algebraMap (𝓞 E) E ((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) :=
    mul_left_cancel₀ (left_ne_zero_of_mul_eq_one ha) (ha.trans h3.symm)
  have hint : IsIntegral ℤ u := by rw [hu']; exact RingOfIntegers.isIntegral_coe _
  have hn : ∀ φ : E →+* ℂ, ‖φ u‖ = 1 := by
    intro φ
    have h4 : φ u * (starRingEnd ℂ) (φ u) = 1 := by rw [← hc, ← map_mul, hu, map_one]
    rw [Complex.mul_conj'] at h4
    have h5 : ‖φ u‖ ^ 2 = 1 := by exact_mod_cast h4
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5
  obtain ⟨n, hn0, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := E) (A := ℂ) hint hn
  exact ⟨n, hn0, hpow⟩

theorem ker_le (c : E →+* E) (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x))
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (hμ : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ s, emb s x = 1) :
    (iota c).ker ≤ (lam c S emb).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have h1 : Submodule.span (𝓞 E) {((u : Eˣ) : E)} = 1 := by
    rw [← iota_val, hu, Units.val_one]
  ext
  rw [lam_apply, Finset.prod_inv_distrib, hμ _ (kron_step c hc _ ((mem_normOne c _).1 u.2) h1), inv_one, Units.val_one]

noncomputable def chi0 (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ)
    (hker : (iota c).ker ≤ (lam c S emb).ker) : (iota c).range →* ℂˣ :=
  (QuotientGroup.lift (iota c).ker (lam c S emb) hker).comp
    (QuotientGroup.quotientKerEquivRange (iota c)).symm.toMonoidHom

theorem normOne_character_apply (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ)
    (hker : (iota c).ker ≤ (lam c S emb).ker) (u : normOne c) :
    chi0 c S emb hker ⟨iota c u, MonoidHom.mem_range.2 ⟨u, rfl⟩⟩ = lam c S emb u := by
  have h : (QuotientGroup.quotientKerEquivRange (iota c)).symm ⟨iota c u, MonoidHom.mem_range.2 ⟨u, rfl⟩⟩ =
      (u : normOne c ⧸ (iota c).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [chi0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]

end

theorem main : PI.ChiExCM := by
  intro E _ _ c hc S _ emb hμ
  classical
  obtain ⟨ψ, hψ⟩ := PI.character_extension_exists (Submodule (𝓞 E) E)ˣ (iota c).range (chi0 c S emb (ker_le c hc S emb hμ))
  refine ⟨fun 𝔞 => if h : IsUnit 𝔞 then ((ψ h.unit : ℂˣ) : ℂ) else 0, ?_, ?_⟩
  · rintro 𝔞 𝔟 ⟨𝔞', -, h𝔞⟩ ⟨𝔟', -, h𝔟⟩
    have ha : IsUnit 𝔞 := IsUnit.of_mul_eq_one _ h𝔞
    have hb : IsUnit 𝔟 := IsUnit.of_mul_eq_one _ h𝔟
    have hab : IsUnit (𝔞 * 𝔟) := ha.mul hb
    have e : hab.unit = ha.unit * hb.unit := Units.ext rfl
    simp only [dif_pos hab, dif_pos ha, dif_pos hb, e, map_mul, Units.val_mul]
  · intro z hz
    let u : Eˣ := Units.mkOfMulEqOne z (c z) hz
    have hu : u ∈ normOne c := hz
    have hval : ((iota c ⟨u, hu⟩ : (Submodule (𝓞 E) E)ˣ) : Submodule (𝓞 E) E) = Submodule.span (𝓞 E) {z} := rfl
    have hunit : IsUnit (Submodule.span (𝓞 E) {z}) := hval ▸ (iota c ⟨u, hu⟩).isUnit
    have e : hunit.unit = iota c ⟨u, hu⟩ := Units.ext hval.symm
    simp only [dif_pos hunit, e]
    rw [hψ ⟨iota c ⟨u, hu⟩, MonoidHom.mem_range.2 ⟨⟨u, hu⟩, rfl⟩⟩, normOne_character_apply, lam_apply]
    rfl

end PI.UnitaryGroupMassFormula.ChiExCM
