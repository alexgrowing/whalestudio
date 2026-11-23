import Formalism.SharpRestriction.GlobalSchurBounds.Joints

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField

section General

variable {M : Type*} [Field M] [NumberField M]

theorem index_span_smul (d : M) (hd : d ≠ 0) (a : 𝓞 M) :
    ((Submodule.span (𝓞 M) {a • d}).toAddSubgroup.addSubgroupOf
      (Submodule.span (𝓞 M) {d}).toAddSubgroup).index = (Algebra.norm ℤ a).natAbs := by
  let f : 𝓞 M →+ (Submodule.span (𝓞 M) {d}).toAddSubgroup :=
    { toFun := fun x => ⟨x • d, Submodule.smul_mem _ x (Submodule.mem_span_singleton_self d)⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [add_smul] }
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨x, rfl⟩
  have hcomap : ((Submodule.span (𝓞 M) {a • d}).toAddSubgroup.addSubgroupOf
      (Submodule.span (𝓞 M) {d}).toAddSubgroup).comap f = (Ideal.span {a} : Ideal (𝓞 M)).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      Submodule.mem_toAddSubgroup]
    show x • d ∈ Submodule.span (𝓞 M) {a • d} ↔ x ∈ Ideal.span {a}
    rw [Submodule.mem_span_singleton, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [smul_smul] at hc
      exact RingOfIntegers.coe_injective (mul_right_cancel₀ hd (by simpa only [Algebra.smul_def] using hc))
    · rintro ⟨c, rfl⟩
      exact ⟨c, by rw [smul_smul]⟩
  rw [← AddSubgroup.index_comap_of_surjective _ hsurj, hcomap, ← Ideal.absNorm_span_singleton,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem sum_log_emb (a : 𝓞 M) (ha : a ≠ 0) :
    ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (‖ρ (a : M)‖ ^ 2) = 2 * Real.log ((Algebra.norm ℤ a).natAbs : ℝ) := by
  have ha' : (a : M) ≠ 0 := fun h => ha (by exact_mod_cast h)
  have hne : ∀ ρ : M →ₐ[ℚ] ℂ, ‖ρ (a : M)‖ ≠ 0 := fun ρ => by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact ha'
  calc ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (‖ρ (a : M)‖ ^ 2)
      = ∑ ρ : M →ₐ[ℚ] ℂ, 2 * Real.log ‖ρ (a : M)‖ := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Real.log_pow]
        push_cast
        ring
    _ = 2 * Real.log (∏ ρ : M →ₐ[ℚ] ℂ, ‖ρ (a : M)‖) := by
        rw [← Finset.mul_sum, Real.log_prod (fun ρ _ => hne ρ)]
    _ = 2 * Real.log ((Algebra.norm ℤ a).natAbs : ℝ) := by
        congr 2
        rw [← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ, ← Algebra.coe_norm_int]
        simp [Nat.cast_natAbs]

end General

def conjOf {D : D7} {M : IntermediateField ℚ ℂ} (e : D.what₂.LL ≃+* M) (s : D.what₂.LL →+* ℂ) : M →ₐ[ℚ] ℂ :=
  (s.comp (e.symm : M →+* D.what₂.LL)).toRatAlgHom

def conjEquiv {D : D7} {M : IntermediateField ℚ ℂ} (e : D.what₂.LL ≃+* M) : (D.what₂.LL →+* ℂ) ≃ (M →ₐ[ℚ] ℂ) where
  toFun := conjOf e
  invFun ρ := (ρ : M →+* ℂ).comp (e : D.what₂.LL →+* M)
  left_inv s := by ext y; simp [conjOf]
  right_inv ρ := by ext y; simp [conjOf]

def OmegaCompatible (D : D7) (δ : ℂ) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (e : D.what₂.LL ≃+* M),
    (∀ y, ((e y : M) : ℂ) = D.what₂.embLL y) ∧
    TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M ∧
    ∀ τ, ∃ d : M, TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {d} ∧
      ∀ s : D.what₂.LL →+* ℂ, D.gx.Om τ s =
        (Real.pi * ‖conjOf e s d‖ ^ 2 / TaylorLogMetric.area (TaylorLogMetric.lamConj M (conjOf e s) (TaylorLogMetric.lamOf D D.host.ccK δ)))⁻¹

theorem omLink_of_tied {D : D7} {δ : ℂ} (h : OmegaCompatible D δ) : OmLink D (TaylorLogMetric.tor0 D D.host.ccK δ) := by
  obtain ⟨M, hM, e, -, hData, hτ⟩ := h
  refine ⟨M, hM, hData, fun τ => ?_⟩
  obtain ⟨d, hd, hOm⟩ := hτ τ
  set Λ := TaylorLogMetric.lamOf D D.host.ccK δ with hΛ
  have hX : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < Real.pi * ‖ρ d‖ ^ 2 / TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ Λ) := by
    intro ρ
    have h1 := D.gx.Om_pos τ ((conjEquiv e).symm ρ)
    rw [hOm] at h1
    have h2 : conjOf e ((conjEquiv e).symm ρ) = ρ := (conjEquiv e).apply_symm_apply ρ
    rw [h2] at h1
    exact inv_pos.mp h1
  have hcardM : Fintype.card (M →ₐ[ℚ] ℂ) = Module.finrank ℚ M := AlgHom.card ℚ M ℂ
  have hcardLL : Fintype.card (D.what₂.LL →+* ℂ) = Fintype.card (M →ₐ[ℚ] ℂ) :=
    Fintype.card_congr (conjEquiv e)
  have hpos : 0 < Fintype.card (M →ₐ[ℚ] ℂ) := by rw [hcardM]; exact Module.finrank_pos
  obtain ⟨ρ0⟩ : Nonempty (M →ₐ[ℚ] ℂ) := Fintype.card_pos_iff.mp hpos
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 := hX ρ0
    rw [h0, map_zero, norm_zero] at h1
    simp at h1
  have hL : D.gx.logOmMean τ = -(∑ ρ : M →ₐ[ℚ] ℂ, TaylorLogMetric.logMet M Λ ρ d) / (Module.finrank ℚ M : ℝ) := by
    unfold Formalism.BasicNotions.GlobalExtra.logOmMean
    rw [hcardLL, hcardM]
    congr 1
    rw [← Finset.sum_neg_distrib, ← (conjEquiv e).sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hOm, Real.log_inv]
    rfl
  have hR : TaylorLogMetric.meanLogOm D Λ M τ = -(∑ ρ : M →ₐ[ℚ] ℂ, TaylorLogMetric.logMet M Λ ρ d) / (Module.finrank ℚ M : ℝ) := by
    simp only [TaylorLogMetric.meanLogOm]
    have hspec := Classical.epsilon_spec (p := fun s : M => s ≠ 0 ∧ s ∈ TaylorLogMetric.ellT D M τ)
      ⟨d, hd0, by rw [hd]; exact Submodule.mem_span_singleton_self d⟩
    set s₀ := Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ TaylorLogMetric.ellT D M τ) with hs₀
    obtain ⟨hs0, hsmem⟩ := hspec
    rw [hd] at hsmem
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp hsmem
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hs0 (by rw [← hx, zero_smul])
    rw [hd, ← hx, index_span_smul d hd0 x]
    have hsplit : ∀ ρ : M →ₐ[ℚ] ℂ, TaylorLogMetric.logMet M Λ ρ (x • d) =
        Real.log (‖ρ (x : M)‖ ^ 2) + TaylorLogMetric.logMet M Λ ρ d := by
      intro ρ
      have hxM : (x : M) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_injective (by simpa using h))
      have hρx : ρ (x : M) ≠ 0 := (map_ne_zero ρ).mpr hxM
      simp only [TaylorLogMetric.logMet]
      rw [Algebra.smul_def, map_mul, norm_mul, mul_pow]
      have e1 : Real.pi * (‖ρ (algebraMap (𝓞 M) M x)‖ ^ 2 * ‖ρ d‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ Λ) =
          ‖ρ (x : M)‖ ^ 2 * (Real.pi * ‖ρ d‖ ^ 2 / TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ Λ)) := by
        ring
      rw [e1, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hρx)) (hX ρ).ne']
    simp_rw [hsplit, Finset.sum_add_distrib, sum_log_emb x hx0]
    ring
  rw [hL]
  exact hR.symm

end Formalism.L2.GlobalTheoryTheory

end
