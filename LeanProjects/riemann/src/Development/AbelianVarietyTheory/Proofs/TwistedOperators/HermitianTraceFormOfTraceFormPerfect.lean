import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS

section

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem form_conj_symm (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A}
    (hJ : IsHerm σ J) (a b : n → A) : σ (form σ J b a) = form σ J a b := by
  have hJij : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [cT] using this
  simp only [form, hform, map_sum, map_mul, hσ, hJij]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eq_zero_of_form_eq_zero (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a : n → A) (h0 : ∀ w, form σ J a w = 0) : a = 0 := by
  have hJa : J *ᵥ a = 0 := by
    funext i
    have := h0 (Pi.single i 1)
    have hs : (fun k => σ ((Pi.single i (1 : A) : n → A) k)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [form, hform_eq, hs] at this
    simpa [dotProduct, Pi.single_apply] using this
  calc a = (J⁻¹ * J) *ᵥ a := by rw [Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hJa, Matrix.mulVec_zero]

end

theorem traceClause_of_tracePerfect (hP : TracePerfect) : TraceClause := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  haveI := quad_finite h.quad
  haveI := genAlg_isReduced h hA
  obtain ⟨b⟩ := hA.2.2.1
  haveI : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  haveI : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  obtain ⟨v, hv⟩ := hA.2.2.2.1
  obtain ⟨τ, hτ, hττ, hτE, hplus⟩ := exists_adjEquiv h hA
  have hP' := hP F E (genAlg (γ : Matrix n n E))
  let φ : genAlg (γ : Matrix n n E) →ₗ[E] E :=
    { toFun := fun y => form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v
      map_add' := fun a b => by
        simp only [form, hform_eq, Subalgebra.coe_add, Matrix.add_mulVec, Matrix.mulVec_add,
          dotProduct_add]
      map_smul' := fun c a => by
        simp only [form, hform_eq, Subalgebra.coe_smul, Matrix.smul_mulVec,
          Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul] }
  obtain ⟨x, hx⟩ := hP'.2 φ
  have hxy : ∀ y, Algebra.trace E _ (x * y) = form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v :=
    fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this

  have hK : ∀ y y' : genAlg (γ : Matrix n n E),
      form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) ((y' : Matrix n n E) *ᵥ v) =
        Algebra.trace E _ (x * (τ y' * y)) := fun y y' => by
    rw [hxy, form_adj _ h.nondeg, ← hτ, Matrix.mulVec_mulVec]
    rfl

  let σE : E ≃+* E := RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective h.quad.invol)
  have hTr : ∀ z, Algebra.trace E _ (τ z) = σ (Algebra.trace E (genAlg (γ : Matrix n n E)) z) := by
    intro z
    have he : (algebraMap E (genAlg (γ : Matrix n n E))).comp (σE : E →+* E) =
        (τ.toRingEquiv : genAlg (γ : Matrix n n E) →+* genAlg (γ : Matrix n n E)).comp
          (algebraMap E (genAlg (γ : Matrix n n E))) := RingHom.ext fun e => (hτE e).symm
    have := Algebra.trace_eq_of_equiv_equiv σE τ.toRingEquiv he z
    rw [this]
    exact (σE.apply_symm_apply _).symm

  have hxτ : τ x = x := by
    refine hP'.1 (LinearMap.ext fun y => ?_)
    simp only [Algebra.traceForm_apply]
    have e1 : τ x * y = τ (x * (τ y * 1)) := by rw [mul_one, map_mul, hττ]
    rw [e1, hTr, ← hK]
    have hs := form_conj_symm (σ : E →+* E) h.quad.invol h.herm
      ((y : Matrix n n E) *ᵥ v) (((1 : genAlg (γ : Matrix n n E)) : Matrix n n E) *ᵥ v)
    simp only [RingHom.coe_coe] at hs
    rw [hs, hK, map_one, one_mul]
  have hxplus : x ∈ plusAlg σ J (γ : Matrix n n E) := (hplus x).2 hxτ

  have hinj : ∀ y : genAlg (γ : Matrix n n E), x * y = 0 → y = 0 := by
    intro y hy
    have h0 : (y : Matrix n n E) *ᵥ v = 0 := by
      refine eq_zero_of_form_eq_zero (σ : E →+* E) h.nondeg _ fun w => ?_
      obtain ⟨y', rfl⟩ := hv.2 w
      simp only
      rw [hK, mul_left_comm, hy, mul_zero, map_zero]
    refine hv.1 ?_
    simp only [h0, ZeroMemClass.coe_zero, Matrix.zero_mulVec]

  let xp : plusAlg σ J (γ : Matrix n n E) := ⟨x, hxplus⟩
  haveI : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have hsurj : Function.Surjective (LinearMap.mulLeft F xp) := by
    refine LinearMap.injective_iff_surjective.1 fun a c hac => ?_
    have : x * ((a : genAlg (γ : Matrix n n E)) - c) = 0 := by
      have := congrArg Subtype.val hac
      simp only [LinearMap.mulLeft_apply] at this
      rw [mul_sub]; exact sub_eq_zero.2 this
    exact Subtype.ext (sub_eq_zero.1 (hinj _ this))
  obtain ⟨w, hw⟩ := hsurj 1
  have hu : IsUnit xp := ⟨⟨xp, w, hw, by rw [mul_comm]; exact hw⟩, rfl⟩
  refine ⟨hu.unit, v, hv, fun y y' => ⟨τ y', hτ y', ?_⟩⟩
  rw [hK]
  congr 1
  change x * (τ y' * y) = x * y * τ y'
  ring

end GlobalTheory.RegSS
