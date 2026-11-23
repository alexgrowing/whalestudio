import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem quadAlg_isField_or_split {K A : Type} [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
    (h2 : (2 : K) ≠ 0) (τ : A →+* A) (hτ : ∀ k, τ (algebraMap K A k) = algebraMap K A k)
    (δ : A) (d : K) (hd : d ≠ 0) (hδ : δ * δ = algebraMap K A d) (hs : τ δ = -δ)
    (hsp : ∀ x : A, ∃ a b : K, x = algebraMap K A a + algebraMap K A b * δ) :
    IsField A ∨ ∃ φ : A ≃+* K × K, ∀ x, φ (τ x) = (φ x).swap := by
  by_cases hsq : ∃ s : K, d = s * s
  · right
    obtain ⟨s, rfl⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hd (by simp [h])
    set e : A := algebraMap K A (2⁻¹) + algebraMap K A (2⁻¹ * s⁻¹) * δ with he
    have h1 : algebraMap K A (2⁻¹) * 2 = 1 := by
      rw [show (2 : A) = algebraMap K A 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ h2, map_one]
    have h3 : algebraMap K A (s⁻¹) * algebraMap K A s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs0, map_one]
    rw [map_mul] at hδ he
    have hee : e * e = e := by
      rw [he]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (p + p * q * δ) * h1 + p ^ 2 * q ^ 2 * hδ + p ^ 2 * (q * t + 1) * h3
    have hτe : τ e = 1 - e := by
      rw [he]
      simp only [map_add, map_mul, hτ, hs]
      linear_combination h1
    have hτe' : τ (1 - e) = e := by
      rw [map_sub, map_one, hτe]; ring
    have hδe : δ = algebraMap K A s * e + algebraMap K A (-s) * (1 - e) := by
      rw [he, map_neg]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (-t - t * q * δ) * h1 - δ * h3
    have he0 : e ≠ 0 := by
      intro h
      rw [h] at hτe
      simp at hτe
    have he1 : 1 - e ≠ 0 := by
      intro h
      rw [h, map_zero] at hτe'
      exact he0 hτe'.symm
    let ψ : K × K →+* A :=
      { toFun := fun x => algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e)
        map_one' := by simp
        map_zero' := by simp
        map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
        map_mul' := by
          intro x y
          simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
          generalize algebraMap K A x.1 = a
          generalize algebraMap K A x.2 = b
          generalize algebraMap K A y.1 = c
          generalize algebraMap K A y.2 = f
          linear_combination (-(a - b) * (c - f)) * hee }
    have hψ : ∀ x, ψ x = algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e) := fun _ => rfl
    have hinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      rw [hψ] at hx
      have ha : algebraMap K A x.1 * e = 0 := by
        linear_combination e * hx - (algebraMap K A x.1 - algebraMap K A x.2) * hee
      have hb : algebraMap K A x.2 * (1 - e) = 0 := by
        linear_combination hx - ha
      rw [← Algebra.smul_def, smul_eq_zero] at ha hb
      exact Prod.ext (ha.resolve_right he0) (hb.resolve_right he1)
    have hsurj : Function.Surjective ψ := by
      intro x
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨(a + b * s, a - b * s), ?_⟩
      rw [hψ]
      simp only [map_add, map_sub, map_mul]
      rw [map_neg] at hδe
      linear_combination (-algebraMap K A b) * hδe
    refine ⟨(RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).surjective x
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq]
    change τ (ψ y) = ψ y.swap
    simp only [hψ, map_add, map_mul, hτ, hτe, hτe', Prod.fst_swap,
      Prod.snd_swap]
    ring
  · left
    refine ⟨exists_pair_ne A, mul_comm, fun {x} hx => ?_⟩
    obtain ⟨a, b, rfl⟩ := hsp x
    have hn : a * a - d * (b * b) ≠ 0 := by
      intro h
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using h
        subst this
        simp at hx
      · refine hsq ⟨a / b, ?_⟩
        field_simp
        linear_combination -h
    refine ⟨(algebraMap K A a - algebraMap K A b * δ) * algebraMap K A (a * a - d * (b * b))⁻¹, ?_⟩
    have h4 : algebraMap K A (a * a - d * (b * b)) * algebraMap K A (a * a - d * (b * b))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn, map_one]
    generalize algebraMap K A (a * a - d * (b * b))⁻¹ = u at *
    simp only [map_sub, map_mul] at h4
    linear_combination h4 - (algebraMap K A b) ^ 2 * u * hδ

theorem quadExt_exists_skew {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ a, σ (σ a) = a) (hne : ∃ a, σ a ≠ a) :
    ∃ (δ : E) (d : F), d ≠ 0 ∧ δ * δ = algebraMap F E d ∧ σ δ = -δ ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
  obtain ⟨t, ht⟩ := hne
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  set δ := t - σ t with hδ
  have hδ0 : δ ≠ 0 := fun h => ht (sub_eq_zero.mp h).symm
  have hs : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h' := congrArg σ h
    rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, hs,
      map_one, map_zero, ← Algebra.smul_def, ← Algebra.smul_def, smul_neg] at h'
    have ha : (2 * a) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination h + h'
    have hb : (2 * b) • δ = 0 := by
      rw [two_mul, add_smul]; linear_combination h - h'
    rw [smul_eq_zero] at ha hb
    exact ⟨by simpa using ha, by simpa [hδ0] using hb⟩
  have hsp : ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
    intro x
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have h := B.sum_repr x
    rw [Fin.sum_univ_two] at h
    have h0 : B 0 = 1 := by simp [B]
    have h1 : B 1 = δ := by simp [B]
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
    exact h.symm
  obtain ⟨a, b, hab⟩ := hsp (δ * δ)
  have h' := congrArg σ hab
  simp only [map_add, map_mul, hs, AlgHom.commutes] at h'
  have hd : δ * δ = algebraMap F E a := by
    have h2 : (2 : E) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    linear_combination hab + h'
  refine ⟨δ, a, ?_, hd, hs, hsp⟩
  rintro rfl
  simp [hδ0] at hd

theorem quadBaseChange_isField_or_split :
    ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field K] [Algebra F K] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ a, σ (σ a) = a) → (∃ a, σ a ≠ a) → (IsField (K ⊗[F] E) ∨ ∃ φ : K ⊗[F] E ≃+* K × K, ∀ x, φ (sigR K σ x) = (φ x).swap) ∧ ∃ (δ : K ⊗[F] E) (d : K), d ≠ 0 ∧ δ * δ = algebraMap K (K ⊗[F] E) d ∧ sigR K σ δ = -δ ∧ ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * δ := by
  intro F E K _ _ _ _ _ _ σ hr hσ hne
  obtain ⟨δ, d, hd, hδ, hs, hsp⟩ := quadExt_exists_skew σ hr hσ hne
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hd' : algebraMap F K d ≠ 0 := by simpa using hd
  have hδ' : ((1 : K) ⊗ₜ[F] δ) * ((1 : K) ⊗ₜ[F] δ) =
      algebraMap K (K ⊗[F] E) (algebraMap F K d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, one_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply']
  have hsig : ∀ (k : K) (x : E), sigR K σ (k ⊗ₜ[F] x) = k ⊗ₜ[F] σ x := fun k x => by
    simp [sigR]
  have hs' : sigR K σ ((1 : K) ⊗ₜ[F] δ) = -((1 : K) ⊗ₜ[F] δ) := by
    rw [hsig, hs, TensorProduct.tmul_neg]
  have hsp' : ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a +
      algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] δ) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul k x =>
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨a • k, b • k, ?_⟩
      rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul]
      simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, e, rfl⟩ := hy
      exact ⟨a + c, b + e, by simp only [map_add]; ring⟩
  refine ⟨quadAlg_isField_or_split two_ne_zero (sigR K σ) (fun k => ?_) _ _ hd' hδ' hs' hsp',
    _, _, hd', hδ', hs', hsp'⟩
  rw [Algebra.TensorProduct.algebraMap_apply, hsig, map_one]

end GlobalTheory
