import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfTheta

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

set_option linter.deprecated false

def ThetaSpan : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ θ : 𝓞 E,
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ) →
    ∀ x ∈ OEv (E := E) v, ∃ a0 a1 : v.adicCompletionIntegers F,
      x = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * inclR (F := F) (Fv F v) (θ : E)

theorem theta_exists (h : IsCMExt F E σ) : ∃ θ : 𝓞 E,
    (∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) ∧
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ) := by
  classical
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finite_res v
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hcard : Nat.card (QE (E := E) v) = Nat.card (𝓞 F ⧸ v.asIdeal) ^ 2 := card_QE σ v h
  have hk : 1 < Nat.card (𝓞 F ⧸ v.asIdeal) := Finite.one_lt_card
  have hpos : Nat.card (QE (E := E) v) ≠ 0 := by
    rw [hcard]
    positivity
  haveI : Finite (QE (E := E) v) := Nat.finite_of_card_ne_zero hpos
  haveI : Nontrivial (QE (E := E) v) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    nlinarith
  have hx : ∃ x : QE (E := E) v, x ∉ Set.range (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)) := by
    by_contra hne
    push_neg at hne
    have hs : Function.Surjective (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)) := fun y => hne y
    have hle := Nat.card_le_card_of_surjective _ hs
    rw [hcard] at hle
    nlinarith
  obtain ⟨x, hx⟩ := hx
  obtain ⟨θ, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hind : ∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0 := by
    intro a0 a1 h0
    by_cases ha1 : a1 = 0
    · subst ha1
      simp only [map_zero, zero_mul, add_zero] at h0
      exact ⟨(algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)).injective (by rw [h0, map_zero]), rfl⟩
    · exfalso
      apply hx
      refine ⟨-(a0 * a1⁻¹), ?_⟩
      have hinv : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1⁻¹ *
          algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ ha1, map_one]
      rw [map_neg, map_mul]
      linear_combination (-(algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1⁻¹)) * h0 +
        (Ideal.Quotient.mk (IE (E := E) v) θ) * hinv
  refine ⟨θ, hind, ?_⟩
  let f : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) → QE (E := E) v := fun p =>
    algebraMap _ (QE (E := E) v) p.1 + algebraMap _ (QE (E := E) v) p.2 * Ideal.Quotient.mk (IE (E := E) v) θ
  have hinj : Function.Injective f := by
    intro p p' hpp
    have h0 := hind (p.1 - p'.1) (p.2 - p'.2) (by
      simp only [f] at hpp
      rw [map_sub, map_sub]
      linear_combination hpp)
    exact Prod.ext (sub_eq_zero.mp h0.1) (sub_eq_zero.mp h0.2)
  have hbij := bij_of_card f hinj (by rw [Nat.card_prod, hcard, sq])
  intro q
  obtain ⟨p, hp⟩ := hbij.2 q
  exact ⟨p.1, p.2, hp.symm⟩

theorem theta_indep (h : IsCMExt F E σ) (θ : 𝓞 E)
    (h3 : ∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) :
    ∀ a0 a1 : Fv F v, sc (E := E) v a0 + sc (E := E) v a1 * inclR (F := F) (Fv F v) (θ : E) = 0 →
      a0 = 0 ∧ a1 = 0 := by
  classical
  intro a0 a1 h0
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hθ : ∀ f : F, algebraMap F E f ≠ (θ : E) := by
    intro f hf
    have hint : IsIntegral ℤ f := (isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom)
        (algebraMap F E).injective).mp (by
      show IsIntegral ℤ (algebraMap F E f)
      rw [hf]
      exact RingOfIntegers.isIntegral_coe θ)
    have hg : θ = algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩ := by
      apply RingOfIntegers.ext
      rw [← hf]
      rfl
    have hz := h3 (-(Ideal.Quotient.mk _ ⟨f, hint⟩)) 1 (by
      rw [map_neg, map_one, one_mul, hg]
      show -Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩) +
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩) = 0
      exact neg_add_cancel _)
    exact one_ne_zero hz.2
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
      exact ⟨(algebraMap F E).injective (by rw [hst, map_zero]), rfl⟩
    · exfalso
      apply hθ (-(s * t⁻¹))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have hinv : algebraMap F E t⁻¹ * algebraMap F E t = 1 := by
        rw [← map_mul, inv_mul_cancel₀ ht, map_one]
      rw [map_neg, map_mul]
      linear_combination (-(algebraMap F E t⁻¹)) * hst + (θ : E) * hinv
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, h.2.2.1])
  let b' := Algebra.TensorProduct.basis (Fv F v) b
  have hb : ![(1 : Fv F v) ⊗ₜ[F] (1 : E), (1 : Fv F v) ⊗ₜ[F] (θ : E)] = ⇑b' := by
    ext i
    fin_cases i <;>
      simp [b', b, Algebra.TensorProduct.basis_apply, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hli' : LinearIndependent (Fv F v) ![(1 : Fv F v) ⊗ₜ[F] (1 : E), (1 : Fv F v) ⊗ₜ[F] (θ : E)] := by
    rw [hb]
    exact b'.linearIndependent
  apply LinearIndependent.pair_iff.mp hli' a0 a1
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  rw [← h0]
  simp [sc, inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem thetaBas_of (hS : ThetaSpan σ J ψ v) : ThetaBas σ J ψ v := fun hstd hun => by
  obtain ⟨θ, h3, h4⟩ := theta_exists σ v hstd.1
  exact ⟨θ, hS hstd hun θ h4, theta_indep σ v hstd.1 θ h3, h3, h4⟩

theorem resAlg_of_span (hS : ThetaSpan σ J ψ v) (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_theta σ J ψ v (thetaBas_of σ J ψ v hS) hE

end PI.OmLocU.Red
