import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacDual

theorem exists_extension {O E V : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (Λ : Submodule O V) (hspan : Submodule.span E (Λ : Set V) = ⊤) (φ : Λ →ₗ[O] O) :
    ∃ ψ : V →ₗ[E] E, ∀ x : Λ, ψ x = algebraMap O E (φ x) := by
  haveI : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun x => by
        rw [Module.End.isUnit_iff]
        have hx : algebraMap O E x ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
        refine ⟨fun a b h => ?_, fun b => ⟨(algebraMap O E x)⁻¹ • b, ?_⟩⟩
        · have h' : algebraMap O E x • a = algebraMap O E x • b := by
            simpa [Module.algebraMap_end_apply] using h
          exact smul_right_injective V hx h'
        · rw [Module.algebraMap_end_apply, ← algebraMap_smul E, smul_smul, mul_inv_cancel₀ hx, one_smul]
      surj := fun y => by
        have hy : y ∈ Submodule.span E (Λ : Set V) := hspan ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
      exists_of_eq := fun {a b} h => ⟨1, by rw [Λ.injective_subtype h]⟩ }
  let g : V →ₗ[O] E := IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
    ((Algebra.linearMap O E).comp φ) (IsLocalizedModule.map_units (Algebra.linearMap O E))
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype ((Algebra.linearMap O E).comp φ)
    (IsLocalizedModule.map_units (Algebra.linearMap O E)) x

theorem exists_dual_family {E : Type} [Field E] [NumberField E] [StarRing E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (hG : ∀ i j, star (G i j) = G j i) (hdet : IsUnit G.det)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hsd : ∀ y : Fin r → E, (∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j) → y ∈ Λ) :
    ∃ (n : ℕ) (s s' : Fin n → Fin r → E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧
      ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * G k j = if a = j then 1 else 0 := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose ψ hψ using fun i : Fin n => exists_extension Λ hspan ((LinearMap.proj i).comp σ)
  let c : Fin n → Fin r → E := fun i j => ψ i (Pi.single j 1)
  have hc : ∀ i x, ψ i x = ∑ j, x j * c i j := by
    intro i x
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp [c, map_sum]
  let s' : Fin n → Fin r → E := fun i => star (c i ᵥ* G⁻¹)
  have hs' : ∀ i j, ∑ k, star (s' i k) * G k j = c i j := by
    intro i j
    have : (c i ᵥ* G⁻¹) ᵥ* G = c i := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    rw [← congrFun this j]
    simp [s', Matrix.vecMul, dotProduct]
  let s : Fin n → Fin r → E := fun i => f (Pi.single i 1)
  refine ⟨n, s, s', fun i => ⟨(f (Pi.single i 1)).2, hsd _ fun x hx => ?_⟩, fun a j => ?_⟩
  · have h1 : ∑ a, ∑ b, star (x a) * G a b * s' i b = star (ψ i x) := by
      rw [hc, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hs', star_mul', star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', star_star, hG]; ring
    have h2 := hψ i ⟨x, hx⟩
    rw [h1]
    refine ⟨⟨star (ψ i x), ?_⟩, rfl⟩
    have h3 : IsIntegral ℤ (ψ i x) := by
      rw [show ψ i x = _ from h2]
      exact RingOfIntegers.isIntegral_coe _
    exact h3.map (starRingEnd E).toIntAlgHom
  · have key : (∑ i, (ψ i).smulRight (s i) : (Fin r → E) →ₗ[E] (Fin r → E)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun x hx => ?_
      have h1 : f (σ ⟨x, hx⟩) = ⟨x, hx⟩ := LinearMap.congr_fun hσ ⟨x, hx⟩
      rw [pi_eq_sum_univ' (σ ⟨x, hx⟩), map_sum] at h1
      have h2 := congrArg Λ.subtype h1
      rw [map_sum] at h2
      rw [LinearMap.sum_apply, LinearMap.id_apply]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
      rw [LinearMap.smulRight_apply, show ψ i x = _ from hψ i ⟨x, hx⟩, algebraMap_smul, map_smul, map_smul]
      rfl
    have h := congrFun (LinearMap.congr_fun key (Pi.single j 1)) a
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.id_apply, Pi.single_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs', mul_comm]

theorem dualFamily : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), IsSelfDualC S Λ → ∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0 := by
  intro D S Λ h
  exact exists_dual_family S.gram (gram_star S) (gram_det_isUnit S) Λ h.1.fg h.1.span_eq_top
    fun y hy => (h.2 y).2 hy

end GlobalTheory.LatVacDual
