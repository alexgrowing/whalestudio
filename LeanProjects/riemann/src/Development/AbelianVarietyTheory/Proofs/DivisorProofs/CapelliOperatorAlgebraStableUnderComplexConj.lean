import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.ConjZalg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem map_qdet_semilinear {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →+* B) (σ : ℂ →+* ℂ)
    (hf : ∀ c, f (algebraMap ℂ A c) = algebraMap ℂ B (σ c)) (X : Fin a → Fin a → A) (u : ℂ) :
    f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) (σ u) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, Formalism.REAL.Tm, map_add, apply_ite f, map_zero, hf, map_sub, map_natCast]

def conjBy (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) : Module.End ℂ (Sm E a) →+* Module.End ℂ (Sm E a) where
  toFun z :=
    { toFun := fun φ => C.symm (z (C φ))
      map_add' := fun φ ψ => by simp
      map_smul' := fun c φ => by
        rw [LinearEquiv.map_smulₛₗ, LinearMap.map_smul, LinearEquiv.map_smulₛₗ]; simp }
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' z w := LinearMap.ext fun φ => by simp
  map_zero' := LinearMap.ext fun φ => by simp
  map_add' z w := LinearMap.ext fun φ => by simp

theorem conjBy_apply (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjBy C z φ = C.symm (z (C φ)) := rfl

theorem conjBy_algebraMap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (c : ℂ) :
    conjBy C (algebraMap ℂ (Module.End ℂ (Sm E a)) c) = algebraMap ℂ _ (starRingEnd ℂ c) :=
  LinearMap.ext fun φ => by
    rw [conjBy_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearEquiv.map_smulₛₗ]; simp

theorem C_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a)
    (φ : Sm E a) : C (Eop τ i j φ) = Eop (ComplexEmbedding.conjugate τ) i j (C φ) := by
  have hl : ∀ x φ, C (lieS E a i j x φ) = lieS E a i j x (C φ) := fun x φ => (hC (Op.lie _) φ).symm
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, map_smulₛₗ, map_sub, hl, atEmb_conj, map_one,
    Complex.conj_I, e, map_neg, LinearMap.neg_apply]
  have h2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by simp [map_div₀, map_ofNat]
  rw [h2]
  congr 1
  simp [sub_eq_add_neg, neg_smul, smul_neg]

theorem conjBy_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a) :
    conjBy C (Eop τ i j) = Eop (ComplexEmbedding.conjugate τ) i j :=
  LinearMap.ext fun φ => by
    apply C.injective
    have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [conjBy_apply, LinearEquiv.apply_symm_apply, C_Eop C hC, hcc]

theorem conjBy_cap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (u : ℂ) :
    conjBy C (cap τ u) = cap (ComplexEmbedding.conjugate τ) (starRingEnd ℂ u) := by
  rw [cap, map_qdet_semilinear (conjBy C) (starRingEnd ℂ) (conjBy_algebraMap C)]
  simp only [conjBy_Eop C hC, cap]
  congr 1
  simp [map_div₀, map_ofNat, map_sub, map_natCast]

theorem conjBy_mem_Zalg (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : conjBy C z ∈ Zalg E a := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | conjBy C z ∈ Zalg E a}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul] at *; exact Subalgebra.mul_mem _ hx hy
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at *; exact Subalgebra.add_mem _ hx hy
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, conjBy_algebraMap]; exact Subalgebra.algebraMap_mem _ _ }
  refine (Algebra.adjoin_le (S := S) ?_) hz
  rintro _ ⟨τ, u, rfl⟩
  change conjBy C (cap τ u) ∈ Zalg E a
  rw [conjBy_cap C hC]
  exact Algebra.subset_adjoin ⟨_, _, rfl⟩

theorem conj_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a),
    (∀ o φ, act o (C φ) = C (act o φ)) → ∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ) := by
  intro E _ _ _ a C hC z hz
  exact ⟨conjBy C z, conjBy_mem_Zalg C hC hz, fun φ => by rw [conjBy_apply, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.CuspRep.ConjZalg
