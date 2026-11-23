import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleSumPowMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharPStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.Descent

variable {R : Type} [CommRing R]

theorem descend {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D')
    (hψ : (ψ : D →+* D').FaithfullyFlat) (s : D')
    (hs : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α s = β s) :
    ∃ k, ψ k = s := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  refine (Algebra.IsEffective.of_faithfullyFlat D D' s).1 ?_
  have h := hs (D' ⊗[D] D') ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').restrictScalars R)
    ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').restrictScalars R) (by
      ext d
      exact ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').commutes d).symm)
  simpa [sub_eq_zero] using h

theorem exists_square {D D' D₂ : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D₂]
    [Algebra R D₂] (ψ : D →ₐ[R] D') (hψ : (ψ : D →+* D').FaithfullyFlat) (ψ₂ : D →ₐ[R] D₂) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra R E) (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
      α.comp ψ = β.comp ψ₂ ∧ Function.Injective β := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  letI : Algebra D D₂ := (ψ₂ : D →+* D₂).toAlgebra
  haveI : IsScalarTower R D D₂ := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ₂.commutes r).symm
  refine ⟨D₂ ⊗[D] D', inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').restrictScalars R,
    (Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').restrictScalars R, ?_, ?_⟩
  · ext d
    exact ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').commutes d).symm
  · exact FaithfulSMul.algebraMap_injective D₂ (D₂ ⊗[D] D')

variable {A : Over (Sp R)} [GrpObj A]

def sig (p : ℕ) (f : Fn1 A) (g : Fn2 A) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (x : Pt A D) (z : Pt A D') : D' :=
  chi p g D' z + f R D' (Algebra.ofId R D') 1 - f D D' ψ x

theorem sig_nat {p : ℕ} (hp : (p : R) = 0) {f : Fn1 A} {g : Fn2 A} (hf : IsCoc (whole A) f) (hfg : IsAdd f g)
    {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D''] [Algebra R D'']
    (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D') (hz : z ^ p = spOver ψ ≫ x) :
    θ (sig p f g ψ x z) = sig p f g (θ.comp ψ) x (spOver θ ≫ z) := by
  have h1 := GlobalTheory.T.sumTwoPointFunction_multiples_natural_charP p R hp A f g hfg D' D'' θ z
  have h2 := hf D D' D'' ψ θ x (sm_whole _)
  have h3 := hf R D' D'' (Algebra.ofId R D') θ 1 (sm_whole _)
  have e : θ.comp (Algebra.ofId R D') = Algebra.ofId R D'' := Subsingleton.elim _ _
  rw [e, MonObj.comp_one] at h3
  rw [hz] at h1
  simp only [sig, map_add, map_sub]
  linear_combination -h1 + h2 - h3

theorem chi_indep [IsCommMonObj A] {p : ℕ} (hp : (p : R) = 0) {g : Fn2 A} (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → chi p g D x = 0)
    {D : Type} [CommRing D] [Algebra R D] (z z' : Pt A D) (h : z ^ p = z' ^ p) : chi p g D z = chi p g D z' := by
  obtain ⟨t, rfl⟩ : ∃ t, z = z' * t := ⟨z'⁻¹ * z, by simp⟩
  have ht : t ^ p = 1 := by rwa [mul_pow, mul_eq_left] at h
  have h1 := GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul (Pt A D) D (g D) (hg D).1 (hg D).2 p z' t
  have h2 := (hg D).2 (z' ^ p) 1 1
  have h3 := h0 D t ht
  have h4 : (p : D) = 0 := by rw [← map_natCast (algebraMap R D), hp, map_zero]
  rw [ht, nsmul_eq_mul, h4] at h1
  simp only [_root_.mul_one] at h2
  simp only [chi] at h3 ⊢
  linear_combination h1 - h2 + h3

theorem pow_comp {p : ℕ} {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D'']
    [Algebra R D''] (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D') (hz : z ^ p = spOver ψ ≫ x) :
    (spOver θ ≫ z) ^ p = spOver (θ.comp ψ) ≫ x := by
  rw [← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]

theorem exists_isCob (p : ℕ) (R : Type) [CommRing R] (hp : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (f : Fn1 A) (g : Fn2 A) (hf : IsCoc (whole A) f) (hfg : IsAdd f g) (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → chi p g D x = 0)
    (hr : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
      (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ z ^ p = spOver ψ ≫ x) :
    ∃ k : Fn0 A, IsCob (whole A) f k := by
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ k : D,
      ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂), z₂ ^ p = spOver ψ₂ ≫ x →
        ψ₂ k = sig p f g ψ₂ x z₂ := by
    intro D _ _ x
    obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D x
    have cmp : ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂),
        z₂ ^ p = spOver ψ₂ ≫ x → ∀ (E : Type) [CommRing E] [Algebra R E] (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
        α.comp ψ = β.comp ψ₂ → α (sig p f g ψ x z) = β (sig p f g ψ₂ x z₂) := by
      intro D₂ _ _ ψ₂ z₂ hz₂ E _ _ α β e
      rw [sig_nat hp hf hfg ψ α x z hz, sig_nat hp hf hfg ψ₂ β x z₂ hz₂, sig, sig, e,
        chi_indep hp hg h0 (spOver α ≫ z) (spOver β ≫ z₂)
          (by rw [pow_comp ψ α x z hz, pow_comp ψ₂ β x z₂ hz₂, e])]
    obtain ⟨k, hk⟩ := descend ψ hψ (sig p f g ψ x z) (fun E _ _ α β e ↦ cmp D' ψ z hz E α β e)
    refine ⟨k, fun D₂ _ _ ψ₂ z₂ hz₂ ↦ ?_⟩
    obtain ⟨E, _, _, α, β, e, hβ⟩ := exists_square ψ hψ ψ₂
    apply hβ
    rw [← cmp D₂ ψ₂ z₂ hz₂ E α β e, ← hk]
    exact (DFunLike.congr_fun e k).symm
  choose k hk using key
  refine ⟨k, fun D _ _ D₁ _ _ φ x _ ↦ ?_⟩
  obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D₁ (spOver φ ≫ x)
  have hi : Function.Injective ψ := hψ.injective
  apply hi
  have h1 := hk D₁ (spOver φ ≫ x) D' ψ z hz
  have h2 := hk D x D' (ψ.comp φ) z (by rw [hz, ← Category.assoc, spOver_comp])
  have h3 := hf D D₁ D' φ ψ x (sm_whole _)
  simp only [sig, AlgHom.comp_apply] at h1 h2
  rw [map_sub]
  linear_combination h2 - h1 - h3

end GlobalTheory.PtExt.Descent
