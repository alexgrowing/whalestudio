import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich
import GroundTheory.AutomorphicForms.GL2.GJStandardLDual
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.HeckeAlgebra

namespace UpperTheory.V.Z.Inf.LocalUnramifiedTorus

section Alg

variable {F : Type} [Field F] {n : ℕ}

private theorem anti_symm :
    (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id = (1 : Matrix (Fin n) (Fin n) F).submatrix id Fin.rev := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.one_apply, Fin.rev_eq_iff]

private theorem anti_mul (A : Matrix (Fin n) (Fin n) F) :
    (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id * A = A.submatrix Fin.rev id := by
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) F) A Fin.rev (Equiv.refl (Fin n)) id
  simpa using this

private theorem mul_anti (A : Matrix (Fin n) (Fin n) F) :
    A * (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id = A.submatrix id Fin.rev := by
  rw [anti_symm]
  have := Matrix.submatrix_mul_equiv A (1 : Matrix (Fin n) (Fin n) F) id (Equiv.refl (Fin n)) Fin.rev
  simpa using this

private theorem anti_sq :
    (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id * (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id = 1 := by
  rw [anti_mul]
  ext i j
  simp [Matrix.one_apply]

variable (F n) in

private def wl : GL (Fin n) F :=
  ⟨(1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id, (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id, anti_sq, anti_sq⟩

private theorem wl_conj (g : GL (Fin n) F) (i j : Fin n) :
    ((wl F n * g * (wl F n)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (g : Matrix (Fin n) (Fin n) F) i.rev j.rev := by
  have : ((wl F n * g * (wl F n)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id * (g : Matrix (Fin n) (Fin n) F) *
        (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id := rfl
  rw [this, anti_mul, mul_anti]
  rfl

variable [ValuativeRel F]

private theorem wl_mem : wl F n ∈ integralGL F n := by
  have h : ∀ i j, ((1 : Matrix (Fin n) (Fin n) F).submatrix Fin.rev id) i j ∈ (ValuativeRel.valuation F).integer := by
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [mem_integralGL_iff]
  exact ⟨h, h⟩

private theorem conj_unip {u : GL (Fin n) F} (hu : u ∈ unipotent F n) :
    wl F n * transposeInv F n u * (wl F n)⁻¹ ∈ unipotent F n := by
  have hi := (unipotent F n).inv_mem hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [wl_conj, coe_transposeInv, Matrix.transpose_apply]
    exact hi.1 (Fin.rev_lt_rev.2 hij)
  · change ((wl F n * transposeInv F n u * (wl F n)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1
    rw [wl_conj, coe_transposeInv, Matrix.transpose_apply]
    exact hi.2 _

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem conj_torus (l : Fin n → ℤ) :
    wl F n * transposeInv F n (torusPow F n l) * (wl F n)⁻¹ = torusPow F n fun i => -l i.rev := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [wl_conj, coe_transposeInv, Matrix.transpose_apply, torusPow, ← map_inv, coe_diagGL, coe_torusPow]
  by_cases h : i = j
  · subst h
    simp [Units.val_zpow_eq_zpow_val]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm)]

private theorem exponent_conj (g : GL (Fin n) F) :
    iwasawaExponent F n (wl F n * transposeInv F n g) = fun i => -iwasawaExponent F n g i.rev := by
  obtain ⟨u, hu, k, hk, hg⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  set l := iwasawaExponent F n g
  have : wl F n * transposeInv F n g = (wl F n * transposeInv F n u * (wl F n)⁻¹) *
      (torusPow F n fun i => -l i.rev) * (wl F n * transposeInv F n k) := by
    rw [← conj_torus, hg, map_mul, map_mul]
    group
  rw [this]
  exact iwasawaExponent_eq F n (conj_unip hu) ((integralGL F n).mul_mem wl_mem (transposeInv_mem_integralGL hk))

private theorem halfPoint_rev (i : Fin n) : halfPoint F n i.rev = (halfPoint F n i)⁻¹ := by
  refine Units.ext ?_
  rw [Units.val_inv_eq_inv_val, halfPoint, halfPoint, Units.val_mk0, Units.val_mk0, halfModulus_eq, halfModulus_eq,
    rhoPair_single, rhoPair_single, ← zpow_neg, Fin.val_rev]
  congr 1
  have := i.is_lt
  omega

private theorem monomial_conj (l : Fin n → ℤ) (z : Fin n → ℂˣ) :
    monomialChar (fun i => -l i.rev) (((z⁻¹) ∘ (Fin.revPerm : Equiv.Perm (Fin n))) * halfPoint F n) =
      monomialChar l (z * halfPoint F n) := by
  rw [monomialChar_apply, monomialChar_apply]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  congr 1
  simp only [Pi.mul_apply, Function.comp_apply, Pi.inv_apply, Fin.revPerm_apply, halfPoint_rev]
  rw [← inv_zpow', mul_inv, inv_inv]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

private theorem evalAt_eq_integral (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt z (satakeTransform μ h) =
      ∫ g, (h : HeckeAlgebra μ) g * monomialChar (iwasawaExponent F n g) (z * halfPoint F n) ∂μ := by
  rw [satakeTransform_apply, evalAt_normalize, evalAt_satake, sphericalCharacter_apply, sphericalEigen]
  simp only [sphericalFun_unramifiedChar]

private def flip (h : SphericalHecke μ (F := F) (n := n)) : SphericalHecke μ (F := F) (n := n) :=
  HeckeAlgebraLevel.mk _ _ (HeckeAlgebra.mk μ (fun g => (h : HeckeAlgebra μ) (transposeInv F n g))
    ⟨(h : HeckeAlgebra μ).mem.1.comp_continuous continuous_transposeInv,
      (h : HeckeAlgebra μ).mem.2.comp_homeomorph (transposeInvHomeomorph (F := F) (n := n))⟩)
    (fun k hk x => by
      have := HeckeAlgebraLevel.val_mem _ _ h _ (transposeInv_mem_integralGL hk) (transposeInv F n x)
      change (h : HeckeAlgebra μ) (transposeInv F n (k * x)) = (h : HeckeAlgebra μ) (transposeInv F n x) ∧
        (h : HeckeAlgebra μ) (transposeInv F n (x * k)) = (h : HeckeAlgebra μ) (transposeInv F n x)
      rw [map_mul (transposeInv F n), map_mul (transposeInv F n)]
      exact this)

private theorem flip_apply (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (flip h : HeckeAlgebra μ) g = (h : HeckeAlgebra μ) (transposeInv F n g) := rfl

private theorem evalAt_flip (z : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt z (satakeTransform μ (flip h)) = evalAt z⁻¹ (satakeTransform μ h) := by
  rw [← evalAt_comp_satakeTransform z⁻¹ Fin.revPerm h, evalAt_eq_integral, evalAt_eq_integral]
  set φ : GL (Fin n) F → ℂ := fun g => (h : HeckeAlgebra μ) g *
    monomialChar (iwasawaExponent F n g) (((z⁻¹) ∘ (Fin.revPerm : Equiv.Perm (Fin n))) * halfPoint F n) with hφ
  rw [← integral_mul_left_eq_self φ (wl F n), ← integral_comp_transposeInv μ fun g => φ (wl F n * g)]
  congr 1
  funext g
  simp only [hφ]
  rw [exponent_conj, monomial_conj, flip_apply, (HeckeAlgebraLevel.val_mem _ _ h _ wl_mem _).1]

private theorem exists_pair {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
    (hπ : IsAdmissible π) (hK : fixedVectors π (integralGL F n) ≠ ⊥) :
    ∃ v₀ ∈ fixedVectors π (integralGL F n), ∃ ℓ₀ ∈ fixedVectors (Representation.dual π) (integralGL F n),
      ℓ₀ v₀ = 1 := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have hne : (⟨v₀, hv₀⟩ : fixedVectors π (integralGL F n)) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hne
  refine ⟨v₀, hv₀, f ∘ₗ fixedProj π hπ.1 hKc hKo, mem_fixedVectors_dual.2 fun k hk x => ?_, ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, fixedProj_apply_act hπ.1 hKc hKo hk]
  · have : fixedProj π hπ.1 hKc hKo v₀ = ⟨v₀, hv₀⟩ := Subtype.ext (fixedProj_apply_of_mem hπ.1 hKc hKo hv₀)
    simp only [LinearMap.coe_comp, Function.comp_apply, this, hf]

private theorem lfun_contra [NeZero n] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} [π.IsIrreducible] (hπ : IsAdmissible π)
    (hK : fixedVectors π (integralGL F n) ≠ ⊥) {z : Fin n → ℂˣ} (hz : IsSatakeParameter π μ z) (t : ℂ) :
    LFunction (contragredient π) t = ∏ i, (1 - (z i : ℂ)⁻¹ * qs F t)⁻¹ := by
  obtain ⟨v₀, hv₀, ℓ₀, hℓK, hℓ⟩ := exists_pair hπ hK
  obtain ⟨z', hz', hL⟩ := exists_satakeParameter_contragredient π hπ μ hℓK hℓ
  have hsm : ℓ₀ ∈ smoothVectors (Representation.dual π) :=
    mem_smoothVectors_of_mem_fixedVectors (isOpen_integralGL F n) hℓK
  have hfix : (⟨ℓ₀, hsm⟩ : smoothVectors (Representation.dual π)) ∈
      fixedVectors (contragredient π) (integralGL F n) :=
    mem_fixedVectors_contragredient.2 (mem_fixedVectors_dual.1 hℓK)
  have hbi : ∀ k ∈ integralGL F n, ∀ x, Parabolic.matrixCoeff π v₀ ℓ₀ (k * x) = Parabolic.matrixCoeff π v₀ ℓ₀ x ∧
      Parabolic.matrixCoeff π v₀ ℓ₀ (x * k) = Parabolic.matrixCoeff π v₀ ℓ₀ x := by
    intro k hk x
    constructor
    · change ℓ₀ (π (k * x) v₀) = ℓ₀ (π x v₀)
      rw [map_mul, Module.End.mul_apply, mem_fixedVectors_dual.1 hℓK k hk]
    · change ℓ₀ (π (x * k) v₀) = ℓ₀ (π x v₀)
      rw [map_mul, Module.End.mul_apply, hv₀ k hk]
  have key : (evalAt z⁻¹).comp (satakeTransform μ (F := F) (n := n)) = (evalAt z').comp (satakeTransform μ) := by
    refine AlgHom.ext fun h => ?_
    have h1 := integral_mul_matrixCoeff_of_isSatakeParameter hz' hfix (evalSmooth π v₀) h
    have h2 := integral_mul_matrixCoeff_of_isSatakeParameter hz hv₀ ℓ₀ (flip h)
    have hev : evalSmooth π v₀ ⟨ℓ₀, hsm⟩ = 1 := hℓ
    rw [hev, mul_one] at h1
    rw [hℓ, mul_one, evalAt_flip] at h2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, ← h1, ← h2, ← integral_comp_transposeInv μ
      fun g => (h : HeckeAlgebra μ) g * Parabolic.matrixCoeff (contragredient π) ⟨ℓ₀, hsm⟩ (evalSmooth π v₀) g]
    congr 1
    funext g
    rw [flip_apply, ← matrixCoeff_inv_eq_contragredient, apply_inv_transposeInv hbi]
  obtain ⟨σ, rfl⟩ := (evalAt_comp_satakeTransform_eq_iff _ _).1 key
  rw [hL]
  refine Fintype.prod_equiv σ _ _ fun i => ?_
  simp only [Function.comp_apply, Pi.inv_apply, Units.val_inv_eq_inv_val]

end Alg

end UpperTheory.V.Z.Inf.LocalUnramifiedTorus

theorem UpperTheory.V.Z.Inf.locUnr :
    UpperTheory.V.Z.Inf.LocUnr := by
  intro K _ _ n hn v V _ _ π hirr hadm hK z hz t
  haveI : NeZero n := ⟨by omega⟩
  have hq : qs (v.adicCompletion K) t = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-t) := by
    rw [qs, GroundTheory.Global.residueCard_adicCompletion]
  rw [← hq]
  exact ⟨LFunction_eq_prod_of_isSatakeParameter hadm hK _ hz t, LocalUnramifiedTorus.lfun_contra hadm hK hz t⟩
