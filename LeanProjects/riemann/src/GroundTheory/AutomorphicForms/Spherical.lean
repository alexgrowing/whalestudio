import Mathlib
import GroundTheory.AutomorphicForms.SphericalIntegral

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa Parabolic HeckeAlgebra HeckeAlgebraLevel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Characters

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem exists_ker_sphericalCharacter_eq (I : Ideal (SphericalHecke μ (F := F) (n := n)))
    [I.IsMaximal] : ∃ w : Fin n → ℂˣ,
      RingHom.ker (sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w)) = I := by
  haveI := isIntegral_satake (μ := μ) (F := F) (n := n)
  obtain ⟨w, hw⟩ := exists_ker_evalAt_comp_eq (satakeHom μ) satakeHom_injective I
  exact ⟨w, by rw [← evalAt_comp_satakeHom]; exact hw⟩

theorem exists_eq_sphericalCharacter (ω : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] ℂ) :
    ∃ χ : levi F n (id : Fin n → Fin n) →* ℂ, ∃ hχ : IsUnramified χ, ω = sphericalCharacter μ hχ := by
  have hsurj : Function.Surjective ω := fun c => ⟨algebraMap ℂ _ c, AlgHom.commutes ω c⟩
  haveI : (RingHom.ker ω).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨w, hw⟩ := exists_ker_sphericalCharacter_eq (μ := μ) (RingHom.ker ω)
  refine ⟨unramifiedChar w, isUnramified_unramifiedChar w, AlgHom.ext fun h => ?_⟩
  have hmem : h - algebraMap ℂ _ (ω h) ∈ RingHom.ker ω := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  rw [← hw, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hmem
  exact hmem.symm

end Characters

theorem exists_subquotient_principalSeries {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ (integralGL F n) ≠ ⊥) :
    ∃ χ : levi F n (id : Fin n → Fin n) →* ℂ, IsUnramified χ ∧
      ∃ W : Subrepresentation (principalSeries F n χ),
        ∃ f : Representation.IntertwiningMap W.toRepresentation ρ, Function.Surjective f := by
  borelize (GL (Fin n) F)
  let μ : Measure (GL (Fin n) F) := Measure.haar
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  let s₀ := LinearMap.toSpanSingleton (SphericalHecke μ (F := F) (n := n))
    (fixedVectors ρ (integralGL F n)) ⟨v₀, hv₀⟩
  let I : Ideal (SphericalHecke μ (F := F) (n := n)) := LinearMap.ker s₀
  have hsimple := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  have hsurj : Function.Surjective s₀ :=
    ((isSimpleModule_iff_toSpanSingleton_surjective).1 hsimple).2 _
      fun h => h0 (congrArg Subtype.val h)
  haveI hI : I.IsMaximal := by
    rw [Ideal.isMaximal_def]
    exact isSimpleModule_iff_isCoatom.1 (IsSimpleModule.congr (LinearMap.quotKerEquivOfSurjective _ hsurj))
  obtain ⟨w, hw⟩ := exists_ker_sphericalCharacter_eq (μ := μ) I
  set χ := unramifiedChar (F := F) w
  have hχ := isUnramified_unramifiedChar (F := F) w
  refine ⟨χ, hχ, ?_⟩
  set φ := sphericalVector hχ
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n)) (charRep χ)
  have hφK := sphericalVector_mem_fixedVectors hχ
  have hIv : ∀ h : SphericalHecke μ (F := F) (n := n), h ∈ I ↔
      heckeAct μ ρ (h : HeckeAlgebra μ) v₀ = 0 := by
    intro h
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Subtype.ext_iff]
    rfl
  have hIφ : ∀ h : SphericalHecke μ (F := F) (n := n), h ∈ I ↔
      heckeAct μ (principalSeries F n χ) (h : HeckeAlgebra μ) φ = 0 := by
    intro h
    rw [heckeAct_sphericalVector hχ, smul_eq_zero, ← hw, RingHom.mem_ker, sphericalCharacter_apply]
    simp [φ, sphericalVector_ne_zero hχ]
  obtain ⟨A⟩ := nonempty_equiv_quotRep hKc hKo I hρ hv₀ h0 hIv
  let Φ : HeckeAlgebra μ →ₗ[ℂ] principalSeriesSpace F n χ := orbitMap φ (hs φ)
  have hΦ : ∀ f, Φ f = heckeAct μ (principalSeries F n χ) f φ := fun _ => rfl
  have hint : ∀ g f, Φ (leftReg μ g f) = principalSeries F n χ g (Φ f) := fun g f =>
    (heckeAct_ltrans g f.mem (hs φ)).symm
  have key : ∀ f g, heckeAct μ (principalSeries F n χ) (idem μ hKc hKo)
      (principalSeries F n χ g (Φ f)) =
        heckeAct μ (principalSeries F n χ) (cornerₗ hKc hKo (leftReg μ g f) : HeckeAlgebra μ) φ := by
    intro f g
    rw [hΦ, heckeAct_ltrans g f.mem (hs φ)]
    change heckeAct μ _ (idem μ hKc hKo) (heckeAct μ _ (leftReg μ g f : HeckeAlgebra μ) φ) = _
    rw [← heckeAct_mul _ _ (hs φ)]
    exact (heckeAct_corner hKc hKo hφK _).symm
  have hker : LinearMap.ker Φ ≤ heckeKernel hKc hKo I := by
    intro f hf g
    rw [LinearMap.mem_ker] at hf
    rw [hIφ, ← key, hf, map_zero]
    exact heckeAct_zero_right (idem μ hKc hKo).mem
  let W : Subrepresentation (principalSeries F n χ) :=
    ⟨LinearMap.range Φ, by
      rintro g _ ⟨f, rfl⟩
      exact ⟨leftReg μ g f, hint g f⟩⟩
  let Ψ : HeckeAlgebra μ →ₗ[ℂ] V := A.toLinearMap ∘ₗ (heckeKernel hKc hKo I).mkQ
  have hΨ : LinearMap.ker Φ ≤ LinearMap.ker Ψ := fun f hf => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 (hker hf), map_zero]
  let T : LinearMap.range Φ →ₗ[ℂ] V :=
    (LinearMap.ker Φ).liftQ Ψ hΨ ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hT : ∀ f, T ⟨Φ f, LinearMap.mem_range_self Φ f⟩ = Ψ f := by
    intro f
    simp only [T, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hT' : ∀ (y : LinearMap.range Φ) (f) (_ : Φ f = y), T y = Ψ f := by
    rintro ⟨y, hy⟩ f rfl
    exact hT f
  refine ⟨W, ⟨T, fun g => LinearMap.ext fun y => ?_⟩, fun v => ?_⟩
  · obtain ⟨f, hf⟩ := y.2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    have hy : (W.toRepresentation g y : principalSeriesSpace F n χ) = Φ (leftReg μ g f) := by
      rw [hint, hf]
      rfl
    rw [hT' _ _ hy.symm, hT' y f hf]
    simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, Representation.Equiv.coe_toLinearMap]
    rw [← quotRep_mkQ]
    exact Representation.IntertwiningMap.isIntertwining _ _ A.toIntertwiningMap g _
  · obtain ⟨y, hy⟩ := A.toLinearEquiv.surjective v
    obtain ⟨f, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective y
    refine ⟨⟨Φ f, LinearMap.mem_range_self Φ f⟩, ?_⟩
    change T _ = v
    rw [hT]
    exact hy

end Spherical

end GroundTheory.Automorphic
