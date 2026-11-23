import Mathlib
import GroundTheory.AutomorphicForms.SatakeTriangular
import GroundTheory.AutomorphicForms.Spherical
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideLast

noncomputable section

universe u

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa HeckeAlgebra HeckeAlgebraLevel AddMonoidAlgebra

namespace Spherical

variable {n : ℕ}

theorem evalAt_polyEmb (z : Fin n → ℂˣ) (Q : MvPolynomial (Fin n) ℂ) :
    evalAt z (polyEmb n Q) = MvPolynomial.aeval (fun i => (z i : ℂ)) Q := by
  have : (evalAt z).comp (polyEmb n) = MvPolynomial.aeval (fun i => (z i : ℂ)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, polyEmb_X, evalAt_single, MvPolynomial.aeval_X, one_mul,
      monomialChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_univ i) h)]
    simp
  exact AlgHom.congr_fun this Q

theorem polyEmb_esymm_mem (k : ℕ) :
    polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) ∈ symmetricLaurent n := fun σ => by
  rw [← polyEmb_rename, MvPolynomial.esymm_isSymmetric (Fin n) ℂ k σ]

theorem exists_perm_of_map_eq {z z' : Fin n → ℂˣ}
    (h : Multiset.map (fun i => (z i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => (z' i : ℂ)) Finset.univ.val) :
    ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ :=
  _root_.UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq h

theorem exists_perm_of_evalAt_eq {z z' : Fin n → ℂˣ}
    (h : ∀ p ∈ symmetricLaurent n, evalAt z p = evalAt z' p) :
    ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ := by
  apply exists_perm_of_map_eq
  have he : ∀ k, (Multiset.map (fun i => (z i : ℂ)) Finset.univ.val).esymm k =
      (Multiset.map (fun i => (z' i : ℂ)) Finset.univ.val).esymm k := fun k => by
    have := h _ (polyEmb_esymm_mem k)
    rwa [evalAt_polyEmb, evalAt_polyEmb, MvPolynomial.aeval_esymm_eq_multiset_esymm,
      MvPolynomial.aeval_esymm_eq_multiset_esymm] at this
  have hp : ((Multiset.map (fun i => (z i : ℂ)) Finset.univ.val).map
      fun t => Polynomial.X - Polynomial.C t).prod =
      ((Multiset.map (fun i => (z' i : ℂ)) Finset.univ.val).map
        fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, he]
  have := congrArg Polynomial.roots hp
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

theorem evalAt_comp_of_mem {p : LaurentRing n} (hp : p ∈ symmetricLaurent n) (z : Fin n → ℂˣ)
    (σ : Equiv.Perm (Fin n)) : evalAt (z ∘ σ) p = evalAt z p := by
  rw [← evalAt_permAct, hp σ]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section Measure

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem range_satakeTransform :
    (satakeTransform μ (F := F) (n := n)).range = symmetricLaurent n := by
  refine le_antisymm (fun p hp => ?_) symmetricLaurent_le_range
  obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).1 hp
  exact satakeTransform_mem_symmetric h

variable (μ) in

def satakeEquiv : SphericalHecke μ (F := F) (n := n) ≃ₐ[ℂ] symmetricLaurent n :=
  (AlgEquiv.ofInjective (satakeTransform μ) satakeTransform_injective).trans
    (Subalgebra.equivOfEq _ _ range_satakeTransform)

theorem coe_satakeEquiv (h : SphericalHecke μ (F := F) (n := n)) :
    (satakeEquiv μ h : LaurentRing n) = satakeTransform μ h :=
  rfl

theorem evalAt_comp_satakeTransform (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n))
    (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt (z ∘ σ) (satakeTransform μ h) = evalAt z (satakeTransform μ h) :=
  evalAt_comp_of_mem (satakeTransform_mem_symmetric h) z σ

theorem evalAt_comp_satakeTransform_eq_iff (z z' : Fin n → ℂˣ) :
    (evalAt z).comp (satakeTransform μ (F := F) (n := n)) = (evalAt z').comp (satakeTransform μ) ↔
      ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ := by
  constructor
  · intro hzz
    refine exists_perm_of_evalAt_eq fun p hp => ?_
    rw [← range_satakeTransform (μ := μ) (F := F)] at hp
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).1 hp
    exact AlgHom.congr_fun hzz h
  · rintro ⟨σ, rfl⟩
    exact AlgHom.ext fun h => (evalAt_comp_satakeTransform z σ h).symm

theorem sphericalCharacter_unramifiedChar_eq (w : Fin n → ℂˣ)
    (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) h =
      evalAt (w * (halfPoint F n)⁻¹) (satakeTransform μ h) := by
  rw [satakeTransform_apply, evalAt_normalize, inv_mul_cancel_right, evalAt_satake]

theorem exists_eq_evalAt_comp_satakeTransform
    (ω : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] ℂ) :
    ∃ z : Fin n → ℂˣ, ω = (evalAt z).comp (satakeTransform μ) := by
  have hsurj : Function.Surjective ω := fun c => ⟨algebraMap ℂ _ c, AlgHom.commutes ω c⟩
  have : (RingHom.ker ω).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨w, hw⟩ := exists_ker_sphericalCharacter_eq (μ := μ) (RingHom.ker ω)
  refine ⟨w * (halfPoint F n)⁻¹, AlgHom.ext fun h => ?_⟩
  rw [AlgHom.comp_apply, ← sphericalCharacter_unramifiedChar_eq]
  have hmem : h - algebraMap ℂ _ (ω h) ∈ RingHom.ker ω := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  rw [← hw, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hmem
  exact hmem.symm

theorem sphericalCharacter_paramChar_eq_iff (z z' : Fin n → ℂˣ) :
    sphericalCharacter μ (isUnramified_paramChar (F := F) z) =
        sphericalCharacter μ (isUnramified_paramChar (F := F) z') ↔
      ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ := by
  rw [← evalAt_comp_satakeTransform_eq_iff (μ := μ) (F := F)]
  constructor
  · intro hzz
    exact AlgHom.ext fun h => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, ← sphericalCharacter_paramChar,
        ← sphericalCharacter_paramChar, hzz]
  · intro hzz
    exact AlgHom.ext fun h => by
      rw [sphericalCharacter_paramChar, sphericalCharacter_paramChar]
      exact AlgHom.congr_fun hzz h

def IsSatakeParameter {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    (z : Fin n → ℂˣ) : Prop :=
  ∀ (h : SphericalHecke μ (F := F) (n := n)), ∀ v ∈ fixedVectors ρ (integralGL F n),
    heckeAct μ ρ (h : HeckeAlgebra μ) v = evalAt z (satakeTransform μ h) • v

theorem exists_satakeParameter {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ (integralGL F n) ≠ ⊥) :
    ∃ z : Fin n → ℂˣ, IsSatakeParameter ρ μ z := by
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
  have hI : I.IsMaximal := by
    rw [Ideal.isMaximal_def]
    exact isSimpleModule_iff_isCoatom.1
      (IsSimpleModule.congr (LinearMap.quotKerEquivOfSurjective _ hsurj))
  obtain ⟨w, hw⟩ := exists_ker_sphericalCharacter_eq (μ := μ) I
  refine ⟨w * (halfPoint F n)⁻¹, fun h v hv => ?_⟩
  rw [← sphericalCharacter_unramifiedChar_eq]
  set c := sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) h
  have hmem : h - algebraMap ℂ _ c ∈ I := by
    rw [← hw, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  obtain ⟨h', hh'⟩ := hsurj ⟨v, hv⟩
  have hkill : (h - algebraMap ℂ _ c) • (⟨v, hv⟩ : fixedVectors ρ (integralGL F n)) = 0 := by
    rw [← hh', LinearMap.toSpanSingleton_apply, smul_smul, mul_comm, ← smul_smul]
    have : (h - algebraMap ℂ _ c) • (⟨v₀, hv₀⟩ : fixedVectors ρ (integralGL F n)) = 0 := hmem
    rw [this, smul_zero]
  rw [sub_smul, sub_eq_zero] at hkill
  have hv' := congrArg Subtype.val hkill
  rw [coe_smul_fixedVectors, coe_smul_fixedVectors] at hv'
  rw [hv', Algebra.algebraMap_eq_smul_one, val_smul, val_one, HeckeAlgebra.coe_smul,
    heckeAct_smul_left _ (idem μ hKc hKo).mem (smooth_of_mem_fixedVectors hKo hv),
    heckeAct_idem_of_mem hKc hKo hv]

theorem algebraMap_smul_fixedVectors {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (c : ℂ) (v : fixedVectors ρ (integralGL F n)) :
    (algebraMap ℂ (SphericalHecke μ (F := F) (n := n)) c) • v = c • v := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  refine Subtype.ext ?_
  rw [coe_smul_fixedVectors, Algebra.algebraMap_eq_smul_one, val_smul, val_one,
    HeckeAlgebra.coe_smul, heckeAct_smul_left _ (idem μ hKc hKo).mem
      (smooth_of_mem_fixedVectors hKo v.2), heckeAct_idem_of_mem hKc hKo v.2]
  rfl

theorem smul_fixedVectors_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {z : Fin n → ℂˣ} (hz : IsSatakeParameter ρ μ z)
    (h : SphericalHecke μ (F := F) (n := n)) (v : fixedVectors ρ (integralGL F n)) :
    h • v = evalAt z (satakeTransform μ h) • v :=
  Subtype.ext (by rw [coe_smul_fixedVectors, Submodule.coe_smul]; exact hz h v v.2)

theorem satakeParameter_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hK : fixedVectors ρ (integralGL F n) ≠ ⊥)
    {z z' : Fin n → ℂˣ} (hz : IsSatakeParameter ρ μ z) (hz' : IsSatakeParameter ρ μ z') :
    ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ := by
  obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  refine (evalAt_comp_satakeTransform_eq_iff (μ := μ) z z').1 (AlgHom.ext fun h => ?_)
  have := (hz h v hv).symm.trans (hz' h v hv)
  exact smul_left_injective ℂ h0 this

theorem isSatakeParameter_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {z : Fin n → ℂˣ} (hz : IsSatakeParameter ρ μ z)
    (σ : Equiv.Perm (Fin n)) : IsSatakeParameter ρ μ (z ∘ σ) := fun h v hv => by
  rw [evalAt_comp_satakeTransform]
  exact hz h v hv

theorem isSatakeParameter_principalSeries (z : Fin n → ℂˣ) :
    IsSatakeParameter (principalSeries F n (paramChar F z)) μ z := by
  intro h v hv
  have hχ := isUnramified_paramChar (F := F) z
  rw [fixedVectors_eq_span hχ, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  have hs := Parabolic.isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n))
    (charRep (paramChar F z))
  rw [heckeAct_smul_right (h : HeckeAlgebra μ).mem c (hs _), heckeAct_sphericalVector hχ,
    ← sphericalCharacter_apply hχ, sphericalCharacter_paramChar, smul_comm]

theorem evalAt_inv_halfPoint_satakeTransform (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt (halfPoint F n)⁻¹ (satakeTransform μ h) = ∫ g, (h : HeckeAlgebra μ) g ∂μ := by
  rw [satakeTransform_apply, evalAt_normalize, inv_mul_cancel, evalAt_satake,
    sphericalCharacter_apply, sphericalEigen]
  congr 1
  funext g
  rw [sphericalFun_unramifiedChar, map_one, mul_one]

end Measure

theorem finrank_fixedVectors_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ (integralGL F n) ≠ ⊥) :
    Module.finrank ℂ (fixedVectors ρ (integralGL F n)) = 1 := by
  borelize (GL (Fin n) F)
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨z, hz⟩ := exists_satakeParameter (μ := (Measure.haar : Measure (GL (Fin n) F))) hρ hK
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have hv₀' : (⟨v₀, hv₀⟩ : fixedVectors ρ (integralGL F n)) ≠ 0 :=
    fun h => h0 (congrArg Subtype.val h)
  have hsimple := isSimpleModule_fixedVectors (μ := (Measure.haar : Measure (GL (Fin n) F)))
    hKc hKo hρ hK
  have hsurj := ((isSimpleModule_iff_toSpanSingleton_surjective).1 hsimple).2 _ hv₀'
  have htop : (ℂ ∙ (⟨v₀, hv₀⟩ : fixedVectors ρ (integralGL F n))) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun v => ?_
    obtain ⟨h, rfl⟩ := hsurj v
    rw [LinearMap.toSpanSingleton_apply, smul_fixedVectors_eq hz]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rw [← finrank_top, ← htop, finrank_span_singleton hv₀']

section Classification

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem nonempty_equiv_of_isSatakeParameter {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin n) F) V}
    {σ : Representation ℂ (GL (Fin n) F) W} (hρ : IsSmooth ρ) (hσ : IsSmooth σ) [ρ.IsIrreducible]
    [σ.IsIrreducible] (hKρ : fixedVectors ρ (integralGL F n) ≠ ⊥)
    (hKσ : fixedVectors σ (integralGL F n) ≠ ⊥) {z : Fin n → ℂˣ} (hzρ : IsSatakeParameter ρ μ z)
    (hzσ : IsSatakeParameter σ μ z) : Nonempty (ρ.Equiv σ) := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  have h1 := finrank_fixedVectors_eq_one hρ hKρ
  have h2 := finrank_fixedVectors_eq_one hσ hKσ
  have : FiniteDimensional ℂ (fixedVectors ρ (integralGL F n)) :=
    Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  have : FiniteDimensional ℂ (fixedVectors σ (integralGL F n)) :=
    Module.finite_of_finrank_pos (by rw [h2]; exact one_pos)
  let f : fixedVectors ρ (integralGL F n) ≃ₗ[ℂ] fixedVectors σ (integralGL F n) :=
    LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  let e : fixedVectors ρ (integralGL F n) ≃ₗ[SphericalHecke μ (F := F) (n := n)]
      fixedVectors σ (integralGL F n) :=
    { toFun := f
      invFun := f.symm
      map_add' := f.map_add
      map_smul' := fun h v => by
        rw [RingHom.id_apply, smul_fixedVectors_eq hzρ, smul_fixedVectors_eq hzσ, f.map_smul]
      left_inv := f.left_inv
      right_inv := f.right_inv }
  exact nonempty_equiv_of_fixedVectors_equiv hKc hKo hρ hσ hKρ e

theorem exists_irreducible_isSatakeParameter (z : Fin n → ℂˣ) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (GL (Fin n) F) V),
      IsSmooth ρ ∧ ρ.IsIrreducible ∧ fixedVectors ρ (integralGL F n) ≠ ⊥ ∧
        IsSatakeParameter ρ μ z := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  set ω := (evalAt z).comp (satakeTransform μ (F := F) (n := n))
  have hsurj : Function.Surjective ω := fun c => ⟨algebraMap ℂ _ c, AlgHom.commutes ω c⟩
  set I := RingHom.ker ω
  have hI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have : IsSimpleModule (SphericalHecke μ (F := F) (n := n)) (SphericalHecke μ (F := F) (n := n) ⧸ I) :=
    isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 hI)
  have : Nontrivial (SphericalHecke μ (F := F) (n := n) ⧸ I) :=
    IsSimpleModule.nontrivial (SphericalHecke μ (F := F) (n := n)) _
  obtain ⟨V, _, _, ρ, hρ, hirr, ⟨e⟩⟩ :=
    exists_irreducible_fixedVectors_equiv (μ := μ) hKc hKo (SphericalHecke μ (F := F) (n := n) ⧸ I)
  refine ⟨V, _, _, ρ, hρ, hirr, Submodule.nontrivial_iff_ne_bot.1 e.toEquiv.nontrivial,
    fun h v hv => ?_⟩
  have hq : ∀ m : SphericalHecke μ (F := F) (n := n) ⧸ I, h • m = ω h • m := by
    intro m
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I m
    have hmem : h - algebraMap ℂ _ (ω h) ∈ I := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self]
    rw [← sub_eq_zero, ← algebraMap_smul (SphericalHecke μ (F := F) (n := n)) (ω h), ← sub_smul,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact I.mul_mem_right a hmem
  have hv' : h • (⟨v, hv⟩ : fixedVectors ρ (integralGL F n)) = ω h • ⟨v, hv⟩ := by
    apply e.injective
    rw [e.map_smul, hq, ← algebraMap_smul (SphericalHecke μ (F := F) (n := n)) (ω h),
      ← e.map_smul, algebraMap_smul_fixedVectors]
  have := congrArg Subtype.val hv'
  rw [coe_smul_fixedVectors] at this
  exact this

end Classification

end Spherical

end GroundTheory.Automorphic
