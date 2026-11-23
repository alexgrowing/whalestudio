import Mathlib

open Polynomial

noncomputable def UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField :
    Prop :=
    ∀ (A B : Type) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : CommRing B] [inst_3 : Algebra A B]
      [Module.Finite A B],
      ∃ (L : Type) (x : Field L) (x_1 : Algebra A L) (x_2 : Algebra (FractionRing A) L) (_ :
        IsScalarTower A (FractionRing A) L),
        FiniteDimensional (FractionRing A) L ∧
          Normal (FractionRing A) L ∧
            Finite (B →ₐ[A] ↥(integralClosure A L)) ∧
              ∀ (Ω : Type) [inst_5 : Field Ω] (φ : ↥(integralClosure A L) →+* Ω) (z : B →+* Ω),
                Function.Injective (⇑(φ.comp (Algebra.algebraMap A ↥(integralClosure A L))) : A → Ω) →
                  z.comp (Algebra.algebraMap A B) = φ.comp (Algebra.algebraMap A ↥(integralClosure A L)) →
                    ∃! σ : B →ₐ[A] ↥(integralClosure A L), φ.comp (↑σ : B →+* ↥(integralClosure A L)) = z

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (s : Finset B) :
    ∃ p : A[X], p.Monic ∧ ∀ b ∈ s, aeval b p = 0 := by
  have h : ∀ b : B, ∃ q : A[X], q.Monic ∧ aeval b q = 0 := fun b =>
    (Algebra.IsIntegral.isIntegral (R := A) b)
  choose q hq hq0 using h
  refine ⟨∏ b ∈ s, q b, monic_prod_of_monic _ _ fun b _ => hq b, fun b hb => ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero hb (hq0 b)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom {A B C : Type} [CommRing A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] (s : Finset B)
    (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) : Finite (B →ₐ[A] C) := by
  let f : (B →ₐ[A] C) → (s → p.rootSet C) := fun σ b =>
    ⟨σ b, by
      rw [hp.mem_rootSet, aeval_algHom_apply, h0 b b.2, map_zero]⟩
  refine Finite.of_injective f fun σ τ h => ?_
  apply AlgHom.toLinearMap_injective
  refine LinearMap.ext_on hs fun b hb => ?_
  exact congrArg Subtype.val (congrFun h ⟨b, hb⟩)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.factor {A B C Ω : Type} [CommRing A] [Nontrivial A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra.IsIntegral A C] [Field Ω]
    (s : Finset B) (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) (hsp : (p.map (algebraMap A C)).Splits)
    (φ : C →+* Ω) (z : B →+* Ω) (hinj : Function.Injective (φ.comp (algebraMap A C)))
    (hz : z.comp (algebraMap A B) = φ.comp (algebraMap A C)) :
    ∃! σ : B →ₐ[A] C, φ.comp (σ : B →+* C) = z := by
  have hφ : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hzA : ∀ a : A, z (algebraMap A B a) = φ (algebraMap A C a) := fun a =>
    DFunLike.congr_fun hz a
  have hgen : ∀ b ∈ s, z b ∈ φ.range := by
    intro b hb
    have h1 : eval (z b) ((p.map (algebraMap A C)).map φ) = 0 := by
      rw [Polynomial.map_map, ← hz, eval_map, ← hom_eval₂, ← aeval_def, h0 b hb, map_zero]
    rw [hsp.eq_prod_roots_of_monic (hp.map _), Polynomial.map_multiset_prod,
      eval_multiset_prod, Multiset.prod_eq_zero_iff] at h1
    simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply, Polynomial.map_sub,
      map_X, map_C, eval_sub, eval_X, eval_C] at h1
    obtain ⟨c, -, hc⟩ := h1
    exact ⟨c, (sub_eq_zero.1 hc).symm⟩
  have hall : ∀ b : B, z b ∈ φ.range := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hzA]
      exact mul_mem ⟨_, rfl⟩ hx
  choose g hg using hall
  let σ : B →ₐ[A] C :=
    { toFun := g
      map_one' := hφ (by rw [hg, map_one, map_one])
      map_mul' := fun x y => hφ (by rw [map_mul φ, hg, hg, hg, map_mul])
      map_zero' := hφ (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => hφ (by rw [map_add φ, hg, hg, hg, map_add])
      commutes' := fun a => hφ (by rw [hg, hzA]) }
  refine ⟨σ, RingHom.ext fun b => hg b, fun τ hτ => AlgHom.ext fun b => hφ ?_⟩
  exact (DFunLike.congr_fun hτ b).trans (hg b).symm

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure {A L : Type} [CommRing A] [Field L]
    [Algebra A L] (p : A[X]) (hp : p.Monic) (hsp : (p.map (algebraMap A L)).Splits) :
    (p.map (algebraMap A (integralClosure A L))).Splits := by
  have hm : (p.map (algebraMap A (integralClosure A L))).map
      (algebraMap (integralClosure A L) L) = p.map (algebraMap A L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  refine Splits.of_splits_map_of_injective (i := algebraMap (integralClosure A L) L)
    Subtype.val_injective (hm ▸ hsp) fun a ha => ?_
  rw [hm] at ha
  have h1 := isRoot_of_mem_roots ha
  rw [IsRoot.def, eval_map] at h1
  exact ⟨⟨a, p, hp, h1⟩, rfl⟩

theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of :
    UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField := by
  intro A B _ _ _ _ _
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  obtain ⟨p, hp, h0⟩ := UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic (A := A) s
  let q : (FractionRing A)[X] := p.map (algebraMap A (FractionRing A))
  let L : Type := q.SplittingField
  letI iK : Algebra (FractionRing A) L := inferInstance
  letI iA : Algebra A L :=
    ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI iT : @IsScalarTower A (FractionRing A) L Algebra.toSMul iK.toSMul iA.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hsp : (p.map (algebraMap A L)).Splits := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L, ← Polynomial.map_map]
    exact SplittingField.splits q
  refine ⟨L, inferInstance, iA, iK, iT, inferInstance, inferInstance,
    UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom s hs p hp h0, ?_⟩
  intro Ω _ φ z hinj hz
  exact UpperTheory.Reformulated.B.SplittingFieldConstruction.factor s hs p hp h0
    (UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure p hp hsp) φ z hinj hz
