import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LiftGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.UnivOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PtClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PtTorus

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem prod_part {O U H : Type} [CommRing O] [CommRing U] [Algebra O U] [Group H] (W : WPres O (ℤ × ℤ) U)
    (r : H →* UpperTheory.V.GradeZeroInterpolatingElement.M4 U) (h : ∀ g a b, r g a b ∈ W.part (wt a b)) (L : List (H × Fin 4 × Fin 4)) :
    (L.map fun a => r a.1 a.2.1 a.2.2).prod ∈ W.part (L.map fun a => wt a.2.1 a.2.2).sum := by
  induction L with
  | nil => exact (SetLike.GradedOne.one_mem : (1 : U) ∈ W.part 0)
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact SetLike.GradedMul.mul_mem (h _ _ _) ih

private theorem fin_adjoin {O U R H : Type} [CommRing O] [IsNoetherianRing O] [CommRing U] [Algebra O U] [CommRing R]
    [Algebra O R] [Group H] (W : WPres O (ℤ × ℤ) U) (r : H →* UpperTheory.V.GradeZeroInterpolatingElement.M4 U) (h : ∀ g a b, r g a b ∈ W.part (wt a b))
    (f : U →ₐ[O] R) (r' : H →* UpperTheory.V.GradeZeroInterpolatingElement.M4 R) (hr : ∀ g a b, r' g a b = f (r g a b)) [Module.Finite O (W.gr 0)] :
    Module.Finite O (Algebra.adjoin O (mono r' 0)) := by
  let φ : W.gr 0 →ₗ[O] R := f.toLinearMap ∘ₗ W.A.val.toLinearMap ∘ₗ (W.gr 0).subtype
  have key : ∀ x ∈ Algebra.adjoin O (mono r' 0), ∃ y ∈ W.part 0, f y = x := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨L, hL, rfl⟩ := hx
      refine ⟨_, hL ▸ prod_part W r h L, ?_⟩
      rw [map_list_prod, List.map_map]
      simp only [hr]
      rfl
    | algebraMap a =>
      refine ⟨algebraMap O U a, ?_, f.commutes a⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : U) ∈ W.part 0)
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, add_mem ha hb, map_add f a b⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      refine ⟨a * b, ?_, map_mul f a b⟩
      have := (SetLike.GradedMul.mul_mem ha hb : a * b ∈ W.part (0 + 0))
      rwa [add_zero] at this
  have hm : ∀ x : Algebra.adjoin O (mono r' 0), (Algebra.adjoin O (mono r' 0)).val.toLinearMap x ∈ LinearMap.range φ :=
    fun x => by
      obtain ⟨y, hy, e⟩ := key x.1 x.2
      exact ⟨⟨⟨y, W.part_le_A hy⟩, hy⟩, e⟩
  refine Module.Finite.of_injective (LinearMap.codRestrict _ _ hm) fun x y e => ?_
  have e' := congrArg Subtype.val e
  exact Subtype.ext e'

theorem UpperTheory.V.Ws.Po.univGr :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ¬ D.Fin0 →
      ∃ (U : Type) (_ : CommRing U) (_ : Algebra c.O U) (_ : IsCO c.O U) (ρ : Lift c.O D.rbar U) (W : WPres c.O (ℤ × ℤ) U),
        D.IsPt ρ ∧ (∀ s, W.z s ∈ maximalIdeal U) ∧
        (∀ i, ∃ g a b, W.z i = ρ.hom g a b - algebraMap c.O U (D.r0 g a b) ∧ W.wt i = wt a b) ∧ ¬ Module.Finite c.O (W.gr 0) := by
  intro hP Ω _ _ _ l _ c D hD hF
  have hex : ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R), D.IsPt ρ := by
    by_contra hn
    exact hF fun R _ _ _ ρ h => (hn ⟨R, inferInstance, inferInstance, inferInstance, ρ, h⟩).elim
  obtain ⟨U, _, _, _, ρ, hrep⟩ := univOf hP D hD (fun _ _ _ _ ρ => D.IsPt ρ) (ptClosed hP D hD)
    (fun _ _ _ _ _ h => h.unr) hex
  have hgen : ρ.Generates := fun R' _ _ _ f f' h =>
    ((hrep R').2 (ρ.map f') ((hrep R').1 f')).unique h rfl
  have hst : ρ.TStable w4 := tstable hrep fun R' _ _ _ r r' s h1 h2 h3 h4 => ptTorus D hD R' r r' s h1 h2 h3 h4
  obtain ⟨W, hW, hz⟩ := lift_grading c.O (ℤ × ℤ) (G ℚ Ω) (Fin 4) D.rbar w4 U ρ (fun g a b => D.r0 g a b)
    (fun _ _ _ => rfl) (fun g a b h => Matrix.diagonal_apply_ne _ fun e => h (congrArg w4 e)) hgen hst
  have hid : ρ.map (AlgHom.id c.O U) = ρ := by
    ext g a b
    rfl
  refine ⟨U, inferInstance, inferInstance, inferInstance, ρ, W, hid ▸ (hrep U).1 (AlgHom.id c.O U), fun s => ?_, hz,
    fun hfin => hF fun R _ _ _ r hr => ?_⟩
  · obtain ⟨g, a, b, e, -⟩ := hz s
    rw [e, ← res_eq_zero_iff c.O, map_sub, ρ.red, AlgHom.commutes, sub_eq_zero]
    rfl
  · obtain ⟨f, hf, -⟩ := (hrep R).2 r hr
    exact fin_adjoin W ρ.hom hW f r.hom fun g a b => by rw [← hf]; rfl
