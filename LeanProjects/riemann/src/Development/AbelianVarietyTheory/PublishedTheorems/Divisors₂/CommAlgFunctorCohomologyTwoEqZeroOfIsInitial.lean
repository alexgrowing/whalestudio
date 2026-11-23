import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDeRham.Test

theorem commAlgFunctorCohomologyTwo_eq_zero_of_isInitial {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {T₀ : C} (h : Limits.IsInitial T₀) (c : CatCoh.H2 F) : c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩
  funext T T' T'' φ ψ
  have := z.2 (h.to T) φ ψ
  rw [h.to_comp φ] at this
  rw [d1_apply]
  linear_combination this

variable (R : Type) [CommRing R]

theorem deRham_h2_base_eq_zero {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s] (c : SecondDeRham s) : c = 0 := by
  have hx : inv s ≫ s = spMap (algebraMap R R) := by
    rw [IsIso.inv_hom_id]; exact (Cris.spMap_id R).symm
  refine commAlgFunctorCohomologyTwo_eq_zero_of_isInitial _ (T₀ := Thick.triv R (inv s) hx)
    (Limits.IsInitial.ofUniqueHom (fun T ↦ Thick.trivHom (Algebra.ofId R T.B) ?_) fun T m ↦ ?_) c
  · rw [IsIso.comp_inv_eq]; exact T.w.symm
  · exact Thick.hom_ext fun b ↦ (m.φ.commutes b).trans ((Algebra.ofId R T.B).commutes b).symm

theorem unit_hyp : IsAbelianScheme (𝟙_ (Over (Sp R))) ∧
    SmoothOfRelativeDimension 0 (𝟙_ (Over (Sp R))).hom :=
  ⟨(ReciprocityTheory.ChartRestriction.G.Out.Inh.zeroPolAV (Sp R)).isAb,
    (ReciprocityTheory.ChartRestriction.G.Out.Inh.zeroPolAV (Sp R)).smoothDim⟩

theorem unit_free (A : Over (Sp R)) (hA : A = 𝟙_ (Over (Sp R))) :
    Module.Finite R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧ Module.Projective R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham (A.hom ≫ 𝟙 _)) p = 2 * 0) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham (A.hom ≫ 𝟙 _)) ≃ₗ[R] SecondDeRham (A.hom ≫ 𝟙 _),
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b := by
  have : IsIso (A.hom ≫ 𝟙 _) := by
    subst hA; exact inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
  have : Subsingleton (FirstDeRham (A.hom ≫ 𝟙 _)) :=
    ⟨fun a b ↦ (firstDeRham_base_eq_zero _ a).trans (firstDeRham_base_eq_zero _ b).symm⟩
  have : Subsingleton (SecondDeRham (A.hom ≫ 𝟙 _)) :=
    ⟨fun a b ↦ (deRham_h2_base_eq_zero R _ a).trans (deRham_h2_base_eq_zero R _ b).symm⟩
  have : Subsingleton (⋀[R]^2 (FirstDeRham (A.hom ≫ 𝟙 _))) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    have : Submodule.span R (Set.range
        (exteriorPower.ιMulti R 2 (M := FirstDeRham (A.hom ≫ 𝟙 _)))) ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      exact (exteriorPower.ιMulti R 2).map_coord_zero 0 (Subsingleton.elim _ _)
    exact this hx
  exact ⟨inferInstance, inferInstance, fun p ↦ by simp,
    LinearEquiv.ofSubsingleton _ _, fun a b ↦ Subsingleton.elim _ _⟩

theorem unit_hodge_duality :
    (AllPrim (dp0 R) (𝟙 _) (𝟙_ (Over (Sp R))) ∧ LieExact (𝟙_ (Over (Sp R))) ∧
      (∃ N : Submodule R (primDR (𝟙_ (Over (Sp R)))), IsCompl (PrimitiveSubmodule _) N) ∧
      Module.Finite R (PrimitiveSubmodule (𝟙_ (Over (Sp R)))) ∧ Module.Projective R (PrimitiveSubmodule (𝟙_ (Over (Sp R)))) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (PrimitiveSubmodule (𝟙_ (Over (Sp R)))) p = 0) ∧
    ∀ ψ : LinearMap.BilinForm R (HdR (𝟙_ (Over (Sp R)))),
      (∀ x ∈ Fil (𝟙_ (Over (Sp R))), ∀ y ∈ Fil (𝟙_ (Over (Sp R))), ψ x y = 0) ∧
        LinearMap.IsPerfPair ψ := by
  have : Subsingleton (primDR (𝟙_ (Over (Sp R)))) :=
    ⟨fun a b ↦ (primDR_unit a).trans (primDR_unit b).symm⟩
  have : Subsingleton (HdR (𝟙_ (Over (Sp R)))) :=
    ⟨fun a b ↦ (HdR_unit a).trans (HdR_unit b).symm⟩
  refine ⟨⟨allPrim_unit, lieExact_unit, ⟨⊤, ?_⟩, inferInstance, inferInstance,
    fun p ↦ congrFun Module.rankAtStalk_eq_zero_of_subsingleton p⟩,
    fun ψ ↦ ⟨fun x _ y _ ↦ by rw [HdR_unit x]; simp, ?_⟩⟩
  · rw [Subsingleton.elim (PrimitiveSubmodule (𝟙_ (Over (Sp R)))) ⊥]; exact isCompl_bot_top
  · have key : ∀ f : HdR (𝟙_ (Over (Sp R))) → Module.Dual R (HdR (𝟙_ (Over (Sp R)))),
        Function.Bijective f := fun f ↦
      ⟨fun a b _ ↦ Subsingleton.elim a b, fun c ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    exact ⟨key _, key _⟩

theorem elliptic (H : AbelianDeRham) (k : Type) [Field k] (W : WeierstrassCurve k) [W.IsElliptic] :
    (∀ p : PrimeSpectrum k, Module.rankAtStalk (primDR (GlobalTheory.WeierstrassCurve.ellPolAV W).A) p = 2) ∧
    (∀ p : PrimeSpectrum k, Module.rankAtStalk (PrimitiveSubmodule (GlobalTheory.WeierstrassCurve.ellPolAV W).A) p = 1) ∧
    ∀ ψ, IsPolForm (dp0 k) (𝟙 _) (GlobalTheory.WeierstrassCurve.ellPolAV W).A
      (GlobalTheory.WeierstrassCurve.ellPolAV W).L ψ → LinearMap.IsPerfPair ψ := by
  let P := GlobalTheory.WeierstrassCurve.ellPolAV W
  have hg : SmoothOfRelativeDimension 1 P.A.hom := P.smoothDim
  exact ⟨(H.1.prim P.isAb hg).2.2, (H.2.1 k P.A 1 P.isAb hg).2.2.2.2,
    fun ψ h ↦ (H.2.2.2.2 k P.A 1 P.isAb hg P.L P.isLB ψ h).2 P.ktriv⟩

theorem dual_hyp : IsNilDP (epsDP R) ∧ Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom :=
  ⟨isDPNilpotent_squareZero _, fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩⟩

theorem not_kTriv (H : AbelianDeRham) (k : Type) [Field k] (W : WeierstrassCurve k) [W.IsElliptic] :
    ¬ ReciprocityTheory.ChartRestriction.G.Out.KTriv (GlobalTheory.WeierstrassCurve.ellPolAV W).A
      (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB _) := by
  intro hK
  let P := GlobalTheory.WeierstrassCurve.ellPolAV W
  have hg : SmoothOfRelativeDimension 1 P.A.hom := P.smoothDim
  have hp := (H.2.2.2.2 k P.A 1 P.isAb hg _ (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB _) 0
    (isPolForm_zero _ fun _ _ ↦ rfl)).2 hK
  have h0 : Subsingleton (HdR P.A) := ⟨fun a b ↦ hp.bijective_left.1 rfl⟩
  have h1 : Subsingleton (primDR P.A) := (Module.subsingleton_dual_iff k).1 h0
  have h2 := (H.1.prim P.isAb hg).2.2 ⊥
  rw [Module.rankAtStalk_eq_zero_of_subsingleton] at h2
  simp at h2

end GlobalTheory.Published.AbelianDeRham.Test
