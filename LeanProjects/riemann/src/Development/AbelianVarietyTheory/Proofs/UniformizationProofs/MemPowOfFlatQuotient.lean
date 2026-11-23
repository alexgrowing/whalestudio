import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPushoutQuotientMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatThickenings

theorem mem_pow_of_flat_quotient {V C : Type} [CommRing V] [IsDomain V] [CommRing C] (σ : V →+* C)
    {ϖ : V} (hϖ : ϖ ≠ 0) (I : Ideal V) (hI : I = Ideal.span {ϖ}) (e : ℕ)
    (h : (Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1)))).Flat)
    {a : C} (ha : σ ϖ * a = 0) : a ∈ Ideal.span {σ ϖ} ^ e := by
  set φ := Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1))) with hφ
  let _ := φ.toAlgebra
  have : Module.Flat (V ⧸ I ^ (e + 1)) (C ⧸ (I ^ (e + 1)).map σ) := h
  have hsm : ∀ (v : V) (c : C), (Ideal.Quotient.mk (I ^ (e + 1)) v) •
      (Ideal.Quotient.mk ((I ^ (e + 1)).map σ) c) = Ideal.Quotient.mk _ (σ v * c) := by
    intro v c
    rw [Algebra.smul_def, map_mul]
    rfl
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := V ⧸ I ^ (e + 1)) (M := C ⧸ (I ^ (e + 1)).map σ)
    (f := fun _ : Unit => Ideal.Quotient.mk _ ϖ) (x := fun _ => Ideal.Quotient.mk _ a)
    (by rw [Fintype.sum_unique, hsm, ha, map_zero])
  choose c' hc' using fun j => Ideal.Quotient.mk_surjective (c () j)
  choose y' hy' using fun j => Ideal.Quotient.mk_surjective (y j)
  have hd : ∀ j, ϖ ^ e ∣ c' j := by
    intro j
    have h1 := hc j
    rw [Fintype.sum_unique, ← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ'] at h1
    exact (mul_dvd_mul_iff_left hϖ).1 h1
  have h2 : a - ∑ j, σ (c' j) * y' j ∈ (I ^ (e + 1)).map σ := by
    rw [← Ideal.Quotient.eq, map_sum]
    refine (hy ()).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc', ← hy', hsm]
  rw [hI, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
  have h3 : ∑ j, σ (c' j) * y' j ∈ Ideal.span {σ ϖ} ^ e := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    exact map_dvd σ (hd j)
  simpa using Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) h2) h3

theorem flat_of_flat_quotient {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsNoetherianRing C] (σ : V →+* C)
    (h : ∀ e : ℕ, (Ideal.quotientMap ((IsLocalRing.maximalIdeal V ^ (e + 1)).map σ) σ
      (Ideal.le_comap_map (I := IsLocalRing.maximalIdeal V ^ (e + 1)))).Flat) : σ.Flat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ a : C, σ ϖ * a = 0 → a = 0 := by
    intro a ha
    have hm : a ∈ ⨅ i : ℕ, (Ideal.span {σ ϖ} ^ i • ⊤ : Submodule C C) := by
      rw [Submodule.mem_iInf]
      intro e
      rw [smul_eq_mul, Ideal.mul_top]
      exact mem_pow_of_flat_quotient σ hϖ.ne_zero _ hϖ.maximalIdeal_eq e (h e) ha
    obtain ⟨⟨r, hr⟩, hra⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff _ a).1 hm
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [← hra]
    change c * σ ϖ * a = 0
    rw [_root_.mul_assoc, ha, mul_zero]
  have keyn : ∀ (n : ℕ) (a : C), σ ϖ ^ n * a = 0 → a = 0 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih => intro a ha; exact key a (ih _ (by rw [← ha]; ring))
  let _ := σ.toAlgebra
  change Module.Flat V C
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨v, hv⟩, hva⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hv) hϖ
  have h1 : σ (u * ϖ ^ n) * a = 0 := hva
  rw [map_mul, _root_.mul_assoc, map_pow] at h1
  exact keyn n a (((u.isUnit.map σ).mul_right_eq_zero).1 h1)

theorem flat_chart {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {B : Scheme.{0}} (f : B ⟶ Spec (CommRingCat.of V)) [LocallyOfFiniteType f]
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (b : ∀ e, (Y e).left ⟶ B)
    (hb : ∀ e, IsPullback (b e) (Y e).hom f (thick V (IsLocalRing.maximalIdeal V) e))
    (hY : ∀ e, Flat (Y e).hom) {C : CommRingCat.{0}} (u : Spec C ⟶ B) [IsOpenImmersion u] :
    Flat (u ≫ f) := by
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (u ≫ f)
  have hft : LocallyOfFiniteType (Spec.map σ) := by rw [hσ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{0})] at hft
  have hN : IsNoetherianRing C := by
    let _ : Algebra V C := σ.hom.toAlgebra
    have : Algebra.FiniteType V C := hft
    exact Algebra.FiniteType.isNoetherianRing V C
  rw [← hσ, HasRingHomProperty.Spec_iff (P := @Flat.{0})]
  refine flat_of_flat_quotient σ.hom fun e => ?_
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (NilpotentLift.isPushout_quotient_map (IsLocalRing.maximalIdeal V ^ (e + 1)) σ)
  have H' := (IsPullback.of_hasPullback (b e) u).flip.paste_vert (hb e)
  rw [← hσ] at H'
  have := hY e
  have hf : Flat ((H.isoIsPullback _ _ H').hom ≫ pullback.fst (b e) u ≫ (Y e).hom) := inferInstance
  rw [IsPullback.isoIsPullback_hom_snd, HasRingHomProperty.Spec_iff (P := @Flat.{0})] at hf
  exact hf

theorem flat_of_flat_thickenings :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [LocallyOfFiniteType B.hom] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → Flat B.hom := by
  intro V _ _ _ B _ Y b hb hY
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{0})
  exact IsZariskiLocalAtSource.of_openCover (P := @Flat) B.left.affineOpenCover.openCover
    fun i =>
      have : IsOpenImmersion (B.left.affineOpenCover.f i) := B.left.affineOpenCover.map_prop i
      flat_chart B.hom Y b hb hY (B.left.affineOpenCover.f i)

end GlobalTheory.FlatThickenings
