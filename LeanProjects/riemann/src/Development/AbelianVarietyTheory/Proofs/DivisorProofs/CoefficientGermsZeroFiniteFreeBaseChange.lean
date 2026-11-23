import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FreeCoord

open GlobalTheory.BoxIndep TensorProduct

theorem eq_zero_of_germOf_max {B : CommRingCat.{0}} (a : B)
    (h : ∀ z : Spec B, z.asIdeal.IsMaximal → germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  have : (Ideal.span {a}).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal _ hne
    let z : Spec B := ⟨p, hp.isPrime⟩
    have h1 : algebraMap B ((Spec.structureSheaf B).presheaf.stalk z) a = 0 := h z hp
    have := StructureSheaf.IsLocalization.to_stalk B z
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff z.asIdeal.primeCompl _ _).1 h1
    exact c.2 (hI (Submodule.mem_annihilator_span_singleton _ _ |>.2 hc))
  have h1 : (1 : B) ∈ (Ideal.span {a}).annihilator := this ▸ Submodule.mem_top
  exact (one_smul B _).symm.trans ((Submodule.mem_annihilator_span_singleton _ _).1 h1)

theorem gs_comp' {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U) (f : Γ(X, U)) :
    gs (r ≫ F) z U f = (r.stalkMap z).hom (gs F (r z) U f) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem germ_eq_zero : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  intro R R₁ _ _ ρ₁ d b hb X f U a x hx h
  let _ : Algebra R R₁ := ρ₁.toAlgebra
  let A : CommRingCat.{0} := X.presheaf.stalk x
  let _ : Algebra R A := (germOf (B := CommRingCat.of R) f x).toAlgebra
  have hli : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun c hc =>
    congrFun ((hb 0).unique (y₁ := c) (y₂ := 0) (by simp only [Algebra.smul_def] at hc; exact hc.symm) (by simp))
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := fun r _ => by
    obtain ⟨c, hc, -⟩ := hb r
    rw [hc]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ (c l) (Submodule.subset_span ⟨l, rfl⟩)
  let β := Module.Basis.mk hli hsp
  have : Module.Finite R R₁ := Module.Finite.of_basis β
  let B : CommRingCat.{0} := CommRingCat.of (A ⊗[R] R₁)
  let iA : A ⟶ B := CommRingCat.ofHom (algebraMap A (A ⊗[R] R₁))
  let iR : CommRingCat.of R₁ ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).toRingHom
  have w : (Spec.map iA ≫ X.fromSpecStalk x) ≫ f = Spec.map iR ≫ spMap ρ₁ := by
    rw [Category.assoc, fromSpecStalk_comp (B := CommRingCat.of R)]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    ext r
    exact (IsScalarTower.algebraMap_apply R A (A ⊗[R] R₁) r).symm.trans
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).commutes r).symm
  let r : Spec B ⟶ pullback f (spMap ρ₁) := pullback.lift _ _ w
  have r1 : r ≫ pullback.fst f (spMap ρ₁) = Spec.map iA ≫ X.fromSpecStalk x := pullback.lift_fst _ _ _
  have r2 : r ≫ pullback.snd f (spMap ρ₁) = Spec.map iR := pullback.lift_snd _ _ _
  have key : (∑ l, iR.hom (b l) * iA.hom (gs (𝟙 X) x U (a l)) : B) = 0 := by
    refine eq_zero_of_germOf_max _ fun z hz => ?_
    have hm : (z.asIdeal.comap (algebraMap A (A ⊗[R] R₁))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := A ⊗[R] R₁) z.asIdeal
    have hc : Spec.map iA z = closedPoint A := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    have hzx : pullback.fst f (spMap ρ₁) (r z) = x := by
      have : (r ≫ pullback.fst f (spMap ρ₁)) z = X.fromSpecStalk x (Spec.map iA z) := by rw [r1]; rfl
      rw [hc, Scheme.fromSpecStalk_closedPoint] at this
      exact this
    have e := congrArg (r.stalkMap z).hom (h (r z) hzx)
    rw [map_zero, map_sum] at e
    rw [← e, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_mul, ← gs_comp' r _ z ⊤ trivial, ← gs_comp' r _ z U (hzx ▸ hx), r1, r2,
      gs_fromSpecStalk x hx, ← germOf_apply, ← germOf_map, ← germOf_map, Category.id_comp, Category.id_comp]
  have hli' := (Algebra.TensorProduct.basis A β).linearIndependent
  refine Fintype.linearIndependent_iff.1 hli' (fun l => gs (𝟙 X) x U (a l)) ?_
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  rw [Algebra.smul_def, _root_.mul_comm, Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
  rfl

end GlobalTheory.Mum.FreeCoord
