import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.MulN

theorem isMonHom_mulA {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom (mulA A n) := by
  induction n with
  | zero =>
    change IsMonHom (𝟙 A ^ 0)
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    change IsMonHom (𝟙 A ^ (n + 1))
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift (mulA A n) (𝟙 A) ≫ μ[A]))

theorem isPullback_baseChange {S T : Scheme.{0}} (t : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom t) ((Over.pullback t).map f).left f.left
      (pullback.fst Y.hom t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom t) (v₂₂ := Y.hom) (h₃₁ := t) ?_ ?_
    (IsPullback.of_hasPullback Y.hom t)
  · have h1 : ((Over.pullback t).map f).left ≫ pullback.snd Y.hom t = pullback.snd X.hom t :=
      pullback.lift_snd _ _ _
    rw [h1, Over.w f]
    exact IsPullback.of_hasPullback X.hom t
  · exact (pullback.lift_fst _ _ _).symm

theorem surjective_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Surjective ((Over.pullback t).map f).left) : Surjective f.left := by
  refine ⟨fun y => ?_⟩
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  obtain ⟨x, hx⟩ := ((Over.pullback t).map f).left.surjective (v p)
  refine ⟨pullback.fst X.hom t x, ?_⟩
  have e := (isPullback_baseChange t f).w
  have e1 : f.left (pullback.fst X.hom t x) =
      pullback.fst Y.hom t (((Over.pullback t).map f).left x) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  rw [e1, hx, ← Scheme.Hom.comp_apply]
  have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
  rw [this]
  exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)

theorem mulA_finite_flat_surjective_etale :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left) → (∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left → Flat f.left ∧ Surjective f.left) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFiniteType Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left) → (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left) := by
  intro hfin hK hfib hunr S _ P n hn
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hf := hfin S P n hn
  have hm := isMonHom_mulA P.A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map (mulA P.A n)).left ∧
        Surjective ((Over.pullback t).map (mulA P.A n)).left := fun K _ _ t =>
    hK K _ (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_baseChange t _) hf)
  have hflat : Flat (mulA P.A n).left :=
    hfib S _ _ _ inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1
  refine ⟨hf, hflat, surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2, fun hu => ?_⟩
  have := hunr S P.A n hu
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  exact Etale.of_formallyUnramified_of_flat _

end GlobalTheory.AbLaw.MulN
