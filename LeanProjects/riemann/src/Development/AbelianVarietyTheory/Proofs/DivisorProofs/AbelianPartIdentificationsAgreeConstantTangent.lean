import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigHom

theorem isNilpotent_ker_fst (k : Type) [Field k] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Submodule.mul_le.2 fun a ha b hb => ?_
  rw [RingHom.mem_ker] at ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  rw [Submodule.mem_bot]
  ext <;> simp [ha, hb]

theorem mk_ker_fst_eq (k : Type) [Field k] :
    Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) =
      ((Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom)).comp
        (algebraMap k (DualNumber k))).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq, RingHom.mem_ker]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.RigHom

namespace GlobalTheory.RigHom

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem comp_eq_of_const : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R) (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.P.A.left ⟶ B₀.left), IsGrpPullback Q.P.A B₀ (spMap ιb) β → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (GlobalTheory.RigChart.constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ ≫ β = π₂ ≫ β := by
  intro R _ _ Q W₀ _ ιb B₀ _ β hβ k _ ρ hρ B' _ π₁ π₂ h₁ h₂ h0
  have c₁ : IsGrpPullback B' B₀ (spMap (ρ.comp ιb)) (π₁ ≫ β) :=
    (IsGrpPullback.comp h₁ hβ).congr (spMap_comp' ιb ρ) rfl
  have c₂ : IsGrpPullback B' B₀ (spMap (ρ.comp ιb)) (π₂ ≫ β) := by
    refine (IsGrpPullback.comp h₂ hβ).congr ?_ rfl
    rw [spMap_comp', hρ]
    rfl
  have hab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb h₁
  obtain ⟨e₁, he₁, f₁⟩ := grpPullback_iso c₁ (isGrpPullback_pullback B₀ (spMap (ρ.comp ιb)))
  obtain ⟨e₂, he₂, f₂⟩ := grpPullback_iso c₂ (isGrpPullback_pullback B₀ (spMap (ρ.comp ιb)))
  let I := RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom
  have hI : I ≤ nilradical (DualNumber k) := by
    obtain ⟨n, hn⟩ := isNilpotent_ker_fst k
    intro x hx
    exact ⟨n, by
      have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  have hj : pullback.fst B'.hom (spMap (Ideal.Quotient.mk I)) ≫ π₁ =
      pullback.fst B'.hom (spMap (Ideal.Quotient.mk I)) ≫ π₂ := by
    refine h0 _ _ (pullback.snd B'.hom (spMap (Ideal.Quotient.mk I)) ≫
      spMap ((Ideal.Quotient.mk I).comp (algebraMap k (DualNumber k)))) ?_
    rw [pullback.condition, Category.assoc, spMap_comp']
    congr 2
    exact mk_ker_fst_eq k
  have key : e₁.hom = e₂.hom := by
    refine GlobalTheory.NilRigidity.eq_of_eq_on_quotient I hI B' _ hab e₁.hom e₂.hom ?_
      (by rw [he₁.one_hom, he₂.one_hom])
    apply pullback.hom_ext
    · have f₁' : e₁.hom.left ≫ pullback.fst B₀.hom (spMap (ρ.comp ιb)) = π₁ ≫ β := f₁
      have f₂' : e₂.hom.left ≫ pullback.fst B₀.hom (spMap (ρ.comp ιb)) = π₂ ≫ β := f₂
      rw [Category.assoc, Category.assoc, f₁', f₂', ← Category.assoc, hj, Category.assoc]
    · have w₁ : e₁.hom.left ≫ pullback.snd B₀.hom (spMap (ρ.comp ιb)) = B'.hom := Over.w e₁.hom
      have w₂ : e₂.hom.left ≫ pullback.snd B₀.hom (spMap (ρ.comp ιb)) = B'.hom := Over.w e₂.hom
      rw [Category.assoc, Category.assoc, w₁, w₂]
  rw [← f₁, ← f₂, key]

end GlobalTheory.RigHom
