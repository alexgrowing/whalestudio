import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R}

theorem ext_of_pts (hP : IsProper π) (hS : Surjective π) (hI : IsIntegral S) {Y W : Over (Sp R)} (hY : Flat Y.hom)
    (f₁ f₂ : Y ⟶ W) (h : ∀ (T : Over S) (P : Over.mk (T.hom ≫ π) ⟶ Y), P ≫ f₁ = P ≫ f₂) : f₁ = f₂ := by
  have hpb : IsPullback (pullback.fst Y.hom π) (pullback.snd Y.hom π) Y.hom π := IsPullback.of_hasPullback _ _
  have key : pullback.fst Y.hom π ≫ f₁.left = pullback.fst Y.hom π ≫ f₂.left := by
    have := h (Over.mk (pullback.snd Y.hom π)) (Over.homMk (pullback.fst Y.hom π) pullback.condition)
    simpa using congrArg CommaMorphism.left this
  obtain ⟨h₀, _, hu⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S Y.left (pullback Y.hom π) W.left π Y.hom (pullback.fst Y.hom π)
    (pullback.snd Y.hom π) hP hS hI hY hpb (pullback.fst Y.hom π ≫ f₁.left)
    (by rw [← Category.assoc, ← Category.assoc, pullback.condition])
  ext
  exact (hu _ rfl).trans (hu _ key.symm).symm

variable {G' : Over S} {G : Over (Sp R)} {β : G'.left ⟶ G.left}

def dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : Over.mk (T.hom ≫ π) ⟶ G :=
  Over.homMk (x.left ≫ β) (by
    change x.left ≫ β ≫ G.hom = T.hom ≫ π
    rw [hpb.w, ← Category.assoc, Over.w x])

def up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) : T ⟶ G' :=
  Over.homMk (hpb.lift a.left T.hom (by simpa using Over.w a)) (hpb.lift_snd _ _ _)

theorem dn_up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) :
    dn hpb (up hpb a) = a := by
  ext; simp [dn, up]

theorem up_dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : up hpb (dn hpb x) = x := by
  ext; apply hpb.hom_ext <;> simp [dn, up]

end GlobalTheory.Mum.DescGrp

end

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R} {G' : Over S} [GrpObj G'] {G : Over (Sp R)} {β : G'.left ⟶ G.left}

theorem pt_mul (hpb : IsPullback β G'.hom G.hom π) (m : G ⊗ G ⟶ G)
    (hm : ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β)
    (T : Over S) (a b : Over.mk (T.hom ≫ π) ⟶ G) : lift a b ≫ m = dn hpb (up hpb a * up hpb b) := by
  ext
  rw [hm T (up hpb a) (up hpb b) a b (by simp [up]) (by simp [up])]
  rfl

theorem pt_one (hpb : IsPullback β G'.hom G.hom π) (e : 𝟙_ (Over (Sp R)) ⟶ G)
    (he : ∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) (T : Over S) :
    toUnit (Over.mk (T.hom ≫ π)) ≫ e = dn hpb 1 := by
  ext; rw [he]; rfl

theorem pt_inv (hpb : IsPullback β G'.hom G.hom π) (i : G ⟶ G)
    (hi : ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      (x₀ ≫ i).left = x⁻¹.left ≫ β) (T : Over S) (a : Over.mk (T.hom ≫ π) ⟶ G) :
    a ≫ i = dn hpb (up hpb a)⁻¹ := by
  ext; rw [hi T (up hpb a) a (by simp [up])]; rfl

section shapes
variable {G : Over (Sp R)} {T : Over (Sp R)}

theorem sh_assocL (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (m ▷ G) ≫ m = lift (lift (P ≫ fst _ _ ≫ fst _ _) (P ≫ fst _ _ ≫ snd _ _) ≫ m) (P ≫ snd _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_assocR (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (α_ G G G).hom ≫ (G ◁ m) ≫ m =
      lift (P ≫ fst _ _ ≫ fst _ _) (lift (P ≫ fst _ _ ≫ snd _ _) (P ≫ snd _ _) ≫ m) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneL (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (λ_ G).inv ≫ (e ▷ G) ≫ m = lift (toUnit T ≫ e) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneR (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (ρ_ G).inv ≫ (G ◁ e) ≫ m = lift P (toUnit T ≫ e) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_comm (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (β_ G G).hom ≫ m = lift (P ≫ snd _ _) (P ≫ fst _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_id (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ m = lift (P ≫ fst _ _) (P ≫ snd _ _) ≫ m := by
  rw [← comp_lift, lift_fst_snd, Category.comp_id]
theorem sh_invL (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift i (𝟙 G) ≫ m = lift (P ≫ i) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_invR (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift (𝟙 G) i ≫ m = lift P (P ≫ i) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_unit (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) : P ≫ toUnit G ≫ e = toUnit T ≫ e := by
  rw [← Category.assoc, comp_toUnit]
end shapes

theorem flat_prod2 (G : Over (Sp R)) [Flat G.hom] : Flat (G ⊗ G).hom :=
  inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
theorem flat_prod3 (G : Over (Sp R)) [Flat G.hom] : Flat ((G ⊗ G) ⊗ G).hom := by
  have := flat_prod2 G
  exact inferInstanceAs (Flat (pullback.fst (G ⊗ G).hom G.hom ≫ (G ⊗ G).hom))

end GlobalTheory.Mum.DescGrp

open GlobalTheory.Mum.DescGrp in

theorem GlobalTheory.Mum.descGrpObj_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ (m : G ⊗ G ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (i : G ⟶ G), (∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β) → (∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) → (∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β) → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hP hS hI G' _ _ G β hsm hpb m e i hm he hi
  haveI : Smooth G.hom := hsm
  have f1 : Flat G.hom := inferInstance
  have f2 : Flat (G ⊗ G).hom := flat_prod2 G
  have f3 : Flat ((G ⊗ G) ⊗ G).hom := flat_prod3 G
  have hM := pt_mul hpb m hm
  have hE := pt_one hpb e he
  have hI' := pt_inv hpb i hi
  have a1 : e ▷ G ≫ m = (λ_ G).hom := by
    rw [← cancel_epi (λ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneL, Category.comp_id, hE, hM, up_dn, _root_.one_mul, dn_up]
  have a2 : G ◁ e ≫ m = (ρ_ G).hom := by
    rw [← cancel_epi (ρ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneR, Category.comp_id, hE, hM, up_dn, _root_.mul_one, dn_up]
  have a3 : m ▷ G ≫ m = (α_ G G G).hom ≫ G ◁ m ≫ m := by
    refine ext_of_pts hP hS hI f3 _ _ (fun T P => ?_)
    rw [sh_assocL, sh_assocR]
    simp only [hM, up_dn, _root_.mul_assoc]
  have a4 : lift i (𝟙 G) ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invL, sh_unit, hE, hI', hM, up_dn, _root_.inv_mul_cancel]
  have a5 : lift (𝟙 G) i ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invR, sh_unit, hE, hI', hM, up_dn, _root_.mul_inv_cancel]
  have a6 : (β_ G G).hom ≫ m = m := by
    refine ext_of_pts hP hS hI f2 _ _ (fun T P => ?_)
    rw [sh_comm, sh_id P m, hM, hM]
    letI : CommMonoid (T ⟶ G') := Hom.commMonoid
    rw [_root_.mul_comm]
  letI inst : GrpObj G :=
    { one := e, mul := m, inv := i, one_mul := a1, mul_one := a2, mul_assoc := a3, left_inv := a4,
      right_inv := a5 }
  exact ⟨inst, ⟨a6⟩, hpb, fun T x y x₀ y₀ hx hy => by
    rw [Hom.mul_def]; exact hm T x y x₀ y₀ hx hy⟩
