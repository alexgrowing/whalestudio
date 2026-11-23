import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.ModelPoints

theorem exists_push_equiv {S S' : Scheme.{0}} (f : S' ⟶ S) (H : Over S) [GrpObj H] (T : Over S')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H),
      ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_comp_equiv {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (e : G ≅ H) [IsMonHom e.hom]
    (T : Over S) : ∃ π : (T ⟶ G) ≃* (T ⟶ H), ∀ y, π.symm y = y ≫ e.inv :=
  ⟨{ toFun := fun x => x ≫ e.hom
     invFun := fun y => y ≫ e.inv
     left_inv := fun x => by simp
     right_inv := fun x => by simp
     map_mul' := fun x y => MonObj.mul_comp x y e.hom }, fun _ => rfl⟩

theorem exists_equiv {S₁ S₂ S : Scheme.{0}} (f : S ⟶ S₁) (g : S ⟶ S₂) (A : Over S₁) [GrpObj A]
    (G : Over S₂) [GrpObj G] (e : (Over.pullback g).obj G ≅ (Over.pullback f).obj A) [IsMonHom e.hom]
    {T : Scheme.{0}} (t : T ⟶ S) (s₁ : T ⟶ S₁) (s₂ : T ⟶ S₂) (h₁ : s₁ = t ≫ f) (h₂ : s₂ = t ≫ g) :
    ∃ θ : (Over.mk s₁ ⟶ A) ≃* (Over.mk s₂ ⟶ G), ∀ (x : Over.mk s₁ ⟶ A) (z : T ⟶ pullback A.hom f),
      z ≫ pullback.fst A.hom f = x.left → z ≫ pullback.snd A.hom f = t →
      (θ x).left = z ≫ e.inv.left ≫ pullback.fst G.hom g := by
  obtain ⟨π₁, p₁⟩ := exists_push_equiv f A (Over.mk t) s₁ h₁
  obtain ⟨π₂, p₂⟩ := exists_push_equiv g G (Over.mk t) s₂ h₂
  obtain ⟨π, p⟩ := exists_comp_equiv e (Over.mk t)
  refine ⟨π₁.symm.trans (π.symm.trans π₂), fun x z hz hz' => ?_⟩
  have hx : π₁.symm x = Over.homMk z hz' := by
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hz.symm.trans (p₁ (Over.homMk z hz')).symm)
  show (π₂ (π.symm (π₁.symm x))).left = _
  rw [p₂, p, hx, Over.comp_left, Category.assoc]
  rfl

theorem spMap_comp_of_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap h = spMap g ≫ spMap f := by
  subst e
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem spMap_cancel {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {g : B →+* C}
    (hg : Function.Injective g) {a b : Sp B ⟶ Sp A} (e : spMap g ≫ a = spMap g ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e
  congr 1
  ext x
  exact hg (congrArg (fun q => q.hom x) e)

theorem points_model : ∀ (K W L : Type) [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G], IsModel (L := L) A G → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra W Ω] (j : L →+* Ω), j.comp (algebraMap K L) = algebraMap K Ω → j.comp (algebraMap W L) = algebraMap W Ω → ∃ θ : (Over.mk (spMap (algebraMap K Ω)) ⟶ A) ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G), (∀ τ : Ω →+* Ω, τ.comp j = j → ∀ x x', x'.left = spMap τ ≫ x.left → (θ x').left = spMap τ ≫ (θ x).left) ∧ ∀ (K' : Type) [Field K'] (i : L →+* K') (j' : K' →+* Ω), j'.comp i = j → ∀ (x : Over.mk (spMap (algebraMap K Ω)) ⟶ A) (y : Sp K' ⟶ A.left), spMap j' ≫ y = x.left → ∀ ρ : W →+* K', ρ = i.comp (algebraMap W L) → ∃ y' : Over.mk (spMap ρ) ⟶ G, ∀ c : ℕ, spMap j' ≫ (y' ^ c).left = (θ (x ^ c)).left := by
  intro K W L _ _ _ _ _ A _ G _ ⟨e, he⟩ Ω _ _ _ j hK hW
  obtain ⟨θ, hθ⟩ := exists_equiv (spMap (algebraMap K L)) (spMap (algebraMap W L)) A G e (spMap j)
    _ _ (spMap_comp_of_eq hK) (spMap_comp_of_eq hW)
  refine ⟨θ, fun τ hτ x x' hx => ?_, fun K' _ i j' hj x y hy ρ hρ => ?_⟩
  · have w : x.left ≫ A.hom = spMap j ≫ spMap (algebraMap K L) :=
      (Over.w x).trans (spMap_comp_of_eq hK)
    rw [hθ x (pullback.lift x.left (spMap j) w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
      hθ x' (spMap τ ≫ pullback.lift x.left (spMap j) w)
        (by rw [Category.assoc, pullback.lift_fst, hx])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hτ]), Category.assoc]
  · have w : y ≫ A.hom = spMap i ≫ spMap (algebraMap K L) := by
      apply spMap_cancel j'.injective
      rw [← Category.assoc, hy, ← Category.assoc, ← spMap_comp_of_eq hj]
      exact (Over.w x).trans (spMap_comp_of_eq hK)
    have w' : (pullback.lift y (spMap i) w ≫ e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap W L))) ≫ G.hom
        = spMap ρ := by
      have h₁ : e.inv.left ≫ pullback.snd G.hom (spMap (algebraMap W L))
          = pullback.snd A.hom (spMap (algebraMap K L)) := Over.w e.inv
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% h₁, pullback.lift_snd_assoc]
      exact (spMap_comp_of_eq hρ.symm).symm
    have hU : spMap j' ≫ spMap ρ = spMap (algebraMap W Ω) :=
      (spMap_comp_of_eq (by rw [hρ, ← RingHom.comp_assoc, hj, hW])).symm
    let U : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap ρ) := Over.homMk (spMap j') hU
    let y' : Over.mk (spMap ρ) ⟶ G := Over.homMk _ w'
    have hxy : θ x = U ≫ y' := by
      apply Over.OverMorphism.ext
      rw [hθ x (spMap j' ≫ pullback.lift y (spMap i) w)
        (by rw [Category.assoc, pullback.lift_fst, hy])
        (by rw [Category.assoc, pullback.lift_snd, ← spMap_comp_of_eq hj]), Category.assoc]
      rfl
    refine ⟨y', fun c => ?_⟩
    rw [map_pow, hxy, ← MonObj.comp_pow]
    rfl

end GlobalTheory.SS.ModelPoints
