import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ThickEndo

variable {S S' : Scheme.{0}}

theorem homEquiv_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : (Over.map φ).obj X ⟶ A) :
    (Over.mapPullbackAdj φ).homEquiv X A (a * b) =
      (Over.mapPullbackAdj φ).homEquiv X A a * (Over.mapPullbackAdj φ).homEquiv X A b := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Hom.mul_def,
    Hom.mul_def, Functor.obj.μ_def, ← comp_lift_assoc, ← Category.assoc (lift _ _),
    Functor.Monoidal.lift_μ, CategoryTheory.Functor.map_comp]

theorem homEquiv_symm_mul' (φ : S' ⟶ S) (X : Over S') (A : Over S) [GrpObj A]
    (a b : X ⟶ (Over.pullback φ).obj A) :
    ((Over.mapPullbackAdj φ).homEquiv X A).symm (a * b) =
      ((Over.mapPullbackAdj φ).homEquiv X A).symm a * ((Over.mapPullbackAdj φ).homEquiv X A).symm b := by
  apply ((Over.mapPullbackAdj φ).homEquiv X A).injective
  rw [homEquiv_mul', Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem homEquiv_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (k : (Over.map t).obj Y ⟶ A) :
    ((Over.mapPullbackAdj t).homEquiv Y A k).left ≫ pullback.fst A.hom t = k.left := by
  rw [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

theorem homEquiv_symm_left' (t : S' ⟶ S) {Y : Over S'} {A : Over S} (q : Y ⟶ (Over.pullback t).obj A) :
    (((Over.mapPullbackAdj t).homEquiv Y A).symm q).left = q.left ≫ pullback.fst A.hom t := by
  have := homEquiv_left' t (((Over.mapPullbackAdj t).homEquiv Y A).symm q)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

variable {R : Type} [CommRing R] (I : Ideal R) {B : Type} [CommRing B] [IsLocalRing B]

theorem le_comap_of_mem_range {φ : CommRingCat.of R ⟶ CommRingCat.of B}
    (h : Spec.map φ (closedPoint B) ∈ Set.range (thick R I 0)) :
    I ≤ (maximalIdeal B).comap φ.hom := by
  obtain ⟨y, hy⟩ := h
  intro a ha
  have h1 : a ∈ ((thick R I 0) y).asIdeal := by
    show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)]
    exact zero_mem _
  rw [hy] at h1
  exact h1

def lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ Sp (R ⧸ I ^ (e + 1)) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ.hom
    ((Ideal.pow_right_mono hI (e + 1)).trans (Ideal.le_comap_pow _ _))))

variable {I}

theorem lev_thick (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom) (e : ℕ) :
    lev I φ hI e ≫ thick R I e = thick B (maximalIdeal B) e ≫ Spec.map φ := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem adicLevelMap_lev (φ : CommRingCat.of R ⟶ CommRingCat.of B) (hI : I ≤ (maximalIdeal B).comap φ.hom)
    (e : ℕ) : adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ lev I φ hI (e + 1) =
      lev I φ hI e ≫ thickTrans R I e := by
  rw [lev, lev, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  exact Ideal.Quotient.ringHom_ext rfl

end GlobalTheory.ThickEndo

namespace GlobalTheory.ThickEndo

section Main

variable {R : Type} [CommRing R] {I : Ideal R} {G : Over (Sp R)} [GrpObj G] {B : Type} [CommRing B]
  [IsLocalRing B] {φ : CommRingCat.of R ⟶ CommRingCat.of B} (hI : I ≤ (maximalIdeal B).comap φ.hom)

abbrev lvl (e : ℕ) : Over (Sp (R ⧸ I ^ (e + 1))) := Over.mk (lev I φ hI e)

def incl (e : ℕ) : (Over.map (thick R I e)).obj (lvl hI e) ⟶ Over.mk (Spec.map φ) :=
  Over.homMk (thick B (maximalIdeal B) e) (lev_thick φ hI e).symm

def red (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) : lvl hI e ⟶ thickObj R I e G :=
  (Over.mapPullbackAdj (thick R I e)).homEquiv (lvl hI e) G (incl hI e ≫ x)

theorem red_fst (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left :=
  homEquiv_left' _ _

theorem red_snd (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    (red hI e x).left ≫ pullback.snd G.hom (thick R I e) = lev I φ hI e :=
  Over.w (red hI e x)

omit [GrpObj G] in
theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [GrpObj G] in
theorem thickMap_snd (e : ℕ) :
    thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I e) ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem red_succ (e : ℕ) (x : Over.mk (Spec.map φ) ⟶ G) :
    adicLevelMap (maximalIdeal B) (Nat.le_succ (e + 1)) ≫ (red hI (e + 1) x).left =
      (red hI e x).left ≫ thickMap R I e G := by
  apply pullback.hom_ext
  · rw [Category.assoc, red_fst, Category.assoc, thickMap_fst, red_fst]
    exact adicLevelMap_ι_assoc (maximalIdeal B) (Nat.le_succ (e + 1)) x.left
  · rw [Category.assoc, red_snd, Category.assoc, thickMap_snd, ← Category.assoc, red_snd, adicLevelMap_lev]

variable (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G)

def fam (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ G.left :=
  (red hI e x ≫ b e).left ≫ pullback.fst G.hom (thick R I e)

variable {b}

theorem fam_adic (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : IsAdicFamily (maximalIdeal B) (fam hI b x) := fun e => by
  simp only [fam, Over.comp_left, Category.assoc]
  rw [← Category.assoc (adicLevelMap _ _), red_succ, Category.assoc, ← Category.assoc (thickMap R I e G),
    hb, Category.assoc, thickMap_fst]

variable (b) in
theorem fam_over (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    fam hI b x e ≫ G.hom = adicLevelι (maximalIdeal B) (e + 1) ≫ Spec.map φ := by
  have hw : (b e).left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w (b e)
  simp only [fam, Over.comp_left, Category.assoc]
  rw [pullback.condition, ← Category.assoc ((b e).left), hw, ← Category.assoc, red_snd, lev_thick]

variable [IsAdicComplete (maximalIdeal B) B]

theorem exists_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : ∃ g : Sp B ⟶ G.left, g ≫ G.hom = Spec.map φ ∧
      ∀ e, adicLevelι (maximalIdeal B) (e + 1) ≫ g = fam hI b x e :=
  (existsUnique_over_of_isAdicFamily (Spec.map φ) G.hom (fam_adic hI hb x) (fam_over hI b x)).exists

def lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) : Over.mk (Spec.map φ) ⟶ G :=
  Over.homMk (exists_lim hI hb x).choose (exists_lim hI hb x).choose_spec.1

theorem lim_level (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    thick B (maximalIdeal B) e ≫ (lim hI hb x).left = fam hI b x e :=
  (exists_lim hI hb x).choose_spec.2 e

theorem incl_lim (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x : Over.mk (Spec.map φ) ⟶ G) (e : ℕ) :
    incl hI e ≫ lim hI hb x = ((Over.mapPullbackAdj (thick R I e)).homEquiv _ G).symm (red hI e x ≫ b e) := by
  apply Over.OverMorphism.ext
  rw [homEquiv_symm_left', Over.comp_left]
  exact lim_level hI hb x e

theorem lim_mul (hmon : ∀ e, IsMonHom (b e))
    (hb : ∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G)
    (x y : Over.mk (Spec.map φ) ⟶ G) : lim hI hb (x * y) = lim hI hb x * lim hI hb y := by
  have he : ∀ e, incl hI e ≫ lim hI hb (x * y) = incl hI e ≫ (lim hI hb x * lim hI hb y) := by
    intro e
    have := hmon e
    rw [comp_mul, incl_lim, incl_lim, incl_lim, red, comp_mul, homEquiv_mul', mul_comp, homEquiv_symm_mul']
    rfl
  exact Over.OverMorphism.ext (hom_ext_of_isHausdorff (maximalIdeal B) fun e => congrArg (·.left) (he e))

end Main

end GlobalTheory.ThickEndo

open GlobalTheory.ThickEndo in

theorem GlobalTheory.exists_mul_map_points_of_thickEndo : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  intro R _ I G _ b hmon hb B _ _ _ s hs
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hI := le_comap_of_mem_range I hs
  refine ⟨lim hI hb, fun x y => lim_mul hI hmon hb x y, fun x e => ⟨(red hI e x).left, red_fst hI e x, ?_⟩⟩
  rw [lim_level hI hb x e]
  simp only [fam, Over.comp_left, Category.assoc]
