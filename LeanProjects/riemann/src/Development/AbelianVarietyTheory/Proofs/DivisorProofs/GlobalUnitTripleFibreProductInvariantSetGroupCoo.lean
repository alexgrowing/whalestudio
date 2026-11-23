import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm.RigidW

theorem triple_ext {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g h : Z ⟶ Triple f)
    (h1 : g ≫ pullback.fst _ _ ≫ pullback.fst f f = h ≫ pullback.fst _ _ ≫ pullback.fst f f)
    (h2 : g ≫ pullback.fst _ _ ≫ pullback.snd f f = h ≫ pullback.fst _ _ ≫ pullback.snd f f)
    (h3 : g ≫ pullback.snd _ _ ≫ pullback.snd f f = h ≫ pullback.snd _ _ ≫ pullback.snd f f) : g = h := by
  have c := pullback.condition (f := pullback.snd f f) (g := pullback.fst f f)
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · simpa only [Category.assoc] using h2
  · apply pullback.hom_ext
    · simp only [Category.assoc, ← c]
      simpa only [Category.assoc] using h2
    · simpa only [Category.assoc] using h3

theorem appTop_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

theorem snd_hom : pullback.snd (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom := by
  rw [← Over.w (q ▷ B), pullback.condition_assoc]

variable (B) in

def W0 : Over (Sp K) :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom : Triple (q ▷ B).left ⟶ Sp K)

def p1 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) (by simp [W0])

def p2 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom])

def p3 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom, ← pullback.condition_assoc, snd_hom])

theorem rigidityTripleFibreProductFirstCoord_left : (p1 q).left = pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductSecondCoord_left : (p2 q).left = pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductThirdCoord_left : (p3 q).left = pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl

theorem p12 : p1 q ≫ q ▷ B = p2 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductFirstCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem p23 : p2 q ≫ q ▷ B = p3 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductThirdCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (congrArg (· ≫ _) pullback.condition).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))

end
end GlobalTheory.DescNorm.RigidW

namespace GlobalTheory.DescNorm.RigidW
section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

def beta : W0 B q ⟶ B := p1 q ≫ snd A B

theorem rigidityTripleSecondCoord_snd_eq_groupCoord : p2 q ≫ snd A B = beta q := by
  rw [beta, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p12]

theorem rigidityTripleThirdCoord_snd_eq_groupCoord : p3 q ≫ snd A B = beta q := by
  rw [← rigidityTripleSecondCoord_snd_eq_groupCoord, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p23]

def E (u : W0 B q ⟶ A ⊗ B) : B ⊗ W0 B q ⟶ A ⊗ B := lift (snd B (W0 B q) ≫ u ≫ fst A B) (fst B (W0 B q))

theorem E_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) : E q u ≫ q ▷ B = E q v ≫ q ▷ B := by
  have h' : u ≫ fst A B ≫ q = v ≫ fst A B ≫ q := by
    have := congrArg (· ≫ fst A' B) h
    simpa using this
  apply CartesianMonoidalCategory.hom_ext
  · simp [E, h']
  · simp [E]

theorem E_left_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) :
    (E q u).left ≫ (q ▷ B).left = (E q v).left ≫ (q ▷ B).left := by
  rw [← Over.comp_left, ← Over.comp_left, E_eq q h]

theorem lift_E (x : W0 B q ⟶ B) (u : W0 B q ⟶ A ⊗ B) : lift x (𝟙 _) ≫ E q u = lift (u ≫ fst A B) x := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [E]

def eL : (B ⊗ W0 B q).left ⟶ Triple (q ▷ B).left :=
  pullback.lift (pullback.lift (E q (p1 q)).left (E q (p2 q)).left (E_left_eq q (p12 q)))
    (pullback.lift (E q (p2 q)).left (E q (p3 q)).left (E_left_eq q (p23 q)))
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

theorem eL_1 : eL q ≫ pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left = (E q (p1 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
theorem eL_2 : eL q ≫ pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p2 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
theorem eL_3 : eL q ≫ pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p3 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]

theorem sec_beta : (lift (beta q) (𝟙 (W0 B q))).left ≫ eL q = 𝟙 _ := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p1 q ≫ fst A B) (beta q) = p1 q)).trans
      ((rigidityTripleFibreProductFirstCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [beta]
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p2 q ≫ fst A B) (beta q) = p2 q)).trans
      ((rigidityTripleFibreProductSecondCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleSecondCoord_snd_eq_groupCoord]
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p3 q ≫ fst A B) (beta q) = p3 q)).trans
      ((rigidityTripleFibreProductThirdCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleThirdCoord_snd_eq_groupCoord]

theorem lift_one (u : W0 B q ⟶ A ⊗ B) : lift (u ≫ fst A B) (1 : W0 B q ⟶ B) = u ≫ zb A B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [zb]
  · simp [zb, MonObj.comp_one]

theorem sec_one : (lift (1 : W0 B q ⟶ B) (𝟙 (W0 B q))).left ≫ eL q = rhoW q := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductFirstCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_fst q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductSecondCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductThirdCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_snd_assoc q _).symm

theorem rhoW_appTop (hB : IsAbelianScheme B) (D : Γ(Triple (q ▷ B).left, ⊤)) : (rhoW q).appTop.hom D = D := by
  have hs : Function.Surjective ((snd B (W0 B q)).left.appTop).hom :=
    surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback (W0 B q).hom B hB) ⊤
  obtain ⟨F, hF⟩ := hs ((eL q).appTop.hom D)
  have hsnd : ∀ x : W0 B q ⟶ B, (lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have key : ∀ x : W0 B q ⟶ B, ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D = F := by
    intro x
    calc ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D
        = (lift x (𝟙 (W0 B q))).left.appTop.hom ((eL q).appTop.hom D) := appTop_comp _ _ _
      _ = (lift x (𝟙 (W0 B q))).left.appTop.hom ((snd B (W0 B q)).left.appTop.hom F) := by rw [hF]
      _ = ((lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left).appTop.hom F := (appTop_comp _ _ _).symm
      _ = F := by rw [hsnd x, Scheme.Hom.id_appTop]; rfl
  have h1 : D = F := by
    have h := key (beta q)
    rw [sec_beta] at h
    exact h
  have h0 := key 1
  rw [sec_one] at h0
  exact h0.trans h1.symm

end

theorem gm_rhoW_eq_gm_id_of_abelian : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B →
    ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  intro K _ A A' B _ q hB D w
  have := gm_comp_top (𝟙 _) (rhoW q) w D D (rhoW_appTop q hB D.val)
  rwa [Category.id_comp] at this

end GlobalTheory.DescNorm.RigidW
