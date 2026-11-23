import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.CrossTheta

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem cross_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (b : Y ⟶ Y) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k')))
    (H : ∀ y J, Good L y J → sval s₁ b y J * sval s₂' (𝟙 _) y J = sval s₂ b y J * sval s₁' (𝟙 _) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ (r ≫ b) z J * sval s₂' r z J = sval s₂ (r ≫ b) z J * sval s₁' r z J := by
  obtain ⟨I, hI, e⟩ := exists_good L hL (r z) (K := Bool) (fun c => cond c (b ≫ p) (𝟙 _ ≫ p))
    (fun c => J (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p))) (fun a c e => congrArg (fun q => J (r ≫ q)) e)
    (fun c => hJ (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p)))
  have v : ∀ (c : Y ⟶ Y) {m : ℤ} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => m))),
      I (c ≫ p) = J (r ≫ c ≫ p) → sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
    intro c m s hc
    rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
    exact gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _
  have h := congrArg (r.stalkMap z).hom (H (r z) I hI)
  rw [map_mul, map_mul, ← v b s₁ (e true), ← v b s₂ (e true), ← v (𝟙 _) s₁' (e false), ← v (𝟙 _) s₂' (e false),
    Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (a : A ⟶ A) [IsMonHom a] (x : T ⟶ A) :
    translT A x ≫ T ◁ a = T ◁ a ≫ translT A (x ≫ a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (a : A ⟶ A) [IsMonHom a] {k k' : ℤ} (θ : ThetaGrp A L k T) (θ' : ThetaGrp A L k' T) (hp : θ.pt = θ'.pt ≫ a)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A L k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A L k' T)}
    (h₁ : IsActOf A L k θ t₁ T₁) (h₂ : IsActOf A L k θ t₂ T₂) (h₁' : IsActOf A L k' θ' t₁' T₁')
    (h₂' : IsActOf A L k' θ' t₂' T₂') :
    (∀ y J, Good L y J → sval (L := L) t₁ (T ◁ a).left y J * sval (L := L) t₂' (𝟙 _) y J =
      sval (L := L) t₂ (T ◁ a).left y J * sval (L := L) t₁' (𝟙 _) y J) ↔
    (∀ y J, Good L y J → sval (L := L) T₁ (T ◁ a).left y J * sval (L := L) T₂' (𝟙 _) y J =
      sval (L := L) T₂ (T ◁ a).left y J * sval (L := L) T₁' (𝟙 _) y J) := by
  have c : (T ◁ a).left ≫ (translT A θ.pt).left = (translT A θ'.pt).left ≫ (T ◁ a).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}, Good L z J →
      (sval (L := L) T₁ (r ≫ (T ◁ a).left) z J * sval (L := L) T₂' r z J =
        sval (L := L) T₂ (r ≫ (T ◁ a).left) z J * sval (L := L) T₁' r z J ↔
      sval (L := L) t₁ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₂' (r ≫ (translT A θ'.pt).left) z J =
        sval (L := L) t₂ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₁' (r ≫ (translT A θ'.pt).left) z J) := by
    intro Z r z J hJ
    rw [ThetaPowOrder.act_sval h₁ _ z hJ, ThetaPowOrder.act_sval h₂ _ z hJ, ThetaPowOrder.act_sval h₁' _ z hJ,
      ThetaPowOrder.act_sval h₂' _ z hJ, Category.assoc, c, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L) t₂ _ z J), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J hJ
    have h := (key (𝟙 _) y hJ).2 (cross_val hL _ _ t₁ t₂ t₁' t₂' H _ y hJ)
    rwa [Category.id_comp] at h
  · intro H y J hJ
    have h := (key (translT A θ'.pt⁻¹).left y hJ).1 (cross_val hL _ _ T₁ T₂ T₁' T₂' H _ y hJ)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta

namespace GlobalTheory

theorem cross_iff_of_isActOf : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j j' : ℕ) (θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A.A A.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ a → ∀ (t₁ t₂ T₁ T₂ : SecA A F j) (t₁' t₂' T₁' T₂' : SecA A F j'), IsActOf A.A A.L j θ t₁ T₁ → IsActOf A.A A.L j θ t₂ T₂ → IsActOf A.A A.L j' θ' t₁' T₁' → IsActOf A.A A.L j' θ' t₂' T₂' → (Cross a t₁ t₂ t₁' t₂' ↔ Cross a T₁ T₂ T₁' T₂') := by
  intro _ R _ _ A F _ _ a ha j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  exact CrossTheta.cross_act A.isLB a θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
