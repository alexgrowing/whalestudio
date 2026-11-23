import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossIffOfIsActOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.CrossTheta₂

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} (p : Y' ⟶ X) {k : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k))) (r : Z ⟶ Y) (c : Y ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} {I : (Y ⟶ X) → L.ι} (hI : Good L (r z) I) (hc : I (c ≫ p) = J (r ≫ c ≫ p)) :
    sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
  rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
  exact GlobalTheory.CrossTheta.gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _

theorem cross_val {X₁ X₂ Y₁ Y₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂) (b : Y₁ ⟶ Y₂) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L₂ (fun _ : Fin 1 => p₂) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L₁ (fun _ : Fin 1 => p₁) (fun _ => k')))
    (H : ∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval s₁ b y J₂ * sval s₂' (𝟙 _) y J₁ = sval s₂ b y J₂ * sval s₁' (𝟙 _) y J₁)
    {Z : Scheme.{0}} (r : Z ⟶ Y₁) (z : Z) {J₁ J₂} (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    sval s₁ (r ≫ b) z J₂ * sval s₂' r z J₁ = sval s₂ (r ≫ b) z J₂ * sval s₁' r z J₁ := by
  obtain ⟨I₁, hI₁, e₁⟩ := exists_good L₁ hL₁ (r z) (K := Unit) (fun _ => 𝟙 _ ≫ p₁)
    (fun _ => J₁ (r ≫ 𝟙 _ ≫ p₁)) (fun _ _ _ => rfl) (fun _ => hJ₁ (r ≫ 𝟙 _ ≫ p₁))
  obtain ⟨I₂, hI₂, e₂⟩ := exists_good L₂ hL₂ (r z) (K := Unit) (fun _ => b ≫ p₂)
    (fun _ => J₂ (r ≫ b ≫ p₂)) (fun _ _ _ => rfl) (fun _ => hJ₂ (r ≫ b ≫ p₂))
  have h := congrArg (r.stalkMap z).hom (H (r z) I₁ I₂ hI₁ hI₂)
  rw [map_mul, map_mul, ← sval_comp p₂ s₁ r b z hI₂ (e₂ ()), ← sval_comp p₂ s₂ r b z hI₂ (e₂ ()),
    ← sval_comp p₁ s₁' r (𝟙 _) z hI₁ (e₁ ()), ← sval_comp p₁ s₂' r (𝟙 _) z hI₁ (e₁ ()), Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {T : Over S} (c : A₁ ⟶ A₂)
    [IsMonHom c] (x : T ⟶ A₁) :
    translT A₁ x ≫ T ◁ c = T ◁ c ≫ translT A₂ (x ≫ c) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {L₁ : LB A₁.left} {L₂ : LB A₂.left}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {T : Over S} (c : A₁ ⟶ A₂) [IsMonHom c] {k k' : ℤ}
    (θ : ThetaGrp A₂ L₂ k T) (θ' : ThetaGrp A₁ L₁ k' T) (hp : θ.pt = θ'.pt ≫ c)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A₂ L₂ k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A₁ L₁ k' T)}
    (h₁ : IsActOf A₂ L₂ k θ t₁ T₁) (h₂ : IsActOf A₂ L₂ k θ t₂ T₂) (h₁' : IsActOf A₁ L₁ k' θ' t₁' T₁')
    (h₂' : IsActOf A₁ L₁ k' θ' t₂' T₂') :
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) t₁ (T ◁ c).left y J₂ * sval (L := L₁) t₂' (𝟙 _) y J₁ =
        sval (L := L₂) t₂ (T ◁ c).left y J₂ * sval (L := L₁) t₁' (𝟙 _) y J₁) ↔
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) T₁ (T ◁ c).left y J₂ * sval (L := L₁) T₂' (𝟙 _) y J₁ =
        sval (L := L₂) T₂ (T ◁ c).left y J₂ * sval (L := L₁) T₁' (𝟙 _) y J₁) := by
  have cc : (T ◁ c).left ≫ (translT A₂ θ.pt).left = (translT A₁ θ'.pt).left ≫ (T ◁ c).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A₁).left) (z : Z) {J₁ J₂}, Good L₁ z J₁ → Good L₂ z J₂ →
      (sval (L := L₂) T₁ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₂' r z J₁ =
        sval (L := L₂) T₂ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₁' r z J₁ ↔
      sval (L := L₂) t₁ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₂' (r ≫ (translT A₁ θ'.pt).left) z J₁ =
        sval (L := L₂) t₂ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₁' (r ≫ (translT A₁ θ'.pt).left) z J₁) := by
    intro Z r z J₁ J₂ hJ₁ hJ₂
    rw [ThetaPowOrder.act_sval h₁ _ z hJ₂, ThetaPowOrder.act_sval h₂ _ z hJ₂, ThetaPowOrder.act_sval h₁' _ z hJ₁,
      ThetaPowOrder.act_sval h₂' _ z hJ₁, Category.assoc, cc, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L₂) t₂ _ z J₂), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (𝟙 _) y hJ₁ hJ₂).2 (cross_val hL₁ hL₂ _ _ _ t₁ t₂ t₁' t₂' H _ y hJ₁ hJ₂)
    rwa [Category.id_comp] at h
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (translT A₁ θ'.pt⁻¹).left y hJ₁ hJ₂).1 (cross_val hL₁ hL₂ _ _ _ T₁ T₂ T₁' T₂' H _ y hJ₁ hJ₂)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta₂

namespace GlobalTheory

theorem crossH_iff_of_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  intro R _ _ A₁ A₂ F _ _ c hc j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  haveI := hc
  exact CrossTheta₂.cross_act A₁.isLB A₂.isLB c θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
