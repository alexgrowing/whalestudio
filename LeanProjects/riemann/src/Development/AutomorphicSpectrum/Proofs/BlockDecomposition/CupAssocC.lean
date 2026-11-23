import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CupAssocC

section
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem term_term (F : C ⥤ ModuleCat.{w} R) {p m n : ℕ} (s : ComposableArrows C n) (f : Cn F p)
    (g : Fin (m + 1) → Fin (n + 1)) (hg : Monotone g) (g' : Fin (p + 1) → Fin (m + 1)) (hg' : Monotone g') :
    (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last m)))))).hom (term F (hg.functor ⋙ s) f g' hg') =
      term F s f (g ∘ g') (hg.comp hg') := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last (g' (Fin.last p)))) ≫
      s.map (homOfLE (Fin.le_last (g (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (g (g' (Fin.last p))))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have key : ∀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (x : F.obj X),
      (F.map b).hom ((F.map a).hom x) = (F.map (a ≫ b)).hom x := by
    intro X Y Z a b x
    rw [F.map_comp]; rfl
  refine (key _ _ _).trans ?_
  exact congrArg (fun φ => (F.map φ).hom (f ((hg.comp hg').functor ⋙ s))) e

theorem term_id (F : C ⥤ ModuleCat.{w} R) {n : ℕ} (s : ComposableArrows C n) (f : Cn F n) :
    term F s f id monotone_id = f s := by
  have e : s.map (homOfLE (Fin.le_last (id (Fin.last n)))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  unfold term
  rw [e, F.map_id]
  rfl

theorem term_cupC {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q a n : ℕ} (h : p + q = a) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) (θ : Fin (a + 1) → Fin (n + 1)) (hθ : Monotone θ) :
    term F₃ s (P.cupC h f g) θ hθ =
      P.μ _ (term F₁ s f (θ ∘ front h) (hθ.comp (front_mono h)))
        (term F₂ s g (θ ∘ back h) (hθ.comp (back_mono h))) := by
  rw [← term_term F₁ s f θ hθ _ (front_mono h), ← term_term F₂ s g θ hθ _ (back_mono h), P.nat]
  rfl

theorem cupC_at {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) :
    P.cupC h f g s = P.μ _ (term F₁ s f (front h) (front_mono h)) (term F₂ s g (back h) (back_mono h)) := rfl

theorem term_one (A : C ⥤ CommAlgCat.{w} R) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin (0 + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (modF A) s (fun s => (1 : A.obj (s.obj (Fin.last 0)))) g hg = (1 : A.obj (s.obj (Fin.last n))) :=
  map_one (A.map (s.map (homOfLE (Fin.le_last (g (Fin.last 0)))))).hom

end

theorem cup_assocC : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R), (∀ n (x : Cn (modF A) n), (mulP A).cupC (Nat.zero_add n) (fun s => (1 : A.obj (s.obj (Fin.last 0)))) x = x ∧ (mulP A).cupC (Nat.add_zero n) x (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = x) ∧ ∀ {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n) (h₃ : q + r = b) (h₄ : p + b = n) x y z, (mulP A).cupC h₂ ((mulP A).cupC h₁ x y) z = (mulP A).cupC h₄ x ((mulP A).cupC h₃ y z) := by
  intro R _ C _ A
  refine ⟨fun n x => ⟨?_, ?_⟩, ?_⟩
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (back_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [back])), term_id]
    exact one_mul (M := A.obj (s.obj (Fin.last n))) _
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (front_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [front])), term_id]
    exact mul_one (M := A.obj (s.obj (Fin.last n))) _
  · intro p q r a b n h₁ h₂ h₃ h₄ x y z
    funext s
    rw [cupC_at, cupC_at, term_cupC, term_cupC,
      term_congr (modF A) s x ((front_mono h₂).comp (front_mono h₁)) (front_mono h₄)
        (funext fun i => Fin.ext (by simp [front])),
      term_congr (modF A) s y ((front_mono h₂).comp (back_mono h₁)) ((back_mono h₄).comp (front_mono h₃))
        (funext fun i => Fin.ext (by simp [front, back])),
      term_congr (modF A) s z (back_mono h₂) ((back_mono h₄).comp (back_mono h₃))
        (funext fun i => Fin.ext (by simp [back]; omega))]
    exact mul_assoc (G := A.obj (s.obj (Fin.last n))) _ _ _

end GlobalTheory.CompanionTheory.CupAssocC
