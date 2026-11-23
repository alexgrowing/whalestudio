import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.CechAugRowU

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe u v w

namespace GlobalTheory.CompanionTheory.CechFull

section Complexes

variable {R : Type} [CommRing R]

theorem mapH_mapH_of_inv {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R))
    (ψ : Cx.Hom L K (RingHom.id R)) (h : ∀ n x, ψ.f n (φ.f n x) = x) (p : ℕ) (x : K.H p) :
    ψ.mapH p (φ.mapH p x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ψ.mapZ p (φ.mapZ p z)) = Submodule.Quotient.mk z
  exact congrArg _ (Subtype.ext (h p z.1))

def equivH {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L K (RingHom.id R))
    (h : ∀ n x, ψ.f n (φ.f n x) = x) (h' : ∀ n x, φ.f n (ψ.f n x) = x) (p : ℕ) : K.H p ≃ₗ[R] L.H p :=
  LinearEquiv.ofLinear (φ.mapH p) (ψ.mapH p)
    (LinearMap.ext (mapH_mapH_of_inv ψ φ h' p)) (LinearMap.ext (mapH_mapH_of_inv φ ψ h p))

def cosHom {K L : Cos.{w} R} (f : ∀ n, K.X n →ₗ[R] L.X n)
    (h : ∀ n k x, L.δ n k (f n x) = f (n + 1) (K.δ n k x)) : Cx.Hom K.cx L.cx (RingHom.id R) :=
  ⟨f, fun n x => by
    change L.d n (f n x) = f (n + 1) (K.d n x)
    rw [Cos.d_apply, Cos.d_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul, h]⟩

end Complexes

section Cat

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem pull_pull_of_inv {C' : Type u} [Category.{v} C'] {G : C ⥤ ModuleCat.{w} R} {G' : C' ⥤ ModuleCat.{w} R}
    (m : CH.Mor G G' (RingHom.id R)) (m' : CH.Mor G' G (RingHom.id R))
    (h : ∀ n f, m'.pullC n (m.pullC n f) = f) (p : ℕ) (x : CH.H G p) : m'.pull p (m.pull p x) = x :=
  mapH_mapH_of_inv m.hom m'.hom h p x

variable (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C)

abbrev subFam : ι → ObjectProperty Q.FullSubcategory := fun α T => W α T.obj

variable {Q W}

def upG (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT W i).FullSubcategory ⥤ (capT (subFam Q W) i).FullSubcategory :=
  (capT (subFam Q W) i).lift (Q.lift (capT W i).ι fun T => hW (i 0) _ (T.property 0)) fun T => T.property

def downG {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT (subFam Q W) i).FullSubcategory ⥤ (capT W i).FullSubcategory :=
  (capT W i).lift ((capT (subFam Q W) i).ι ⋙ Q.ι) fun T => T.property

def upM (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) ((capT W i).ι ⋙ F) (RingHom.id R) where
  G := upG hW i
  τ _ := LinearMap.id
  nat _ _ := rfl

def downM {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT W i).ι ⋙ F) ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) (RingHom.id R) where
  G := downG i
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem down_up_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) m) :
    (downM F i).pullC m ((upM F hW i).pullC m f) = f := rfl

theorem up_down_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT W i).ι ⋙ F) m) :
    (upM F hW i).pullC m ((downM F i).pullC m f) = f := rfl

end Cat

section Assemble

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) {Q : ObjectProperty C} {ι : Type} {W : ι → ObjectProperty C}

def upX (hW : ∀ α, W α ≤ Q) (q n : ℕ) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).X n →ₗ[R] (cechH F W q).X n :=
  LinearMap.pi fun i => ((upM F hW i).pull q).comp (LinearMap.proj i)

def downX (q n : ℕ) :
    (cechH F W q).X n →ₗ[R] (cechH (Q.ι ⋙ F) (subFam Q W) q).X n :=
  LinearMap.pi fun i => ((downM F i).pull q).comp (LinearMap.proj i)

theorem upX_δ (hW : ∀ α, W α ≤ Q) (q n : ℕ) (k : Fin (n + 2))
    (x : (cechH (Q.ι ⋙ F) (subFam Q W) q).X n) :
    (cechH F W q).δ n k (upX F hW q n x) = upX F hW q (n + 1) ((cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU F _).pull q ((upM F hW (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (upM F hW t).pull q ((resU (Q.ι ⋙ F) _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

theorem downX_δ (q n : ℕ) (k : Fin (n + 2)) (x : (cechH F W q).X n) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k (downX (Q := Q) F q n x) =
      downX (Q := Q) F q (n + 1) ((cechH F W q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU (Q.ι ⋙ F) _).pull q ((downM F (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (downM F t).pull q ((resU F _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

end Assemble

theorem cechH_fullSubcategory_H : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p,
    Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  intro R _ C _ F Q ι W hW q p
  exact ⟨equivH (cosHom (upX F hW q) (upX_δ F hW q)) (cosHom (downX (Q := Q) F q) (downX_δ F q))
    (fun n x => funext fun i => pull_pull_of_inv (upM F hW i) (downM F i) (down_up_pullC F hW i) q (x i))
    (fun n x => funext fun i => pull_pull_of_inv (downM F i) (upM F hW i) (up_down_pullC F hW i) q (x i)) p⟩

end GlobalTheory.CompanionTheory.CechFull
