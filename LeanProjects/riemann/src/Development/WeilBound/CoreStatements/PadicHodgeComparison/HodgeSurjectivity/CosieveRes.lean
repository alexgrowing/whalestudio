import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory

universe w w' v u

namespace CrystallineSemistableComparison.Onto

open Pb

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

structure PM (R : Type) [CommRing R] (ι : Type) : Type (w + 1) where
  M : Finset ι → Type w
  [ab : ∀ S, AddCommGroup (M S)]
  [md : ∀ S, Module R (M S)]
  res : ∀ {S T : Finset ι}, S ⊆ T → (M S →ₗ[R] M T)
  res_id : ∀ (S : Finset ι) (h : S ⊆ S) x, res h x = x
  res_comp : ∀ {S T U : Finset ι} (h : S ⊆ T) (h' : T ⊆ U) x, res h' (res h x) = res (h.trans h') x

attribute [instance] PM.ab PM.md

def ent {n : ℕ} (i : Fin n → ι) : Finset ι := Finset.univ.image i

theorem ent_comp {m n : ℕ} (i : Fin n → ι) (θ : Fin m → Fin n) : ent (i ∘ θ) ⊆ ent i := fun x hx => by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

abbrev PM.cech (P : PM.{w} R ι) : Cos.{w} R where
  X n := ∀ i : Fin (n + 1) → ι, P.M (ent i)
  δ n k := LinearMap.pi fun i => (P.res (ent_comp i k.succAbove)).comp (LinearMap.proj (i ∘ k.succAbove))
  rel n j i x := by
    funext t
    have e : (t ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove = (t ∘ j.succAbove) ∘ i.succAbove :=
      funext fun k => congrArg t (Fin.succAbove_succAbove_succAbove_predAbove j i k)
    have key : ∀ (b b' : Fin (n + 1) → ι) (hb : b = b') (h1 : ent b ⊆ ent t) (h2 : ent b' ⊆ ent t),
        P.res h1 (x b) = P.res h2 (x b') := by
      intro b b' hb h1 h2
      subst hb
      rfl
    change P.res _ (P.res _ (x _)) = P.res _ (P.res _ (x _))
    rw [P.res_comp, P.res_comp]
    exact key _ _ e _ _

def PM.aug (P : PM.{w} R ι) : P.M ∅ →ₗ[R] P.cech.X 0 := LinearMap.pi fun i => P.res (Finset.empty_subset _)

def PM.Ex (P : PM.{w} R ι) : Prop := P.cech.cx.ResUpTo 1 P.aug

structure Sy (R : Type) [CommRing R] (ι : Type) : Type (w + 1) where
  K : Finset ι → Cx.{w} R
  res : ∀ {S T : Finset ι}, S ⊆ T → Cx.Hom (K S) (K T) (RingHom.id R)
  res_id : ∀ (S : Finset ι) (h : S ⊆ S) n x, (res h).f n x = x
  res_comp : ∀ {S T U : Finset ι} (h : S ⊆ T) (h' : T ⊆ U) n x, (res h').f n ((res h).f n x) = (res (h.trans h')).f n x

abbrev Sy.term (A : Sy.{w} R ι) (n : ℕ) : PM.{w} R ι where
  M S := (A.K S).X n
  res h := (A.res h).f n
  res_id S h := A.res_id S h n
  res_comp h h' := A.res_comp h h' n

abbrev Sy.coh (A : Sy.{w} R ι) (n : ℕ) : PM.{w} R ι where
  M S := (A.K S).H n
  res h := (A.res h).mapH n
  res_id S h x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (A.res_id S h n z.1))
  res_comp h h' x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (A.res_comp h h' n z.1))

def Sy.Desc (A : Sy.{w} R ι) : Prop := ∀ n, (A.term n).Ex

def Sy.One (A : Sy.{w} R ι) (a : ℕ) : Prop := ∀ S : Finset ι, S.Nonempty → ∀ j, j ≠ a → Subsingleton ((A.K S).H j)

structure Sy.Hom (A : Sy.{w} R ι) (B : Sy.{w'} R ι) where
  φ : ∀ S, Cx.Hom (A.K S) (B.K S) (RingHom.id R)
  nat : ∀ {S T : Finset ι} (h : S ⊆ T) n x, (φ T).f n ((A.res h).f n x) = (B.res h).f n ((φ S).f n x)

def MVBij : Prop := ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (A B : Sy.{1} R ι) (m : A.Hom B), A.Desc → B.Desc →
  (∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) → ∀ n, Function.Bijective ((m.φ ∅).mapH n)

def OneRes : Prop := ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (A : Sy.{1} R ι) (a : ℕ), A.Desc → A.One a →
  (A.coh a).cech.cx.ResUpTo 1 (LinearMap.ker ((A.coh a).cech.d 0)).subtype →
  (∀ j, j ≠ a → Subsingleton ((A.K ∅).H j)) ∧ (A.coh a).Ex

def OneLow : Prop := ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (A : Sy.{1} R ι) (a : ℕ), A.Desc → A.One a →
  (∀ j < a, Subsingleton ((A.K ∅).H j)) ∧ Function.Injective (A.coh a).aug ∧ Function.Exact (A.coh a).aug ((A.coh a).cech.d 0)

def OneSurj : Prop := ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (A B : Sy.{1} R ι) (m : A.Hom B) (a : ℕ), A.Desc → B.Desc →
  A.One a → B.One a → ∀ σ : ∀ S : Finset ι, S.Nonempty → ((B.K S).H a →ₗ[R] (A.K S).H a),
  (∀ S hS x, (m.φ S).mapH a (σ S hS x) = x) →
  (∀ {S T : Finset ι} (h : S ⊆ T) hS hT x, σ T hT ((B.res h).mapH a x) = (A.res h).mapH a (σ S hS x)) →
  ∀ n, Function.Surjective ((m.φ ∅).mapH n)

section Rel

variable {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

def relS (Q : ObjectProperty C) (n : ℕ) : Submodule R (CH.Cn F n) where
  carrier := {z | ∀ s : ComposableArrows C n, Q (s.obj 0) → z s = 0}
  add_mem' hx hy s hs := by rw [Pi.add_apply, hx s hs, hy s hs, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r _ hx s hs := by rw [Pi.smul_apply, hx s hs, smul_zero]

theorem d_mem_relS {Q : ObjectProperty C} (hQ : Cosieve Q) (n : ℕ) (z : CH.Cn F n) (hz : z ∈ relS F Q n) :
    CH.d F n z ∈ relS F Q (n + 1) := fun s hs => by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (GlobalTheory.CatH.toLast i s)).hom (z (GlobalTheory.CatH.face i s)) = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hz _ (hQ (s.map (homOfLE (Fin.zero_le _))) hs), map_zero, smul_zero]

theorem cosieve_res {Q : ObjectProperty C} (hQ : Cosieve Q) (U : ObjectProperty C) :
    Cosieve (fun T : U.FullSubcategory => Q T.obj) := fun _ _ φ h => hQ φ.hom h

abbrev RC (U : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q) : Cx.{max u v w} R :=
  (CH.cx (U.ι ⋙ F)).sub (relS (U.ι ⋙ F) fun T => Q T.obj) (d_mem_relS _ (cosieve_res hQ U))

def RC.res {U V Q : ObjectProperty C} (hQ : Cosieve Q) (h : V ≤ U) : Cx.Hom (RC F U hQ) (RC F V hQ) (RingHom.id R) where
  f n := ((resU F h).pullC n).restrict fun z hz s hs => hz _ hs
  comm n x := Subtype.ext ((resU F h).d_pullC n x.1)

def capU (U : ι → ObjectProperty C) (S : Finset ι) : ObjectProperty C := fun T => (∃ α, U α T) ∧ ∀ α ∈ S, U α T

def covSy (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q) : Sy.{max u v w} R ι where
  K S := RC F (capU U S) hQ
  res h := RC.res F hQ fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩
  res_id _ _ _ _ := rfl
  res_comp _ _ _ _ := rfl

end Rel

def CovDesc : Prop := ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (C : Type 1) [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
  (U : ι → ObjectProperty C) (Q : ObjectProperty C) (hQ : Cosieve Q), (∀ α, Cosieve (U α)) → (covSy F U hQ).Desc

end CrystallineSemistableComparison.Onto

end
