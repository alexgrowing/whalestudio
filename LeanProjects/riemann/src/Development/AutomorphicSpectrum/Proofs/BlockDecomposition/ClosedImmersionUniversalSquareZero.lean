import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotLift

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

section Ker

variable {R P : Type} [CommRing R] [CommRing P]

def KerW (_ : R →+* P) (ε : P →+* R) : Type := RingHom.ker ε

variable (α : R →+* P) (ε : P →+* R)

instance : AddCommGroup (KerW α ε) := inferInstanceAs (AddCommGroup (RingHom.ker ε))

instance : Module P (KerW α ε) := inferInstanceAs (Module P (RingHom.ker ε))

instance : Module R (KerW α ε) := Module.compHom _ α

instance : Module Rᵐᵒᵖ (KerW α ε) :=
  Module.compHom _ (RingHom.fromOpposite (RingHom.id R) fun _ _ ↦ Commute.all _ _)

instance : IsCentralScalar R (KerW α ε) := ⟨fun _ _ ↦ rfl⟩

variable {α ε}

def KerW.val (w : KerW α ε) : P := Subtype.val (p := fun x ↦ x ∈ RingHom.ker ε) w

theorem KerW.ext' {v w : KerW α ε} (h : v.val = w.val) : v = w := Subtype.ext h

@[simp] theorem KerW.val_add (v w : KerW α ε) : (v + w).val = v.val + w.val := rfl

@[simp] theorem KerW.val_smul (r : R) (w : KerW α ε) : (r • w).val = α r * w.val := rfl

@[simp] theorem KerW.val_op_smul (r : R) (w : KerW α ε) : (MulOpposite.op r • w).val = α r * w.val := rfl

@[simp] theorem KerW.val_zero : (0 : KerW α ε).val = 0 := rfl

theorem KerW.eps_val (w : KerW α ε) : ε w.val = 0 := w.2

def pr (h : ε.comp α = RingHom.id R) (a : P) : KerW α ε :=
  ⟨a - α (ε a), by
    have e : ε (α (ε a)) = ε a := congrArg (fun f ↦ f (ε a)) h
    simp [RingHom.mem_ker, e]⟩

@[simp] theorem pr_val (h : ε.comp α = RingHom.id R) (a : P) : (pr h a).val = a - α (ε a) := rfl

theorem eps_alpha (h : ε.comp α = RingHom.id R) (r : R) : ε (α r) = r := congrArg (fun f ↦ f r) h

def theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) :
    P →+* TrivSqZeroExt R (KerW α ε) where
  toFun a := TrivSqZeroExt.inl (ε a) + TrivSqZeroExt.inr (pr h a)
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp
  map_zero' := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp; ring
  map_mul' a b := by
    have e := hsq (a - α (ε a)) (b - α (ε b)) (by simp [eps_alpha h]) (by simp [eps_alpha h])
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'
      simp
      linear_combination e

@[simp] theorem theta_fst (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) (a : P) :
    (theta h hsq a).fst = ε a := by simp [theta]

@[simp] theorem theta_snd (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) (a : P) :
    (theta h hsq a).snd = pr h a := by simp [theta]

end Ker

section Main

variable {R P B M : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] {α : R →+* P} {ε : P →+* R}

theorem pr_val_self (h : ε.comp α = RingHom.id R) (w : KerW α ε) : pr h w.val = w :=
  KerW.ext' (by simp [KerW.eps_val])

def uOf (φ : P →+* TrivSqZeroExt B M) (hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B))
    (hf : ∀ a, (φ a).fst = algebraMap R B (ε a)) : KerW α ε →ₗ[R] M where
  toFun w := (φ w.val).snd
  map_add' v w := by simp
  map_smul' r w := by
    have e : φ (α r) = TrivSqZeroExt.inl (algebraMap R B r) := congrArg (fun f ↦ f r) hα
    have z : (φ w.val).fst = 0 := by rw [hf, KerW.eps_val, map_zero]
    simp only [KerW.val_smul, map_mul, e, RingHom.id_apply, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, smul_zero, add_zero, algebraMap_smul]

theorem tsz_theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0)
    (φ : P →+* TrivSqZeroExt B M) (hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B))
    (hf : ∀ a, (φ a).fst = algebraMap R B (ε a)) :
    (tsz (uOf φ hα hf)).comp (theta h hsq) = φ := by
  refine RingHom.ext fun a ↦ ?_
  have e : φ (α (ε a)) = TrivSqZeroExt.inl (algebraMap R B (ε a)) := congrArg (fun f ↦ f (ε a)) hα
  have s : (uOf φ hα hf) (pr h a) = (φ a).snd := by
    change (φ (a - α (ε a))).snd = _
    simp [e]
  apply TrivSqZeroExt.ext
  · change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq a).fst) +
      TrivSqZeroExt.inr ((uOf φ hα hf) (theta h hsq a).snd) : TrivSqZeroExt B M).fst = _
    simp [hf]
  · change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq a).fst) +
      TrivSqZeroExt.inr ((uOf φ hα hf) (theta h hsq a).snd) : TrivSqZeroExt B M).snd = _
    simp [s]

theorem snd_tsz_theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0)
    (u : KerW α ε →ₗ[R] M) (w : KerW α ε) : ((tsz (B := B) u).comp (theta h hsq) w.val).snd = u w := by
  change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq w.val).fst) +
    TrivSqZeroExt.inr (u (theta h hsq w.val).snd) : TrivSqZeroExt B M).snd = _
  simp [pr_val_self]

end Main

theorem isCot_of_lifting : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by
  intro R _ X s e P _ α ε j h hsq hj hje hm hlift
  haveI := hm
  refine ⟨KerW α ε, inferInstance, inferInstance, inferInstance, inferInstance, spMap (theta h hsq) ≫ j, ?_⟩
  unfold IsCot
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (theta h hsq).comp α = TrivSqZeroExt.inlHom R (KerW α ε) := by
      refine RingHom.ext fun r ↦ TrivSqZeroExt.ext ?_ (KerW.ext' ?_)
      · simp [eps_alpha h]
      · simp [eps_alpha h]
    rw [Category.assoc, hj, spMap_comp_spMap, e1]
  · have e1 : (TrivSqZeroExt.fstHom R R (KerW α ε)).toRingHom.comp (theta h hsq) = ε :=
      RingHom.ext fun a ↦ theta_fst h hsq a
    rw [← Category.assoc, spMap_comp_spMap, e1, hje]
  · intro B _ _ M _ _ _ _ _ _ y hy1 hy2
    obtain ⟨φ, hφ⟩ := hlift (TrivSqZeroExt B M) B (TrivSqZeroExt.fstHom B B M).toRingHom (algebraMap R B) y
      (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)
      (fun a b ha hb ↦ by
        have ha' : a.fst = 0 := ha
        have hb' : b.fst = 0 := hb
        apply TrivSqZeroExt.ext <;> simp [ha', hb']) hy2
    have hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := spMap_inj (by
      rw [← spMap_comp_spMap, ← hj, ← Category.assoc, hφ, hy1])
    have hf : (TrivSqZeroExt.fstHom B B M).toRingHom.comp φ = (algebraMap R B).comp ε :=
      spMap_inj ((cancel_mono j).1 (by
        rw [← spMap_comp_spMap, Category.assoc, hφ, hy2, ← spMap_comp_spMap, Category.assoc, hje]))
    have hf' : ∀ a, (φ a).fst = algebraMap R B (ε a) := fun a ↦ congrArg (fun f ↦ f a) hf
    refine ⟨uOf φ hα hf', ?_, ?_⟩
    · change y = spMap (tsz (uOf φ hα hf')) ≫ spMap (theta h hsq) ≫ j
      rw [← Category.assoc, spMap_comp_spMap, tsz_theta, hφ]
    · intro u' hu'
      have e1 : (tsz u').comp (theta h hsq) = φ := spMap_inj ((cancel_mono j).1 (by
        rw [← spMap_comp_spMap, Category.assoc, hφ]
        exact hu'.symm))
      refine LinearMap.ext fun w ↦ ?_
      rw [← snd_tsz_theta (B := B) h hsq u' w, e1]
      rfl

end GlobalTheory.CompanionTheory.CotLift
