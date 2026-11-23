import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Asm

section Tw

variable {G M V W Z : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Z] [Module ℂ Z]

def twHom {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (f : ρ.IntertwiningMap σ) :
    (twAct ρ N θ s hs).IntertwiningMap (twAct σ N θ s hs) where
  toLinearMap := twMap ρ σ N θ f.toLinearMap (fun g v => LinearMap.congr_fun (f.isIntertwining' g) v)
  isIntertwining' m := by
    apply Submodule.linearMap_qext
    ext v
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun (f.isIntertwining' (s m)) v)

theorem twHom_comp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G Z} (N : Subgroup G)
    (θ : N →* ℂˣ) (s : M →* G) (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) (f' : ρ.IntertwiningMap τ) (h : ∀ v, f' v = g (f v))
    (x : TwJacquet ρ N θ) : twHom N θ s hs f' x = twHom N θ s hs g (twHom N θ s hs f x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v => exact congrArg Submodule.Quotient.mk (h v)

theorem twHom_id {ρ : Representation ℂ G V} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : ρ.IntertwiningMap ρ) (h : ∀ v, f v = v) (x : TwJacquet ρ N θ) : twHom N θ s hs f x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => exact congrArg Submodule.Quotient.mk (h v)

theorem twHom_zero {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (f : ρ.IntertwiningMap σ) (h : ∀ v, f v = 0) (x : TwJacquet ρ N θ) : twHom N θ s hs f x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v => exact (congrArg Submodule.Quotient.mk (h v)).trans (Submodule.Quotient.mk_zero _)

end Tw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def phiHom (ψ : AddChar k Circle) {n : ℕ} {τ τ' : MRep k (n + 1)} (f : τ.ρ.IntertwiningMap τ'.ρ) :
    (MRep.phiM k ψ τ).ρ.IntertwiningMap (MRep.phiM k ψ τ').ρ :=
  twHom (MirUin k (n + 1)) (mirChar k ψ n) ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n) f

def iterHom (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → {τ τ' : MRep k (n + j)} → τ.ρ.IntertwiningMap τ'.ρ →
    (iterPhi k ψ j τ).ρ.IntertwiningMap (iterPhi k ψ j τ').ρ
  | 0, _, _, _, f => f
  | j + 1, _, _, _, f => iterHom ψ j (phiHom ψ f)

theorem iterHom_comp (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {τ τ' τ'' : MRep k (n + j)}
    (f : τ.ρ.IntertwiningMap τ'.ρ) (g : τ'.ρ.IntertwiningMap τ''.ρ) (f' : τ.ρ.IntertwiningMap τ''.ρ),
    (∀ v, f' v = g (f v)) → ∀ x, iterHom ψ j f' x = iterHom ψ j g (iterHom ψ j f x)
  | 0, _, _, _, _, _, _, _, h, x => h x
  | j + 1, _, _, _, _, f, g, f', h, x =>
    iterHom_comp ψ j (phiHom ψ f) (phiHom ψ g) (phiHom ψ f') (twHom_comp _ _ _ _ f g f' h) x

theorem iterHom_id (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {τ : MRep k (n + j)}
    (f : τ.ρ.IntertwiningMap τ.ρ), (∀ v, f v = v) → ∀ x, iterHom ψ j f x = x
  | 0, _, _, _, h, x => h x
  | j + 1, _, _, f, h, x => iterHom_id ψ j (phiHom ψ f) (twHom_id _ _ _ _ f h) x

theorem iterHom_zero (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {τ τ' : MRep k (n + j)}
    (f : τ.ρ.IntertwiningMap τ'.ρ), (∀ v, f v = 0) → ∀ x, iterHom ψ j f x = 0
  | 0, _, _, _, _, h, x => h x
  | j + 1, _, _, _, f, h, x => iterHom_zero ψ j (phiHom ψ f) (twHom_zero _ _ _ _ f h) x

def resHom {m : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {π : Representation ℂ (GL (Fin (m + 1)) k) X} {σ : Representation ℂ (GL (Fin (m + 1)) k) Y}
    (f : π.IntertwiningMap σ) : (resM k π).ρ.IntertwiningMap (resM k σ).ρ where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' g

def dHom (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → {A B : GRep k (n + j)} → A.ρ.IntertwiningMap B.ρ →
    (derivB ψ j A).ρ.IntertwiningMap (derivB ψ j B).ρ
  | 0, _, _, _, f => f
  | j + 1, n, _, _, f => twHom (MirUin k n) 1 (levi k n) (levi_normalises n) (iterHom ψ j (resHom f))

theorem dHom_comp (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A B C : GRep k (n + j)}
    (f : A.ρ.IntertwiningMap B.ρ) (g : B.ρ.IntertwiningMap C.ρ) (f' : A.ρ.IntertwiningMap C.ρ),
    (∀ v, f' v = g (f v)) → ∀ x, dHom ψ j f' x = dHom ψ j g (dHom ψ j f x)
  | 0, _, _, _, _, _, _, _, h, x => h x
  | j + 1, _, _, _, _, f, g, f', h, x =>
    twHom_comp _ _ _ _ _ _ _ (iterHom_comp ψ j (resHom f) (resHom g) (resHom f') h) x

theorem dHom_id (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A : GRep k (n + j)}
    (f : A.ρ.IntertwiningMap A.ρ), (∀ v, f v = v) → ∀ x, dHom ψ j f x = x
  | 0, _, _, _, h, x => h x
  | j + 1, _, _, f, h, x => twHom_id _ _ _ _ _ (iterHom_id ψ j (resHom f) h) x

theorem dHom_zero (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A B : GRep k (n + j)}
    (f : A.ρ.IntertwiningMap B.ρ), (∀ v, f v = 0) → ∀ x, dHom ψ j f x = 0
  | 0, _, _, _, _, h, x => h x
  | j + 1, _, _, _, f, h, x => twHom_zero _ _ _ _ _ (iterHom_zero ψ j (resHom f) h) x

section Cast

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cast_cast {a b c : ℕ} (e1 : a = b) (e2 : b = c) (X : GRep k a) :
    (X.cast e1).cast e2 = X.cast (e1.trans e2) := by
  subst e1; subst e2; rfl

def castHom {a b : ℕ} (e : a = b) {X Y : GRep k a} (f : X.ρ.IntertwiningMap Y.ρ) :
    (X.cast e).ρ.IntertwiningMap (Y.cast e).ρ := by
  subst e; exact f

theorem castHom_comp {a b : ℕ} (e : a = b) {X Y Z : GRep k a} (f : X.ρ.IntertwiningMap Y.ρ)
    (g : Y.ρ.IntertwiningMap Z.ρ) (f' : X.ρ.IntertwiningMap Z.ρ) (h : ∀ v, f' v = g (f v)) :
    ∀ v, castHom e f' v = castHom e g (castHom e f v) := by
  subst e; exact h

theorem castHom_id {a b : ℕ} (e : a = b) {X : GRep k a} (f : X.ρ.IntertwiningMap X.ρ) (h : ∀ v, f v = v) :
    ∀ v, castHom e f v = v := by
  subst e; exact h

theorem castHom_zero {a b : ℕ} (e : a = b) {X Y : GRep k a} (f : X.ρ.IntertwiningMap Y.ρ) (h : ∀ v, f v = 0) :
    ∀ v, castHom e f v = 0 := by
  subst e; exact h

theorem isSmooth_cast {a b : ℕ} (e : a = b) (X : GRep k a) : IsSmooth (X.cast e).ρ ↔ IsSmooth X.ρ := by
  subst e; rfl

theorem isIrreducible_cast {a b : ℕ} (e : a = b) (X : GRep k a) :
    (X.cast e).ρ.IsIrreducible ↔ X.ρ.IsIrreducible := by
  subst e; rfl

theorem isUnitarisable_cast {a b : ℕ} (e : a = b) (X : GRep k a) :
    IsUnitarisable (X.cast e).ρ ↔ IsUnitarisable X.ρ := by
  subst e; rfl

def DM (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y : GRep k N} (f : X.ρ.IntertwiningMap Y.ρ) :
    (derivB ψ j (X.cast e)).ρ.IntertwiningMap (derivB ψ j (Y.cast e)).ρ :=
  dHom ψ j (castHom e f)

theorem DM_comp (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y Z : GRep k N}
    (f : X.ρ.IntertwiningMap Y.ρ) (g : Y.ρ.IntertwiningMap Z.ρ) (f' : X.ρ.IntertwiningMap Z.ρ)
    (h : ∀ v, f' v = g (f v)) (x : (derivB ψ j (X.cast e)).V) : DM ψ j e f' x = DM ψ j e g (DM ψ j e f x) :=
  dHom_comp ψ j _ _ _ (castHom_comp e f g f' h) x

theorem DM_id (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X : GRep k N}
    (f : X.ρ.IntertwiningMap X.ρ) (h : ∀ v, f v = v) (x : (derivB ψ j (X.cast e)).V) : DM ψ j e f x = x :=
  dHom_id ψ j _ (castHom_id e f h) x

theorem DM_zero (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y : GRep k N}
    (f : X.ρ.IntertwiningMap Y.ρ) (h : ∀ v, f v = 0) (x : (derivB ψ j (X.cast e)).V) : DM ψ j e f x = 0 :=
  dHom_zero ψ j _ (castHom_zero e f h) x

theorem DM_comm (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X Y : GRep k N}
    (f : X.ρ.IntertwiningMap Y.ρ) (g : GL (Fin n) k) (x : (derivB ψ j (X.cast e)).V) :
    DM ψ j e f ((derivB ψ j (X.cast e)).ρ g x) = (derivB ψ j (Y.cast e)).ρ g (DM ψ j e f x) :=
  LinearMap.congr_fun ((DM ψ j e f).isIntertwining' g) x

def ND (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) (j : ℕ) : Prop :=
  ∃ (n : ℕ) (e : N = n + j), Nontrivial (derivB ψ j (X.cast e)).V

theorem nd_iff (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) {n j : ℕ} (e : N = n + j) :
    ND ψ X j ↔ Nontrivial (derivB ψ j (X.cast e)).V := by
  constructor
  · rintro ⟨n', e', h⟩
    obtain rfl : n' = n := by omega
    exact h
  · exact fun h => ⟨n, e, h⟩

theorem le_of_nd (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) {j : ℕ} (h : ND ψ X j) : j ≤ N := by
  obtain ⟨n, e, _⟩ := h
  omega

theorem isTopD_iff (ψ : AddChar k Circle) {N n h : ℕ} (X : GRep k N) (e : N = n + h) :
    Prod.IsTopD ψ (X.cast e) ↔ ND ψ X h ∧ ∀ h', h < h' → ¬ ND ψ X h' := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(nd_iff ψ X e).2 h1, fun h' hlt hnd => ?_⟩
    obtain ⟨n', e', hnt⟩ := hnd
    have hs := h2 n' h' (e.symm.trans e') hlt
    rw [cast_cast] at hs
    exact not_subsingleton _ hs
  · rintro ⟨h1, h2⟩
    refine ⟨(nd_iff ψ X e).1 h1, fun n' h' e' hlt => ?_⟩
    rw [cast_cast]
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact h2 h' hlt ⟨n', _, hns⟩

def subG {N : ℕ} {X : GRep k N} (S : Subrepresentation X.ρ) : GRep k N := ⟨S.toSubmodule, S.toRepresentation⟩

end Cast

end PositivityTheory.RgUd.Prod.Asm
