import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

abbrev CFn (Xo : Moduli D l) (c : Coeff l) : Type := ∀ y : Sp ℂ ⟶ Xo.XF c, Vecs y D.p → Vecs y D.q → ℂ

variable {Xo : Moduli D l} {c : Coeff l}

def IsFlatAn (U : Set (Xo.XF c)) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) {σK : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty) (i : Fin FU.n)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) : Prop :=
  ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ)
    (Fm B : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ),
    IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed U τ σ y v w →
    (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
    (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
    (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = V a) →
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, B j n • W j) →
    (∀ j n, ∑ m, Fm j m * τ' (sesq (FU.Di i) (e m) (e n)) = B j n) →
    Φ y v w * (Matrix.fromRows C Fm).det = ρ

structure IsUnitAn (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) : Prop where

  ne : ∀ y v w, IsFramed Set.univ τ σ y v w → Φ y v w ≠ 0

  chg : ∀ y v w v' w' (A : Matrix (Fin D.p) (Fin D.p) ℂ) (B : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsFramed Set.univ τ σ y v' w' →
    (∀ i, IsComb (A i) v (v' i)) → (∀ j, IsComb (B j) w (w' j)) → Φ y v' w' * A.det = Φ y v w * B.det

  norm : ∀ y v w (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ →
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖Δ.det‖

  hol : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G))
    (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ))
    (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B →
    (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) →
    (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧
      (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧
      ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) →
    DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B

def ExtendsUnitAt {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} (s : X ⟶ Sp K) (σ : K →+* ℂ) (ξ : Sp Ω ⟶ X)
    (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (t : Ω) (x : Sp ℂ ⟶ X) : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y →
    (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x →
    ∃ (ε : ℝ) (h : (Fin m → ℂ) → ℂ), 0 < ε ∧ DifferentiableOn ℂ h (Metric.ball b₀ ε) ∧ h b₀ ≠ 0 ∧
      ∀ b ∈ B ∩ Metric.ball b₀ ε, ⊤ ≤ y b ⁻¹ᵁ W → ∀ r : ℂ, ValAt ξ (y b) t r → F (y b) = h b * r

variable {O : Type} [CommRing O] {β : O →+* c.F}

def SameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (v : epsAt (under y) ⟶ Xo.univ.t.G)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : Prop :=
  ∃ u : Sp (DualNumber F) ⟶ Y.oF.t.G.left, u ≫ Y.oF.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y ∧
    u ≫ Y.m0.toSABMap.φ = v.left ∧ u ≫ Y.m.φ = v'.left

theorem exists_sameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v : epsAt (under y) ⟶ Xo.univ.t.G) : ∃ v', SameVec Y y v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv : v.left ≫ Xo.univ.t.G.hom = (spMap (algebraMap F (DualNumber F)) ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact Over.w v
  refine ⟨Over.homMk (hp.lift _ _ hv ≫ Y.m.φ) ?_, hp.lift _ _ hv, hp.lift_snd _ _ _, hp.lift_fst _ _ _, rfl⟩
  have : (hp.lift _ _ hv ≫ Y.m.φ) ≫ Y.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y ≫ Y.j := by
    rw [Category.assoc, hq.w, ← Category.assoc, hp.lift_snd, Category.assoc]
  exact this

theorem exists_sameVec_left (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : ∃ v, SameVec Y y v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv : v'.left ≫ Y.t.G.hom = (spMap (algebraMap F (DualNumber F)) ≫ y) ≫ Y.j := by
    rw [Category.assoc]; exact Over.w v'
  refine ⟨Over.homMk (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ?_, hq.lift _ _ hv, hq.lift_snd _ _ _, rfl,
    hq.lift_fst _ _ _⟩
  have : (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom =
      spMap (algebraMap F (DualNumber F)) ≫ y ≫ pullback.fst _ _ := by
    rw [Category.assoc, hp.w, ← Category.assoc, hq.lift_snd, Category.assoc]
  exact this

theorem SameVec.unique {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v₁ v₂ : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v v₁) (h₂ : SameVec Y y v v₂) : v₁ = v₂ := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hp.hom_ext (b₁.trans b₂.symm) (a₁.trans a₂.symm)
  ext1
  rw [← c₁, ← c₂, this]

theorem SameVec.unique_left {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v₁ v₂ : epsAt (under y) ⟶ Xo.univ.t.G} {v' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v₁ v') (h₂ : SameVec Y y v₂ v') : v₁ = v₂ := by
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hq.hom_ext (c₁.trans c₂.symm) (a₁.trans a₂.symm)
  ext1
  rw [← b₁, ← b₂, this]

theorem sameVec_iff_of_mono (Y : Model Xo c β) [Mono Y.j] {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) :
    SameVec Y y v v' ↔
      ∃ u : Sp (DualNumber F) ⟶ Y.oF.t.G.left, u ≫ Y.m0.toSABMap.φ = v.left ∧ u ≫ Y.m.φ = v'.left := by
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  refine ⟨fun ⟨u, _, a, b⟩ => ⟨u, a, b⟩, fun ⟨u, a, b⟩ => ⟨u, ?_, a, b⟩⟩
  rw [← cancel_mono Y.j, Category.assoc, ← hq.w, ← Category.assoc, b, Category.assoc]
  exact Over.w v'

def Represents (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ Y.X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel Y.t.G ξ V) (a : ⋀[Ω]^D.p V) (b : ⋀[Ω]^D.q V)
    (φ : FrameFn Xo c) : Prop :=
  ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (b₁ : Fin D.p → V) (b₂ : Fin D.q → V) (α κ : Ω), IsFramed U τ βF y v w →
    a = α • exteriorPower.ιMulti Ω D.p b₁ → b = κ • exteriorPower.ιMulti Ω D.q b₂ →
    (∀ i, ∃ v', M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') →
    (∀ j, ∃ w', M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') →
    ValAt ξ (y ≫ Y.j) (α / κ) (φ F y v w)

structure CptOver (Y : Model Xo c β) (U : Set (Xo.XF c)) where

  Ω : Type
  [field : Field Ω]

  ξ₀ : Sp Ω ⟶ Xo.XF c

  inc : c.F →+* Ω

  over_inc : ξ₀ ≫ pullback.snd _ _ = spMap inc

  gen : IsCptGen (ξ₀ ≫ Y.j)

  closure : ∀ u : Xo.XF c, u ∈ U ↔ genPt ξ₀ ⤳ u

  V : Type
  [acg : AddCommGroup V]
  [mod : Module Ω V]

  M : LieModel Y.t.G (ξ₀ ≫ Y.j) V

  ρ : 𝓞 E →+* Module.End Ω V

  act : M.IsActOf Y.t.act.act ρ

attribute [instance] CptOver.field CptOver.acg CptOver.mod

def CptOver.eig {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) : Lat (Z.ξ₀ ≫ Y.j) Z.V :=
  Z.M.eigLat Z.ρ (Z.inc.comp (tauIn c τ))

def CptOver.genFib {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Set (Cpt (Z.ξ₀ ≫ Y.j)) :=
  {x | x.1 ∈ Set.range (pullback.fst Y.s (spMap β))}

def FlatOnModel {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) : Prop :=
  IsLineFn U τ φ ∧ ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧ Represents Y U τ Z.M a b φ

theorem FlatOnModel.isLineFn {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : IsLineFn U τ φ := h.1

theorem FlatOnModel.exists_gen {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧
      Represents Y U τ Z.M a b φ := h.2

theorem FlatOnModel.of_gen {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} {a : ⋀[Z.Ω]^D.p Z.V} {b : ⋀[Z.Ω]^D.q Z.V} (hφ : IsLineFn U τ φ)
    (hg : IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib)
    (hr : Represents Y U τ Z.M a b φ) : FlatOnModel Z τ φ := ⟨hφ, a, b, hg, hr⟩

theorem CptOver.genPt_mem {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : genPt Z.ξ₀ ∈ U :=
  (Z.closure _).2 specializes_rfl

def CptOver.IsGeom {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Prop :=
  ∀ x : Z.Ω, (∃ f : Polynomial c.F, f ≠ 0 ∧ f.eval₂ Z.inc x = 0) → x ∈ Set.range Z.inc

theorem isFlatAn_iff_isConstMul (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) :
    IsFlatAn U τ τ (algebraMap c.F ℂ) (φ ℂ) FU i e ρ ↔ IsConstMul U τ φ FU i e ρ := Iff.rfl

theorem IsFlatAn.const_mul {U : Set (Xo.XF c)} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ} {Φ : CFn Xo c} {σK : KA l →+* ℂ}
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo σK ty} {i : Fin FU.n}
    {e : Fin D.p ⊕ Fin D.q → (FU.Di i).La} {ρ : ℂ} (h : IsFlatAn U τ τ' σ Φ FU i e ρ) (k : ℂ) :
    IsFlatAn U τ τ' σ (fun y v w => k * Φ y v w) FU i e (k * ρ) := by
  intro P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8
  show k * Φ y v w * _ = _
  rw [_root_.mul_assoc, h P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8]

theorem IsUnitAn.const_mul {τ : E →+* ℂ} {σ : c.F →+* ℂ} {Φ : CFn Xo c} (h : IsUnitAn τ σ Φ) {k : ℂ}
    (hk : ‖k‖ = 1) : IsUnitAn τ σ (fun y v w => k * Φ y v w) where
  ne y v w hf := mul_ne_zero (by rintro rfl; simp at hk) (h.ne y v w hf)
  chg y v w v' w' A B h1 h2 h3 h4 := by rw [_root_.mul_assoc, _root_.mul_assoc, h.chg y v w v' w' A B h1 h2 h3 h4]
  norm y v w Γ Δ h1 h2 h3 := by rw [norm_mul, hk, _root_.one_mul]; exact h.norm y v w Γ Δ h1 h2 h3
  hol R _ x vR wR m B ψ v w h1 h2 h3 := (h.hol R x vR wR m B ψ v w h1 h2 h3).const_mul k

theorem ExtendsUnitAt.const_mul {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} {s : X ⟶ Sp K} {σ : K →+* ℂ}
    {ξ : Sp Ω ⟶ X} {W : X.Opens} {F : (Sp ℂ ⟶ X) → ℂ} {t : Ω} {x : Sp ℂ ⟶ X}
    (h : ExtendsUnitAt s σ ξ W F t x) {k : ℂ} (hk : k ≠ 0) : ExtendsUnitAt s σ ξ W (fun y => k * F y) t x := by
  intro m B y h1 h2 h3 b₀ h4 h5
  obtain ⟨ε, g, hε, hd, hg, H⟩ := h m B y h1 h2 h3 b₀ h4 h5
  refine ⟨ε, fun b => k * g b, hε, hd.const_mul k, mul_ne_zero hk hg, fun b hb hW r hr => ?_⟩
  show k * F (y b) = k * g b * r
  rw [H b hb hW r hr, _root_.mul_assoc]

theorem ExtendsUnitAt.eq_zero_iff {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} {s : X ⟶ Sp K} {σ : K →+* ℂ}
    {ξ : Sp Ω ⟶ X} {W : X.Opens} {F : (Sp ℂ ⟶ X) → ℂ} {t : Ω} {x : Sp ℂ ⟶ X} (h : ExtendsUnitAt s σ ξ W F t x)
    (hx : x ≫ s = spMap σ) (hW : ⊤ ≤ x ⁻¹ᵁ W) {r : ℂ} (hr : ValAt ξ x t r) : F x = 0 ↔ r = 0 := by
  have hol : IsHolTo (Set.univ : Set (Fin 0 → ℂ)) (fun _ => x) := fun U f =>
    ⟨isOpen_discrete _, differentiableOn_const _⟩
  obtain ⟨ε, g, hε, -, hg, H⟩ := h 0 Set.univ (fun _ => x) isOpen_univ hol (fun _ _ => hx) 0 trivial rfl
  rw [H 0 ⟨trivial, Metric.mem_ball_self hε⟩ hW r hr]
  exact ⟨fun h0 => (mul_eq_zero.mp h0).resolve_left hg, fun h0 => by rw [h0, mul_zero]⟩

theorem CptOver.isGeom_of_surjective {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U)
    (h : Function.Surjective Z.inc) : Z.IsGeom := fun x _ => h x

example {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) {F : Type} [Field F]
    (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (hf : IsFramed U τ βF y v w) :
    ¬ FlatOnModel Z τ (fun _ _ _ _ _ => 0) := fun h => h.isLineFn.ne F βF y v w hf rfl

end GlobalTheory.CompanionTheory.Ar.Flat
