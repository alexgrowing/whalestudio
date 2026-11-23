import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

section Linear

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {H : Type*} [AddCommGroup H] [Module K H] [Module R H]
  [IsScalarTower R K H]

def IsAdapted (β : LinearMap.BilinForm K H) (F : Submodule K H) (N Λ : Submodule R H) : Prop :=
  Λ ⊓ F.restrictScalars R = N ∧ Λ ⊔ F.restrictScalars R = β.dualSubmodule N

def IsLagr (β : LinearMap.BilinForm K H) (F : Submodule K H) : Prop := ∀ s, s ∈ F ↔ ∀ w ∈ F, β s w = 0

end Linear

section Sheaf

variable {O : Type} [CommRing O] {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T}

def toFn (r : K) : Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv r

def resSec (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) (A : X.Modules) (t : Γ((Scheme.Modules.pullback f).obj A, ⊤)) :
    Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤) :=
  ((sqIso w).hom.app A).app ⊤ (QCoh.pullbackSections (spMap (algebraMap R K)) _ (V := ⊤) le_top t)

variable (R) in

def InLat {M : (Sp K).Modules} {n : ℕ} (e : Fin n → Γ(M, ⊤)) (s : Γ(M, ⊤)) : Prop :=
  ∃ r : Fin n → R, s = ∑ i, toFn (algebraMap R K (r i)) • e i

variable (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {A B A' B' : X.Modules} {D : T.Modules}
  (a : (Scheme.Modules.pullback f₀).obj A ⟶ D) (b : D ⟶ (Scheme.Modules.pullback f₀).obj B)

def LatSeq (L : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) → Prop) : Prop :=
  (∀ s, (L s ∧ ((Scheme.Modules.pullback ξ).map b).app ⊤ s = 0) ↔
      ∃ t, s = ((Scheme.Modules.pullback ξ).map a).app ⊤ (resSec w A t)) ∧
    ∀ t', (∃ s, L s ∧ ((Scheme.Modules.pullback ξ).map b).app ⊤ s = t') ↔ ∃ t, t' = resSec w B t

def Reads {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    (E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H) (β : LinearMap.BilinForm K H) (F : Submodule K H)
    (N : Submodule R H) : Prop :=
  (∀ s, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = 0 ↔ E s ∈ F) ∧
    (∀ s, E s ∈ N ↔ ∃ t, s = ((Scheme.Modules.pullback ξ).map a).app ⊤ (resSec w A t)) ∧
    (∀ s, E s ∈ β.dualSubmodule N ↔ ∃ t, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = resSec w B t) ∧
    Function.Surjective (((Scheme.Modules.pullback ξ).map b).app ⊤)

variable {w a b} in

theorem Reads.latSeq {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    {E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H} {β : LinearMap.BilinForm K H} {F : Submodule K H}
    {N Λ : Submodule R H} (h : Reads w a b E β F N) (h' : IsAdapted β F N Λ) : LatSeq w a b fun s => E s ∈ Λ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨fun s => ?_, fun t' => ⟨?_, ?_⟩⟩
  · rw [← h₂, h₁, ← h'.1]; rfl
  · rintro ⟨s, hs, rfl⟩
    exact (h₃ s).1 (h'.2 ▸ Submodule.mem_sup_left hs)
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := h₄ (resSec w B t)
    obtain ⟨x, hx, y, hy, e⟩ := Submodule.mem_sup.1 (h'.2.ge ((h₃ s).2 ⟨t, hs⟩))
    refine ⟨E.symm x, by simpa using hx, ?_⟩
    have e' : s = E.symm x + E.symm y := by rw [← map_add, e, E.symm_apply_apply]
    rw [← hs, e', map_add, (h₁ (E.symm y)).2 (by simpa using hy), add_zero]

variable {α : O →+* End A} {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {r : ℕ}

def HasLattice (d : DatumOn α β α' β' r f₀) : Prop :=
  ∃ (n : ℕ) (e : Fin n → Γ((Scheme.Modules.pullback ξ).obj d.D, ⊤)),
    (∀ x s, InLat R e s → InLat R e ((act (pullAct d.ρ ξ) x).app ⊤ s)) ∧
      LatSeq w d.a d.b (InLat R e) ∧ LatSeq w d.u d.v (InLat R e)

def HasLatticesDvr (d : DatumOn α β α' β' r f₀) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (f : Sp R ⟶ X) (ξ : Sp K ⟶ T)
    (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀), HasLattice w d

def HasLatticesComplete (d : DatumOn α β α' β' r f₀) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (f : Sp R ⟶ X) (ξ : Sp K ⟶ T)
    (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀), HasLattice w d

end Sheaf

section Forms

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

def intForms (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left)
    [Module R (primDR A)] [IsScalarTower R K (primDR A)] : Submodule R (primDR A) where
  carrier := {c | c ∈ PrimitiveSubmodule A ∧ ∀ (v : epsR R ⟶ G) (v' : epsR K ⟶ A) (h : HdR A), IsTangent v →
    v'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) ≫ v.left → IsLieImage h v' →
    h c ∈ (1 : Submodule R K)}
  zero_mem' := ⟨zero_mem _, fun _ _ h _ _ _ => by rw [map_zero]; exact zero_mem _⟩
  add_mem' {x y} hx hy := ⟨add_mem hx.1 hy.1, fun v v' h a b c => by
    rw [map_add]; exact add_mem (hx.2 v v' h a b c) (hy.2 v v' h a b c)⟩
  smul_mem' r x hx := by
    rw [← algebraMap_smul K r x]
    refine ⟨Submodule.smul_mem _ _ hx.1, fun v v' h a b c => ?_⟩
    rw [map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hx.2 v v' h a b c)

end Forms

section Tower

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

structure FinTower (Γ : PDivGroup p R) (G : Over (Sp R)) [GrpObj G] : Type where

  y : ∀ n, SpAlg R (Γ.A n) ⟶ G

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : WithConv (Γ.A n →ₐ[R] B)),
    spOver (φ * ψ).ofConv ≫ y n = (spOver φ.ofConv ≫ y n) * (spOver ψ.ofConv ≫ y n)

  inj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : Γ.A n →ₐ[R] B),
    spOver φ ≫ y n = spOver ψ ≫ y n → φ = ψ

  surj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (z : SpAlg R B ⟶ G),
    z ^ p ^ n = 1 → ∃ φ : Γ.A n →ₐ[R] B, spOver φ ≫ y n = z

  res : ∀ n, spOver (Γ.res n : Γ.A (n + 1) →ₐ[R] Γ.A n) ≫ y (n + 1) = y n

def FinTower.ofTower {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G] (t : Γ.TorsionTower G) : FinTower Γ G :=
  ⟨t.y, t.mul, t.inj, fun n B _ _ _ => t.surj n B, t.res⟩

example [Fact p.Prime] : FinTower (mu p R) (Gm (Sp R)) := .ofTower (muTower p R)

def FinTower.IsIncl {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G] (s : FinTower Γ G) {𝒜 : PDivGroup p K}
    {A : Over (Sp K)} [GrpObj A] (t : 𝒜.TorsionTower A) (φ : A.left ⟶ G.left) (κ : Γ.baseChange K ⟶ 𝒜) : Prop :=
  ∀ n, spMap (κ.app n : 𝒜.A n →+* (Γ.baseChange K).A n) ≫ (t.y n).left ≫ φ =
    spMap ((Γ.toBase K).app n).toRingHom ≫ (s.y n).left

def IsWeilHom {𝒜 ℬ : PDivGroup p R} {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (t : 𝒜.TorsionTower A)
    (u : ℬ.TorsionTower B) (P : LB (A ⊗ B).left) (w : 𝒜 ⟶ ℬ.dual) : Prop :=
  ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ,
    Out.WeilIs (A ⊗ B) P ((p ^ n : ℕ) : ℤ) (T := SpAlg R (𝒜.A n ⊗[R] ℬ.A n))
      (CartesianMonoidalCategory.lift (spOver Algebra.TensorProduct.includeLeft ≫ t.y n) 1)
      (CartesianMonoidalCategory.lift 1 (spOver Algebra.TensorProduct.includeRight ≫ u.y n)) (unitOn U) ∧
    ∀ χ : CartierDual R (ℬ.A n), w.app n χ = TensorProduct.rid R _ (χ.ofConv.lTensor _ U.val)

variable [Fact p.Prime] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

def weilProj (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) : 𝒜 ⟶ Γ.dual.baseChange K :=
  w ≫ dualHom _ _ κ ≫ (PerfdLat.dualBaseChange K Γ).hom

variable [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

def latOmega (κ : Γ.baseChange K ⟶ 𝒜) : Submodule R 𝒜.RigExt where
  carrier := {x | ∃ (w : 𝒜.omega) (w₀ : Γ.omega), x = 𝒜.rigOfOmega w ∧ omegaMap _ _ κ w = (Γ.toBase K).omega w₀}
  zero_mem' := ⟨0, 0, (map_zero _).symm, by rw [map_zero, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨w, w₀, rfl, h⟩ ⟨w', w₀', rfl, h'⟩
    exact ⟨w + w', w₀ + w₀', (map_add _ _ _).symm, by rw [map_add, map_add, h, h']⟩
  smul_mem' := by
    rintro r _ ⟨w, w₀, rfl, h⟩
    exact ⟨algebraMap R K r • w, r • w₀, by rw [map_smul, algebraMap_smul], by rw [map_smul, map_smulₛₗ, h]⟩

def latExt {Δ : PDivGroup p R} (π : 𝒜 ⟶ Δ.baseChange K) : Submodule R 𝒜.RigExt where
  carrier := {x | ∃ y : Δ.RigExt, x = rigExtMap π ((Δ.toBase K).rig y)}
  zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    exact ⟨y + y', by rw [map_add, map_add]⟩
  smul_mem' := by
    rintro r _ ⟨y, rfl⟩
    exact ⟨r • y, by rw [map_smulₛₗ, map_smul, algebraMap_smul]⟩

def lattice (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) : Submodule R 𝒜.RigExt :=
  latOmega κ ⊔ latExt (weilProj κ w)

end Tower

end GlobalTheory.BadPt
