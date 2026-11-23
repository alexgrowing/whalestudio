import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

@[reducible] def Charts.std {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ)
    (Q : Opens (Tot I g) → Prop) : Charts F where
  K := {W : Opens (Tot I g) // (∀ p ∈ W, p.1 ∈ F.V) ∧ Q W}
  W k := k.1
  base k := k.2.1
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

section Fibre

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

@[reducible] def fibFam (u : HolUnif A L g) : Fam Empty g u.Λ where
  V := ⊤
  τ := { toFun x := fun _ ↦ (x : Fin g → ℂ), map_zero' := rfl, map_add' _ _ := rfl }
  hol _ := analyticOnNhd_const

def fibUnif (u : HolUnif A L g) : Unif (fibFam u) (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) where
  E p := (u.ex p.2).left
  w p hp := by
    have e : (Hol.ev p.1 hp).toRingHom.comp (algebraMap ℂ (Hol (fibFam u).V)) = RingHom.id ℂ :=
      RingHom.ext fun c ↦ (Hol.ev p.1 hp).commutes c
    rw [e, Cris.spMap_id, Category.comp_id]
    exact Over.w (u.ex p.2)
  per l p _ := by
    change (u.ex (p.2 + (l : Fin g → ℂ))).left = _
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  hol U f := ⟨by
    have := (u.hol U f).1.preimage (continuous_snd (X := Empty → ℂ))
    convert this using 1
    exact Set.ext fun p ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨trivial, h⟩⟩,
    (u.hol U f).2.comp differentiableOn_snd fun _ h ↦ h.2⟩

def IsPeriodHom (u : HolUnif A L g) (P : u.Λ →+ HdR A) : Prop :=
  ∀ c : primDR A, IsPeriod (fibUnif u) c.1
    { toFun x := algebraMap ℂ (Hol (fibFam u).V) (P x c)
      map_zero' := by rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' x y := by rw [map_add, LinearMap.add_apply, map_add] }

end Fibre

def PExist : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B] (X : Scheme.{0})
    (s : X ⟶ Sp B) [IsSeparated s] (σ : B →+* Hol F.V) (u : Unif F s σ), u.Based → ∀ c : FirstDeRham s, ∃ per, IsPeriod u c per

def PUniq : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B] (X : Scheme.{0})
    (s : X ⟶ Sp B) [IsSeparated s] (σ : B →+* Hol F.V) (u : Unif F s σ) (c : FirstDeRham s) (per per' : Λ →+ Hol F.V),
    IsPeriod u c per → IsPeriod u c per' → per = per'

def PHom : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (L : LB A.left) (u : HolUnif A L g), ∃ P, IsPeriodHom u P

def PLie : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v

def PEnd : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ (α : A ⟶ A) [IsMonHom α] (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w, u.ex (M w) = u.ex w ≫ α) →
      ∀ x x' : u.Λ, (x' : Fin g → ℂ) = M x → push (dp0 ℂ) (𝟙 _) α (P x) = P x'

def PChern (ε : ℤˣ) : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex →
    ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ) (ψ : LinearMap.BilinForm ℂ (HdR A)), u'.IsAH H χ →
      IsPolForm (dp0 ℂ) (𝟙 _) A M ψ → ∀ x x' : u.Λ,
        ψ (P x) (P x') = ((ε : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
          (((x : Fin g → ℂ) ⬝ᵥ H.mulVec (star (x' : Fin g → ℂ))).im : ℂ)

def PSpan : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g

def PFix : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B]
    (𝒜 : Over (Sp B)) [GrpObj 𝒜], IsAbelianScheme 𝒜 → ∀ (σ : B →+* Hol F.V) (e : Unif F (𝒜.hom ≫ 𝟙 _) σ)
    (z : I → ℂ), z ∈ F.V → ∀ (y : B →+* ℂ), (∀ b, y b = (σ b).fn z) →
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (φ : A.left ⟶ 𝒜.left)
      (m : GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 ℂ) (𝟙 _) A y (spMap y) φ) (L : LB A.left) (u : HolUnif A L g),
      (∀ w, e.E (z, w) = (u.ex w).left ≫ φ) → ∀ τ : Λ →+ u.Λ, (∀ l, (τ l : Fin g → ℂ) = F.τ l z) →
    ∀ (P : u.Λ →+ HdR A), IsPeriodHom u P → ∀ (c : primDR 𝒜) (per : Λ →+ Hol F.V), IsPeriod e c.1 per →
      ∀ l, P (τ l) (m.pull c) = (per l).fn z

def PTaylor : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (g : ℕ) (B : Type) [CommRing B] [Algebra ℂ B]
    (𝒜 : Over (Sp B)) [GrpObj 𝒜], IsAbelianScheme 𝒜 → SmoothOfRelativeDimension g 𝒜.hom →
    ∀ (y₀ : B →ₐ[ℂ] ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (φ₀ : A₀.left ⟶ 𝒜.left),
      IsGrpPullback A₀ 𝒜 (spMap (y₀ : B →+* ℂ)) φ₀ → ∀ (L₀ : LB A₀.left) (u₀ : HolUnif A₀ L₀ g)
      (F : Fam I g u₀.Λ) (σ : B →ₐ[ℂ] Hol F.V) (e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V)), 0 ∈ F.V →
      (∀ b, y₀ b = (σ b).fn 0) → (∀ w, e.E (0, w) = (u₀.ex w).left ≫ φ₀) → (∀ x, F.τ x 0 = x) →
    ∀ (P₀ : u₀.Λ →+ HdR A₀), IsPeriodHom u₀ P₀ →
    ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ →
      (∀ a : ℂ, π (algebraMap ℂ D a) = a) →
      ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
      ∀ (j : B →ₐ[ℂ] D), (∀ b, j b = taylor N t (σ b).fn) →
      ∀ (A' : Over (Sp D)) [GrpObj A'] (φ' : A'.left ⟶ 𝒜.left), IsGrpPullback A' 𝒜 (spMap (j : B →+* D)) φ' →
      ∀ (m' : GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 D) (𝟙 _) A' (j : B →+* D) (spMap (j : B →+* D)) φ')
        (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap π) i), i ≫ φ' = φ₀ →
      ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀)))
        (x : u₀.Λ) (d : Crys κ (spMap π) A₀), k.Corr (P₀ x) d → ∀ (c : primDR 𝒜) (per : u₀.Λ →+ Hol F.V),
        IsPeriod e c.1 per → crysToDR κ h d (m'.pull c) = taylor N t (per x).fn

end GlobalTheory.AnPer
