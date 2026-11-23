import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

namespace Sep
open GlobalTheory.ZH

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

structure Tower (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) where

  X₂ : Setup F W i

  act₂ : Matrix (Fin 8) (Fin 8) ℤ → (X₂.ρ.P.A ⟶ X₂.ρ.P.A)
  isAct : IsAct X₂ act₂
  [alg : Algebra X₁.Ω₁ X₂.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X₂.Ω₁
  gal : IsGalois X₁.Ω₁ X₂.Ω₁
  deg : ∃ e, Module.finrank X₁.Ω₁ X₂.Ω₁ = X₁.ρ.n ^ e

  d : ℕ
  lev : X₂.S.r * X₂.S.N = X₁.S.r * X₁.S.N * d

  om : X₁.S.R →+* X₂.S.R
  om_eq : ∀ a, (om a : X₂.Ω₁) = algebraMap X₁.Ω₁ X₂.Ω₁ a
  om_fin : om.Finite

  sR : (X₂.Ω₁ ≃ₐ[X₁.Ω₁] X₂.Ω₁) → (X₂.S.R →+* X₂.S.R)
  sR_eq : ∀ σ a, (sR σ a : X₂.Ω₁) = σ a

  p : X₂.M.Z ⟶ X₁.M.Z
  p_fin : IsFinite p
  p_pt : X₂.M.pt ≫ p = spMap (algebraMap X₁.Ω₁ X₂.Ω₁) ≫ X₁.M.pt
  p_π : p ≫ X₁.π = X₂.π

  φ : X₂.ρ.P.A.left ⟶ X₁.ρ.P.A.left
  cart : IsGrpPullback X₂.ρ.P.A X₁.ρ.P.A (spMap om) φ
  lb : LBIso X₂.ρ.P.L (X₁.ρ.P.L.pull φ)
  act_eq : ∀ a, (act₂ a).left ≫ φ = φ ≫ (act a).left

  lam : X₁.S.Gam →+ X₂.S.Gam
  lam_pt : ∀ a, (X₂.ρ.pt (lam a)).left ≫ φ = spMap om ≫ (X₁.ρ.pt a).left
  lam_range : ∀ a', ∃ a, lam a = d • a'

  gl : (X₂.Ω₁ ≃ₐ[X₁.Ω₁] X₂.Ω₁) → (X₂.S.Gam →+ X₂.S.Gam)
  gl_pt : ∀ σ a, (X₂.ρ.pt (gl σ a)).left ≫ φ = spMap (sR σ) ≫ (X₂.ρ.pt a).left ≫ φ
  gl_lam : ∀ σ a, gl σ (lam a) = lam a

attribute [instance] Tower.alg

def Tower.Ext {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z}
    {z₂ : 𝔗.X₂.M.Z} {V V' : Type} [CommRing V] [CommRing V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') : Prop :=
  IsLocalHom ev₂ ∧ ∀ x x₂, 𝔗.X₂.M.stalkHom z₂ x₂ = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) → ev₂ x₂ = io (ev x)

def Tower.self (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (h : IsAct X₁ act) : Tower X₁ act where
  X₂ := X₁
  act₂ := act
  isAct := h
  alg := Algebra.id _
  fd := inferInstance
  gal := inferInstance
  deg := ⟨0, by simp⟩
  d := 1
  lev := by simp
  om := RingHom.id _
  om_eq _ := rfl
  om_fin := RingHom.Finite.id _
  sR _ := RingHom.id _
  sR_eq σ a := (σ.commutes a).symm
  p := 𝟙 _
  p_fin := inferInstance
  p_pt := by
    rw [show spMap (algebraMap X₁.Ω₁ X₁.Ω₁) = 𝟙 _ from Spec.map_id _]; simp
  p_π := Category.id_comp _
  φ := 𝟙 _
  cart := by rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact Wit.grpPullback_id _
  lb := ⟨Wit.idPull _, Wit.idPull_isGen X₁.ρ.P.isLB⟩
  act_eq _ := by simp
  lam := AddMonoidHom.id _
  lam_pt a := by
    rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  lam_range a := ⟨a, by simp⟩
  gl _ := AddMonoidHom.id _
  gl_pt σ a := by
    rw [show spMap (RingHom.id X₁.S.R) = 𝟙 _ from Spec.map_id _]; exact (Category.id_comp _).symm
  gl_lam _ _ := rfl

end Sep

end GlobalTheory.Poinc
