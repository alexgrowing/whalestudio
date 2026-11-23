import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

open Classical in

def base (X₁ : Setup F W i) (z₁ : X₁.M.Z) : X₁.S.Gam :=
  if h : (X₁.S.supI X₁.M z₁).Nonempty then h.some else 0

def wtChar (D : Deep X₁ ε₁) (T : AddSubgroup D.X.S.Gam) (a : D.X.S.Gam) : T →+ ZMod D.X.S.N where
  toFun t := ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a))
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

open Classical in

def lift (D : Deep X₁ ε₁) (z₂ : D.X.M.Z) (κ : X₁.S.Gam) : D.X.S.Gam :=
  if h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ then h.choose else 0

def part (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z) (a : D.X.S.Gam) (κ : X₁.S.HH X₁.M z₁) : D.X.Ω₁ :=
  (∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M z₂) (wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (lift D z₂ (κ : X₁.S.Gam)) j) / D.X.S.th (D.lab (base X₁ z₁))

end GlobalTheory.Poinc.GSum
