import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.BridgeEx

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

open Loc Glob

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

variable (L) in

structure Pre where
  Δ : Lp L
  e : Lsq (Lp L) Δ ≃+* L
  e_star : ∀ x, e (star x) = IsCMField.complexConj L (e x)
  e_alg : ∀ a : Lp L, e (algebraMap _ _ a) = algebraMap (Lp L) L a
  φ : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → Kv v →+* Kw w
  φ_cont : ∀ v w h, Continuous (φ v w h)
  φ_alg : ∀ v w h (a : Lp L), φ v w h (cv v a) = algebraMap L (Kw w) (algebraMap (Lp L) L a)

def Pre.rt (P : Pre L) (w : Plc L) : Kw w := algebraMap L (Kw w) (P.e QuadraticAlgebra.omega)

theorem Pre.rt_sq (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v) : P.rt w * P.rt w = P.φ v w h (cv v P.Δ) := by
  have hw : (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) * QuadraticAlgebra.omega
      = algebraMap (Lp L) (Lsq (Lp L) P.Δ) P.Δ := by
    rw [QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  unfold Pre.rt
  rw [← map_mul, ← map_mul, hw, P.e_alg, P.φ_alg]

def Pre.rho (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v) : Lsq (Kv v) (cv v P.Δ) →+* Kw w where
  toFun x := P.φ v w h x.re + P.φ v w h x.im * P.rt w
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by
    have := P.rt_sq v w h
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_zero]
    linear_combination (-(P.φ v w h x.im * P.φ v w h y.im)) * this
  map_zero' := by simp
  map_add' x y := by simp; ring

structure IsoOk {k k' : Type} [Field k] [ValuativeRel k] [Field k'] [ValuativeRel k'] (i : k ≃+* k') : Prop where
  int : ∀ a, valuation k' (i a) ≤ 1 ↔ valuation k a ≤ 1

end UpperTheory.V.Z.Sym.Dict.Br

end
