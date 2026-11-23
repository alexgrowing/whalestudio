import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical Loc Glob

section Alg

variable {K : Type} [Field K] {Δ s : K}

def proj (hs : s * s = Δ) : Lsq K Δ →+* K where
  toFun x := x.re + s * x.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by simp [← hs]; ring
  map_zero' := by simp
  map_add' x y := by simp; ring

def eU (hs : s * s = Δ) : U3 Δ →* GL (Fin 3) K := (GeneralLinearGroup.map (proj hs)).comp Unitary.toUnits

def eD (hs : s * s = Δ) : DX Δ →* GL (Fin 2) K := (GeneralLinearGroup.map (proj hs)).comp (DX Δ).subtype

def ev {τ a : K} (h : a * a = τ * a - 1) : Etau K τ →+* K where
  toFun x := x.re + a * x.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by simp; linear_combination (-(x.im * y.im)) * h
  map_zero' := by simp
  map_add' x y := by simp; ring

def evU {τ a : K} (h : a * a = τ * a - 1) : (Etau K τ)ˣ →* Kˣ := Units.map (ev h : Etau K τ →* K)

theorem root_left (a : Kˣ) : (a : K) * a = ((a : K) + (a⁻¹ : Kˣ)) * a - 1 := by simp [add_mul]

theorem root_right (a : Kˣ) : ((a⁻¹ : Kˣ) : K) * (a⁻¹ : Kˣ) = ((a : K) + (a⁻¹ : Kˣ)) * (a⁻¹ : Kˣ) - 1 := by simp [add_mul]

end Alg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

structure IsInts (O : Type) [CommRing O] [Algebra O k] : Prop where
  inj : Function.Injective (algebraMap O k)
  range : ∀ x : k, x ∈ (algebraMap O k).range ↔ valuation k x ≤ 1

namespace Lev

variable (V : Lev k)

def unitaryHeckeTestSum (Ry : Finset kˣ) (t : kˣ) (g : GL (Fin 3) k) : ℂ := ∑ y ∈ Ry, V.unitaryDoubleCosetIndicator ![t * (unif k)⁻¹, y, (unif k)⁻¹] g

def quaternionDoubleCosetIndicator (t : kˣ) (g : GL (Fin 2) k) : ℂ := one (g ∈ V.DC ![t, t⁻¹])

def twistedCentralTestFunction (χ : kˣ →* ℂˣ) (t : kˣ) (g : GL (Fin 2) k) : ℂ := (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] g

def data {Δ s : k} (hs : s * s = Δ) (Ry : Finset kˣ) (χ : kˣ →* ℂˣ) : SigData Δ where
  P := {t | valuation k (t : k) < valuation k (unif k : k) ^ 2}
  H := V.H
  J := (V.J 3).comap (eU hs)
  J2 := (V.J 2).comap (eD hs)
  fG t g := V.unitaryHeckeTestSum Ry t (eU hs g)
  fS t g := V.quaternionDoubleCosetIndicator t (eD hs g)
  fK t g := V.twistedCentralTestFunction χ t (eD hs g)
  cG := (V.H.relIndex (Uo k) : ℝ) * (V.H.relIndex V.H2 : ℝ)
  cS := V.H.relIndex (Uo k)
  cK := V.H.relIndex (Uo k)

end Lev

end UpperTheory.V.Z.Sym.Sig

end
