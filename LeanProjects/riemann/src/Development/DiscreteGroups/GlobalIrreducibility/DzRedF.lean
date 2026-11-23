import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ExistsFunctionalNe

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic
  GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem psi_cancel (a : Circle) (X Y : ℂ) : (a : ℂ) * X * (((a⁻¹ : Circle) : ℂ) * Y) = X * Y := by
  have h : ((a⁻¹ : Circle) : ℂ) * (a : ℂ) = 1 := by rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  linear_combination (X * Y) * h

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

theorem phi_corner {m : ℕ} (κ : GL (Fin m) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g (m + 1) (corner κ)) =
      corner (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m κ)) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (corner κ)) = _
  rw [map_corner, map_corner]
  rfl

theorem phi_invT {n : ℕ} (κ : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n (GlobalTheory.CuspRep.invT n ℤ_[g] κ)) =
      GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (GlobalTheory.CuspRep.invT n ℤ_[g] κ)) = _
  rw [map_invT, map_invT]
  rfl

theorem phi_longElt (n : ℕ) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n (longElt n ℤ_[g])) = longElt n (w.adicCompletion E) := by
  show Matrix.GeneralLinearGroup.map i.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) (longElt n ℤ_[g])) = _
  rw [map_longElt, map_longElt]

theorem red_corner {m : ℕ} (κ : GL (Fin m) ℤ_[g]) : red g (m + 1) (corner κ) = corner (red g m κ) :=
  map_corner _ κ

theorem red_invT {n : ℕ} (κ : GL (Fin n) ℤ_[g]) :
    red g n (GlobalTheory.CuspRep.invT n ℤ_[g] κ) = GlobalTheory.CuspRep.invT n _ (red g n κ) :=
  map_invT _ κ

def FR {m : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')
    (y : V) (v' : V') (h : GL (Fin m) (w.adicCompletion E)) : ℂ :=
  L (π (corner h) y) * l' (ρ₀ h v')

def FL {m : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')
    (y : V) (v' : V') (h : GL (Fin m) (w.adicCompletion E)) : ℂ :=
  L (π (tilde (corner h)) y) * l' (ρ₀ (tilde h) v')

section Inv

variable {m : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GL (Fin (m + 1)) (w.adicCompletion E)) V)
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (L : Module.Dual ℂ V) (l' : Module.Dual ℂ V')

theorem FR_left (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (y : V) (v' : V')
    {u : GL (Fin m) (w.adicCompletion E)} (hu : u ∈ unipB (w.adicCompletion E) (Fin m)) (h : GL (Fin m) (w.adicCompletion E)) :
    FR π ρ₀ L l' y v' (u * h) = FR π ρ₀ L l' y v' h := by
  unfold FR
  rw [corner_mul, rep_mul_apply, hL _ (corner_mem hu), superDiag_corner, rep_mul_apply, hl' _ hu, AddChar.inv_apply']
  exact psi_cancel _ _ _

theorem FL_left (hL : IsFunctional ψ π L) (hl' : IsFunctional ψ⁻¹ ρ₀ l') (y : V) (v' : V')
    {u : GL (Fin m) (w.adicCompletion E)} (hu : u ∈ unipB (w.adicCompletion E) (Fin m)) (h : GL (Fin m) (w.adicCompletion E)) :
    FL π ρ₀ L l' y v' (u * h) = FL π ρ₀ L l' y v' h := by
  obtain ⟨u₁, hu₁, u₂, hu₂, e1, e2, e3⟩ := tilde_corner_unip hu h
  unfold FL
  rw [e1, e2, rep_mul_apply, rep_mul_apply, hL _ hu₁, hl' _ hu₂, e3, AddChar.inv_apply']
  exact psi_cancel _ _ _

end Inv

end DiscreteGroups.sglob.DzRed
