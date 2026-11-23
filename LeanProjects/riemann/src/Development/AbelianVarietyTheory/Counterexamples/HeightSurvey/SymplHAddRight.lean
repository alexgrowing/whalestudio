import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilUnr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

namespace GlobalTheory.WeilVacCollapse

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hHom_add_left (V W : HSp D) (x x' y : WA V W) : hHom V W (x + x') y = hHom V W x y + hHom V W x' y := by
  unfold hHom
  split_ifs <;> simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hHom_add_right (V W : HSp D) (x y y' : WA V W) : hHom V W x (y + y') = hHom V W x y + hHom V W x y' := by
  unfold hHom
  split_ifs <;> simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem symplH_add_left (V W : HSp D) (x x' y : WA V W) :
    symplH V W (x + x') y = symplH V W x y + symplH V W x' y := by
  simp only [symplH, sympl, hHom_add_right, mul_add, map_add]

theorem symplH_add_right (V W : HSp D) (x y y' : WA V W) :
    symplH V W x (y + y') = symplH V W x y + symplH V W x y' := by
  simp only [symplH, sympl, hHom_add_left, mul_add, map_add]

theorem heis_heis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u u' : WA V W) (f : WA V W → ℂ) (w : WA V W) :
    Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W u' f) w = ψ (symplH V W u u') * Heisenberg₂ ψ V W (u + u') f w := by
  simp only [Heisenberg₂, symplH_add_left, symplH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem eq_zero_of_fixed (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : AddSubgroup (WA V W))
    {u u' : WA V W} (hu : u ∈ L) (hu' : u' ∈ L) (hne : ψ (symplH V W u u') ≠ 1)
    (f : WA V W → ℂ) (hf : ∀ x ∈ L, Heisenberg₂ ψ V W x f = f) : f = 0 := by
  funext w
  have h := heis_heis ψ V W u u' f w
  rw [hf u' hu', hf u hu, hf _ (L.add_mem hu hu')] at h
  have : (ψ (symplH V W u u') - 1) * f w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hne
  · exact h1

theorem unr_void {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) (V W : HSp D)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {u u' : WA V W} (hu : u ∈ latVWS V W S) (hu' : u' ∈ latVWS V W S)
    (hne : Wl.ψ (symplH V W u u') ≠ 1) (Φ : X.Sch V W)
    (hΦ : ∀ x ∈ latVWS V W S, Heisenberg₂ Wl.ψ V W x (Wl.evS V W Φ) = Wl.evS V W Φ) :
    Φ = 0 ∧ ∀ χ χ' (p : GA D V × GA D W), Wl.om V W χ χ' p Φ = Φ := by
  have h0 : Φ = 0 := Wl.evS_inj V W (by
    rw [eq_zero_of_fixed Wl.ψ V W _ hu hu' hne _ hΦ, map_zero])
  exact ⟨h0, fun χ χ' p => by rw [h0, map_zero]⟩

end GlobalTheory.WeilVacCollapse

end
