import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

theorem isField_eq_basicOpen {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    {d₁ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (h₁ : IsField V d₁) (h₂ : IsField V d₂)
    (h : ∀ a, d₁ V a = d₂ V a) (s : Γ(Z, V)) (g : Γ(Z, Z.basicOpen s)) :
    d₁ (Z.basicOpen s) g = d₂ (Z.basicOpen s) g := by
  have hle : Z.basicOpen s ≤ V := Z.basicOpen_le s
  haveI := hV.isLocalization_basicOpen s
  have halg : ∀ x, algebraMap Γ(Z, V) Γ(Z, Z.basicOpen s) x = resG Z hle x := fun _ => rfl

  have hres : ∀ x : Γ(Z, V), d₁ _ (resG Z hle x) = d₂ _ (resG Z hle x) := by
    intro x
    rw [h₁.2.2 V _ hle le_rfl, h₂.2.2 V _ hle le_rfl, h]
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) g
  simp only [halg] at hm
  have hu : IsUnit (resG Z hle (m : Γ(Z, V))) := by
    rw [← halg]; exact IsLocalization.map_units _ m
  have e₁ := congrArg (d₁ _) hm
  have e₂ := congrArg (d₂ _) hm
  rw [h₁.2.1 _ hle] at e₁
  rw [h₂.2.1 _ hle] at e₂
  have key : resG Z hle (m : Γ(Z, V)) * (d₁ _ g - d₂ _ g) = 0 := by
    rw [hres m] at e₁
    rw [hres a] at e₁
    linear_combination e₁ - e₂
  exact sub_eq_zero.mp ((hu.mul_right_eq_zero).mp key)

theorem isField_eq_of_affine : ∀ (Z : Scheme.{0}) (V : Z.Opens), IsAffineOpen V → ∀ (d₁ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField V d₁ → IsField V d₂ → (∀ a, d₁ V a = d₂ V a) → ∀ O : Z.Opens, O ≤ V → ∀ f, d₁ O f = d₂ O f := by
  intro Z V hV d₁ d₂ h₁ h₂ h O hO f
  refine TopCat.Presheaf.section_ext Z.sheaf O _ _ fun x hx => ?_
  obtain ⟨r, hrO, hxr⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ (hO hx)
  have e₁ := h₁.2.2 O _ hrO hO f
  have e₂ := h₂.2.2 O _ hrO hO f
  have e := isField_eq_basicOpen hV h₁ h₂ h r (resG Z hrO f)
  rw [e₁, e₂] at e
  have g₁ := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hrO) x hxr (d₁ O f)
  have g₂ := TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hrO) x hxr (d₂ O f)
  exact g₁.symm.trans ((congrArg _ e).trans g₂)

end GlobalTheory.LogKS
