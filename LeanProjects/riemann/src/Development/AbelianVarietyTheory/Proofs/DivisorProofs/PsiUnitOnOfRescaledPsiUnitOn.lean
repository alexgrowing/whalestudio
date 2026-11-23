import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem isUnit_res_of_le_basicOpen' {X : Scheme.{0}} {U V : X.Opens} (f : Γ(X, U)) (hVU : V ≤ U)
    (h : V ≤ X.basicOpen f) : IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  have e : X.presheaf.map (homOfLE hVU).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ X.presheaf.map (homOfLE h).op := by
    rw [← Functor.map_comp]; rfl
  rw [e]
  exact hu

theorem psiUnitOn_of_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (y : D.X) (U : Set (Sp R)) (a b : R), (g y : FractionRing R) * algebraMap R (FractionRing R) a = algebraMap R (FractionRing R) b → (∀ p ∈ U, a ∉ (p : PrimeSpectrum R).asIdeal ∧ b ∉ (p : PrimeSpectrum R).asIdeal) → PsiUnitOn (GlobalTheory.PolDeg.rescale D g) y U → PsiUnitOn D y U := by
  intro R _ _ D g y U a b hab hU hR j V hV hVU hj h
  obtain ⟨r₀, hr₀u, hr₀⟩ := hR j V hV hVU hj h
  have hle : (V : (Sp R).Opens) ≤ ⊤ := le_top
  have hVa : V ≤ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
    intro x hx
    show x ∈ ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) : Set (Sp R))
    rw [basicOpen_eq_of_affine]
    exact (hU x (hVU hx)).1
  have hVb : V ≤ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b) := by
    intro x hx
    show x ∈ ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b) : Set (Sp R))
    rw [basicOpen_eq_of_affine]
    exact (hU x (hVU hx)).2
  obtain ⟨Au, hAu⟩ := isUnit_res_of_le_basicOpen' _ hle hVa
  obtain ⟨Bu, hBu⟩ := isUnit_res_of_le_basicOpen' _ hle hVb
  refine ⟨Au.val * r₀ * (Bu⁻¹ : Γ(Sp R, V)ˣ).val, ((Au.isUnit.mul hr₀u).mul (Bu⁻¹).isUnit), ?_⟩
  set K := FractionRing R
  set c : K →+* Γ((TK R).left, jK R ⁻¹ᵁ V) :=
    ((TK R).left.presheaf.map (homOfLE (le_top : jK R ⁻¹ᵁ V ≤ ⊤)).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    with hc
  have hnat : ∀ x : R, ((jK R).app V).hom ((Sp R).presheaf.map (homOfLE hle).op |>.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) = c (algebraMap R K x) := by
    intro x
    have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))
      ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [e]
    have e2 := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
    rw [hc, RingHom.comp_apply, e2]
    rfl
  have hA : ((jK R).app V).hom Au.val = c (algebraMap R K a) := by rw [hAu]; exact hnat a
  have hB : ((jK R).app V).hom Bu.val = c (algebraMap R K b) := by rw [hBu]; exact hnat b
  have hG : ∀ (W : (TK R).left.Opens) (h₁ : jK R ⁻¹ᵁ V ≤ W) (h₂ : W ≤ ⊤), ((TK R).left.presheaf.map (homOfLE h₁).op).hom (res h₂ (unitOn (g y))).val = c (g y) := by
    intro W h₁ h₂
    show ((TK R).left.presheaf.map (homOfLE h₁).op).hom (((TK R).left.presheaf.map (homOfLE h₂).op).hom (unitOn (g y)).val) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  have hBB : ((jK R).app V).hom Bu.val * ((jK R).app V).hom (Bu⁻¹ : Γ(Sp R, V)ˣ).val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hab' : c (algebraMap R K a) * c (g y) = c (algebraMap R K b) := by
    rw [← map_mul, _root_.mul_comm, hab]
  rw [map_mul, map_mul, hr₀]
  show _ * (((TK R).left.presheaf.map (homOfLE h).op).hom (_ * _)) * _ = _
  erw [map_mul]
  rw [hG, hA]
  rw [← hB] at hab'
  rw [← _root_.mul_assoc, hab', _root_.mul_right_comm, hBB, _root_.one_mul]

end GlobalTheory.PolDeg
