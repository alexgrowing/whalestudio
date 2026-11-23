import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatSym
open GlobalTheory.HeatMod

theorem VS.sub : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (p : Y ⟶ Sp R) (L : LB Y) (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)), x ≫ p = spMap φ → ∀ (k : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g k s' → GlobalTheory.HeatSym.VS φ L x g k (s - s') := by
  intro R Ω _ _ _ _ φ Y p L x g hxp k s s' ⟨r, σ, ω, hr, hv, he⟩ ⟨r', σ', ω', hr', hv', he'⟩
  refine ⟨r * r', constFn p ⊤ r' • σ - constFn p ⊤ r • σ', φ r' * ω - φ r * ω', mul_ne_zero hr hr', ?_, ?_⟩
  · intro Z t z J hJ
    have e : ∀ a : R, ((spMap φ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) =
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a) := by
      intro a
      have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
      exact this.symm
    have key : ∀ a : R, germConstHom ((t ≫ x) ≫ p) z a =
        gs t z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a)) := by
      intro a
      rw [Category.assoc, hxp, gs_eq t z ⊤ trivial, ← e]; rfl
    have hm := hJ.mem (fun _ : Fin 1 => 𝟙 Y) (t ≫ x)
    have h2 : ∀ (a : R) (τ : SecM (𝟙 Y) L k), sval (constFn p ⊤ a • τ) (t ≫ x) z J =
        germConstHom ((t ≫ x) ≫ p) z a * sval τ (t ≫ x) z J := fun a τ =>
      (gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·)
        ((gs_res _ z le_top hm _).trans (gs_constFn_eq_germConstHom p _ z a)) rfl)
    rw [sval_sub_constFn_smul p _ _ r (t ≫ x) z hJ, h2, hv Z t z J hJ, hv' Z t z J hJ, key, key]
    simp only [gs_eq t z ⊤ trivial, map_sub, map_mul]
    ring
  · rw [map_sub, map_mul, map_mul, he, he', map_mul, map_mul]
    ring

end GlobalTheory.HeatSym
