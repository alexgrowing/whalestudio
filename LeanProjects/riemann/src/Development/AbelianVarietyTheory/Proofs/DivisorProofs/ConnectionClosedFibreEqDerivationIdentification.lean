import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreDerivationOfTwoDualNumberPullbacksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalDerivationLiftingPrincipalPolarizationEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreOfPulledBackIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEqUnitMulOneAddEpsPotentialStatement
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

namespace GlobalTheory.HeatConn

theorem connK_eq_ident : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) ∧ ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ h₂ hag A₀ _ m₀ hm₀ pr hpr hprb J V jj ed pb hc w hw
  obtain ⟨dB, hdB, hid⟩ := GlobalTheory.T.exists_fibre_derivation_of_two_dualNumber_pullbacks k R P ρ B' π₁ π₂ h₁ h₂ hag A₀ m₀ hm₀ pr hpr hprb
  obtain ⟨q, hq⟩ := GlobalTheory.T.connection_closedFibre_of_pulledBack_iso k R P ρ B' π₁ π₂ h₁ h₂ hag A₀ m₀ hm₀ pr hpr hprb V jj hc.2.1 hc.2.2.1 dB hdB hid w hw
  have hv : GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj (fun W f => ed W f - dB W f) (fun i => pb i - q i) := by
    refine ⟨⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_, fun W hW r => ?_⟩, hc.2.1, hc.2.2.1, fun i i' => ?_⟩
    · simp only [hc.1.add W hW, hdB.add W hW]; ring
    · simp only [hc.1.mul W hW, hdB.mul W hW]; ring
    · rw [hc.1.res W W' h hW, hdB.res W W' h hW, GlobalTheory.KS.rsT_sub]
    · rw [hc.1.base W hW, hdB.base W hW, sub_self]; simp [constFn]
    · dsimp only
      rw [hc.2.2.2 i i', hq.2.2.2 i i', GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sub]; ring
  have e : ∀ W f, ed W f = dB W f := fun W f =>
    sub_eq_zero.1 (GlobalTheory.T.vertical_derivation_lifting_principalPolarization_eq_zero k R P ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) A₀ m₀ hm₀ V jj _ _ hv W f)
  have hA : (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) := fun W f => by rw [e]; exact hid W f
  exact ⟨hA, GlobalTheory.T.lineBundleIso_eq_unit_mul_one_add_eps_potential k R P ρ B' π₁ π₂ h₁ h₂ hag A₀ m₀ hm₀ pr hpr hprb V jj ed pb hc hA w hw⟩

end GlobalTheory.HeatConn
