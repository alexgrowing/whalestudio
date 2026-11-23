import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedCompatibleMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabMapExtendsDenseStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem psiCoord_associated {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {χ : D.X} {r r' : R}
    (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : Associated r r' := by
  obtain ⟨x, hx, ex⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 h
  obtain ⟨x', hx', ex'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r').1 h'
  obtain ⟨u, hu⟩ := hx.unique hx'
  have e1 : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u * r') := by
    rw [← ex, hu, map_mul, ← ex']
    rfl
  have e2 : r = u * r' := IsFractionRing.injective R (FractionRing R) e1
  exact ⟨u⁻¹, by rw [e2, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

theorem inConePull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R'))
    (P : PELUnif (maximalIdeal R) t) (P' : PELUnif (maximalIdeal R') t') (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    (∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)) → InCone P.D.toPre γ →
    InCone P'.D.toPre (fun i => pull e.toLinearMap (γ i)) := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t t' P P' e m γ hpsi hin
  intro W _ _ _ hW ϖ hϖ f be hsym hF
  have hF0 : FormAt P.D.toPre (f.comp φ) ϖ (pull e.symm.toLinearMap be) := by
    intro y0
    obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P.D.toPre y0).2
      (GlobalTheory.PeriodFormCompare.psiIn_top P.D y0)
    obtain ⟨u, hu⟩ := hpsi (e.symm y0) r (by rwa [e.apply_symm_apply])
    obtain ⟨r', n, hr', hbe, hass⟩ := hF (e.symm y0)
    refine ⟨r, n, hr, by simpa [pull_apply] using hbe, ?_⟩
    have h1 : Associated (u * φ r) r' := psiCoord_associated hu hr'
    have h2 : Associated (f (φ r)) (f (u * φ r)) := by
      rw [map_mul]
      exact ⟨(Units.map f.toMonoidHom u), by simp [mul_comm]⟩
    exact h2.trans ((h1.map f).trans hass)
  obtain ⟨cf, hc, heq⟩ := hin W hW ϖ hϖ (f.comp φ) (pull e.symm.toLinearMap be)
    (fun a b => by simp [pull_apply, hsym]) hF0
  refine ⟨cf, hc, ?_⟩
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  have := congrArg (fun F => F (e a) (e b)) heq
  simpa [toReal, pull_apply, LinearMap.sum_apply] using this

theorem hasCones_of_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop), (∀ (X₁ X₂ : Type) [AddCommGroup X₁] [Module (𝓞 E) X₁] [Module.Finite (𝓞 E) X₁] [AddCommGroup X₂] [Module (𝓞 E) X₂] [Module.Finite (𝓞 E) X₂] (f : X₁ ≃ₗ[𝓞 E] X₂) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₂), Cn X₂ m γ → Cn X₁ m (fun i => pull f.toLinearMap (γ i))) → Z.j ≫ π = X.j → π ≫ X.s = Z.s → HasCones Cn X → HasCones Cn Z := by
  intro E _ _ _ H D l Xo c X Z π Cn hCn hj hs hX z
  obtain ⟨R, _, _, _, ξ, t, a, P, m, γ, hcn, hpt, het, hfu, htor, hcone, hin⟩ := hX (π z)
  obtain ⟨R', _, _, _, ξ', φ, hcn', hpt', het', hfu', hinj, hloc, hsq, hdense⟩ :=
    GlobalTheory.T.formally_unramified_compatible_map E H D l Xo c X Z π hj hs R ξ z hcn het hfu hpt
  obtain ⟨t', a', P', e, htor', hpsi⟩ := pullSt E H R R' φ t P hcn hcn' hinj hloc htor
  obtain ⟨a'', -⟩ := GlobalTheory.ObjMaps.exists_sab_comp a a'
  rw [← hsq] at a''
  obtain ⟨b⟩ := GlobalTheory.T.sabMap_extends_dense E H D l Xo c X Z π hj R' ξ' t' hcn' hdense a''
  exact ⟨R', inferInstance, inferInstance, inferInstance, ξ', t', b, P', m, fun i => pull e.toLinearMap (γ i),
    hcn', hpt', het', hfu', htor', hCn _ _ e m γ hcone, inConePull E H R R' φ t t' P P' e m γ hpsi hin⟩

end GlobalTheory.TorRef
