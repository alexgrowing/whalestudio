import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootsOfPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongPullTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPeriodsBasePeriodsConstFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_degFrom_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  intro g hg φ hφ n hn hodd F T b hb
  have hV : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  let e₀ : (Fin (Module.finrank ℤ T.D.toPre.X) → ℤ) ≃+ T.D.toPre.X :=
    (Module.finBasis ℤ T.D.toPre.X).equivFun.symm.toAddEquiv
  have hc : ∀ a a', T.D.toPre.c (e₀ (a + a')) = T.D.toPre.c (e₀ a) * T.D.toPre.c (e₀ a') := fun a a' => by
    rw [map_add]; exact T.D.toPre.c_add _ _
  obtain ⟨L, V₁, _, _, _, f₁, κ₁, e, hLh, hCN₁, hDVR₁, hi₁, hf₁, hl₁, hκ₁, hb₁, B', _, β', β'', β₂, β₂', p₁, p₂, s₁, s₂,
    lb, pts⟩ := GlobalTheory.T.exists_lower_base_of_trait_abelian_part n hn hodd T.V hV inferInstance b T.D.toPre.P _ (fun a => T.D.toPre.c (e₀ a)) hc
  have hr : L.T.r = Module.finrank ℤ T.D.toPre.X := by
    simpa using LinearEquiv.finrank_eq e.toIntLinearEquiv
  have hgen : L.h + L.T.r = g := by rw [hLh, hr]; exact GlobalTheory.Poinc.Trait.dim_add_rank (by omega) F T
  obtain ⟨q, hqs, hqa, hqp, hq⟩ := GlobalTheory.T.exists_pulledBack_periods_basePeriods_constForm n T.V T.D _ e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV inferInstance hCN₁ hDVR₁ hi₁ hf₁
    hl₁ hκ₁ p₁ p₂ s₁ s₂ lb pts
  obtain ⟨m, N, ε, hcone, hdef, V₂, _, _, _, f₂, fK, s, hCN₂, hDVR₂, hi₂, hf₂, hl₂, hfK, hs₁, hs₂, hqs'⟩ :=
    GlobalTheory.PerRoot.exists_roots_of_periods g n φ hφ (by omega) V₁ hCN₁ hDVR₁ L.T.r (by omega) q hqs hqa hqp
  have hl : IsLocalHom (f₂.comp f₁) := RingHom.isLocalHom_comp f₂ f₁
  have hlκ : IsLocalHom (f₂.comp κ₁) := RingHom.isLocalHom_comp f₂ κ₁
  obtain ⟨D', hD, G', _, _, π, A', U', hU⟩ :=
    GlobalTheory.TraitExt.exists_unifAlong_pullTo F T V₂ (f₂.comp f₁) hCN₂ hDVR₂ (hi₂.comp hi₁) (hf₂.comp hf₁) hl
  refine ⟨L, m, N, ε, V₂, inferInstance, inferInstance, inferInstance, f₂.comp f₁, f₂.comp κ₁, s, D',
    hD.xe.trans (e₀.symm.trans e.symm), G', inferInstance, inferInstance, π, A', U', hgen, hcone, hdef, hCN₂, hDVR₂,
    hi₂.comp hi₁, hf₂.comp hf₁, hl, hlκ, ?_, hs₁, hs₂, hU, ?_⟩
  · rw [RingHom.comp_assoc, hb₁, ← RingHom.comp_assoc]
  · exact hq V₂ f₂ fK s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) hCN₂ hi₂ hf₂ hl₂ hfK hqs' D' hD

end GlobalTheory.TChart
