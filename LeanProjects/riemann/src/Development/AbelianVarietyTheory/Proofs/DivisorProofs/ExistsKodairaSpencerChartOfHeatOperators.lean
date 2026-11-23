import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaudStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChartKSBracket

theorem exists_derivation_intAlgebra' {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩

theorem exists_isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (O : Type) [CommRing O] [StarRing O] [Module O P.D.toPre.X] (oa : P.D.toPre.OAct O) (Y : Ray oa) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab O _ _ _ oa Y n vY dd hdd D hD h hbas hdef
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m d
  haveI : IsNoetherianRing (ChartRing k m d) := hA.1
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) := hA.2.2.2
  letI := H.starRing
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h0 => by
    have h4 := congrArg (fun f : ChartRing k m d => MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1) f) h0
    simp [bdParam, MvPowerSeries.coeff_X] at h4
  obtain ⟨ρ, hρ⟩ := GlobalTheory.TorusModel.exists_ringAct GlobalTheory.allSixLaws.1.globalFns P.oD (Φ := Y.Φ) Y.rep
  let Y' : Ray P.oD := { H := Y.H, Φ := Y.Φ, isGt := Y.isGt, rep := Y.rep, ρ := ρ, smul := hρ }
  choose v' hv' using fun a => tanPt E H (ChartRing k m d) t P Y' (vY a)
  refine ⟨fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left,
    fun a => isTanAtG_tv E H _ t (v' a), ?_⟩
  obtain ⟨D', hD'⟩ := exists_derivation_intAlgebra' _ D
  have key := GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud E H (ChartRing k m d) t P m (bdParam k m d) gam hmon hne hab Y' n vY dd hdd v' hv' D'
  rw [hD'] at key
  exact key h hbas hdef

end GlobalTheory.ChartKSBracket
