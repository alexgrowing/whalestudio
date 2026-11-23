import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstAlongOfKodairaSpencerZeroChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerPullbackSemiAbelianMapStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartConst

theorem exists_derivation_top {R : Type} [CommRing R] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤), ⇑D' = fun r =>
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)) := by
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun x y => by rw [map_add, map_add, map_add] }) fun a b => ?_, rfl⟩
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a * b))) =
    a • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)) +
      b • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a))
  rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, e, e, smul_eq_mul, smul_eq_mul]

theorem valR_mem_maximalIdeal {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (g : Sp R ⟶ X) (U : X.Opens)
    (hU : ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) (hf : g (closedPoint R) ∉ X.basicOpen f) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U ⊤ hU).hom f) ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  rw [e] at h1
  have h2 := (Sp R).basicOpen_of_isUnit h1
  have h3 := Scheme.basicOpen_appLE g ⊤ U hU f
  have h4 : closedPoint R ∈ (⊤ : (Sp R).Opens) ⊓ g ⁻¹ᵁ X.basicOpen f := by
    rw [← h3]
    exact h2.ge trivial
  exact hf h4.2

theorem isConstAlong_of_ks_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → ∀ (t : SAB H (Sp (ChartRing k m' d))) (P : PELUnif (maximalIdeal (ChartRing k m' d)) t) (gam : Fin m' → levelForms H l.M' P.D.toPre.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → Nonempty (SABMap t Y.t (ξ ≫ genι Y)) → IsMonomial P.D.toPre (bdParam k m' d) (fun i => gam i) → IsPartOfBasis gam → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → ∀ ρ : ChartRing k m' d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (DR r))) → ∃ c₀ : ℚ, c₀ ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m' d) (fun i => gam i) ρ (fun i => (c₀ : k) * MvPowerSeries.constantCoeff (a i)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc U n v A hv hb hA D Θ m hm x hxi hxU hxm hKS hΘ k _ m' d ξ x' hξ hx'x t P gam
    hEt hId hBd ⟨φ⟩ hMon hPart hU DR a hDR ha ρ hρ
  subst hξ hx'x
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  have : CharZero k := GlobalTheory.LocReg.charZero_of_chart E H Dw l Xo c Y k m' d ξ
  have hfac := GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := GlobalTheory.LocReg.BasisPull.exists_basis_pull E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hb
  have hab := GlobalTheory.ChartAbLocus.mem_abLocus_iff E H Dw l Xo c Y k m' d ξ t φ hBd
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    hPart.linearIndependent.map' (Submodule.subtype _) (by simp)
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom_inv_id_apply r
  have hval : ∀ r, valR (ξ ≫ genι Y) U.1 r = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom
      (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r) := fun r => dif_pos hU
  have hch : ∀ r, valR (ξ ≫ genι Y) U.1 r = GlobalTheory.LocReg.chartHom Y U ξ hx r := fun r => by
    have h := GlobalTheory.CechKSSmul.valR_spMap_chart U (GlobalTheory.LocReg.chartHom Y U ξ hx) r
    rwa [← hfac] at h
  have happ : (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) =
      ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom := RingHom.ext fun r => by
    rw [RingHom.comp_apply, ← hch, hval, e]
  obtain ⟨D', hD'⟩ := exists_derivation_top DR
  have hV : (⊤ : (Sp (ChartRing k m' d)).Opens) ⊓ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) ≤
      (ξ ≫ genι Y) ⁻¹ᵁ interior Y := by
    intro p hp
    have h1 : p ∈ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) := hp.2
    have h2 := basicOpen_eq_of_affine (R := CommRingCat.of (ChartRing k m' d)) (∏ i, bdParam k m' d i)
    have h3 : p ∈ PrimeSpectrum.basicOpen (∏ i, bdParam k m' d i) := h2.le h1
    have h4 : ξ p ∉ genBd Y := fun h => h3 ((hBd p).1 h)
    rw [mem_genBd_iff, not_not, ← coe_interior] at h4
    exact h4
  have hK := GlobalTheory.T.cechKodairaSpencer_pullback_semiAbelianMap E H Y.X (Sp (ChartRing k m' d)) Y.t t (ξ ≫ genι Y) φ (interior Y) _ U
    (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m' d)).affineOpens) hU hV n v vR hv hvR
    (fun i => by rw [hcomp i, happ]) D.1 D' (fun r => by
      rw [hD']
      show (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (DR
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r))) =
        ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom (D.1 r)
      rw [← hval, hDR, hval, e]) Θ hKS
  rw [hD'] at hK
  exact GlobalTheory.T.isConstAlong_of_kodairaSpencer_zero_chart E H k m' d t P (fun i => gam i) hMon hlin hab n vR hvR hbR DR a ha _ hK
    (fun a b => valR_mem_maximalIdeal (ξ ≫ genι Y) U.1 hU (Θ a b) (hxm _ (hΘ a b))) ρ hρ

end GlobalTheory.ChartConst
