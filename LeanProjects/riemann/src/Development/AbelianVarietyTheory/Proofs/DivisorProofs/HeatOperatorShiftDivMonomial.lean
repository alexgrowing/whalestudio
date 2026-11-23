import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecBEqEverywhereOfGenericAgreeConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermIdentityDescendsGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConstMulDerivationTermStatement
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
namespace GlobalTheory.Heat

theorem heat_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' _ π₁ π₂ c' h1 h2 h3 h4 e he mu α N σ σ' σ₁ σ₁u σ₁' σ₁u' hT hS hS' hv hv'
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

  clear hρ h1 h2 h3 h4 hΘ hmon hli hab
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq h hb hdef ⊢
  letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
  let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
    { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
  have hA1 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁
  have hA2 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁u
  obtain ⟨σ₁'', hA1⟩ := hA1
  obtain ⟨σ₁u'', hA2⟩ := hA2
  refine ⟨σ₁u'', hA2, ?_⟩
  have hd : ShiftEq P.D.toPre e mu α σ' σ₁'' 0 σ₁ := hdef e mu α σ σ' σ₁ σ₁'' he hS hT hA1
  obtain ⟨⟨u, hu, hc⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := P.D.toPre) (F := FractionRing (ChartRing k m d))
    GlobalTheory.SemiRigid.globalFns e mu α
  have hU : ∀ z J, Good P.D.toPre.P.L z J → sval σ₁'' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J =
      sval σ₁' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J := by
    intro z J hJ
    have E1 := GlobalTheory.HeatDefect.shiftEq_at hd u hu hc (𝟙 _) z J hJ
    have E2 := GlobalTheory.HeatDefect.shiftEq_at hS' u hu hc (𝟙 _) z J hJ
    simp only [Category.id_comp, GlobalTheory.HeatDefect.scal_zero, zero_mul, add_zero] at E1 E2
    rw [E1, E2]
  obtain ⟨τ₁, τ₁'', t1, t1'', a1⟩ := hA1
  obtain ⟨τu, τu'', tu, tu'', a2⟩ := hA2
  have hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → sval τ₁ r z J = gs (r ≫ Y.H.hom) z ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval τu r z J := by
    intro Z r z J hJ
    let x : Over.mk (r ≫ Y.H.hom) ⟶ Y.H := Over.homMk r rfl
    have e1 := t1 _ x z J hJ
    have e2 := tu _ x z J hJ
    have e3 := hv Z (r ≫ Y.q.left) z J hJ
    have hw : (r ≫ Y.q.left) ≫ P.D.toPre.P.A.hom = r ≫ Y.H.hom := by rw [Category.assoc, Over.w]
    rw [hw] at e3
    change sval τ₁ r z J = _ at e1
    change sval τu r z J = _ at e2
    rw [Over.comp_left] at e1 e2
    change _ = sval σ₁ (r ≫ Y.q.left) z J * _ at e1
    change _ = sval σ₁u (r ≫ Y.q.left) z J * _ at e2
    rw [e1, e2, e3, _root_.mul_assoc]

  have hτ'' := GlobalTheory.T.heatOperator_const_mul_derivation_term (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y n' (fun a => v' a) dd hdd D' h e
    (∏ i, bdParam k m d i ^ N i) τ₁ τ₁'' τu τu'' a1 a2 hτ
  have hP := GlobalTheory.T.fourierTerm_identity_descends_genericFibre (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y e (α + e • mu) σ₁'' σ₁u'' σ₁u τ₁'' τu'' τu
    (∏ i, bdParam k m d i ^ N i) (2 * (e : ChartRing k m d) * D' (∏ i, bdParam k m d i ^ N i)) t1'' tu'' tu hτ''
  have hpow : ∀ (x c : ChartRing k m d), D' x = c * x → ∀ n : ℕ, D' (x ^ n) = (n : ChartRing k m d) * c * x ^ n := by
    intro x c hx n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, ih, hx, smul_eq_mul, smul_eq_mul]
      push_cast; ring
  have hDt : ∀ s : Finset (Fin m), D' (∏ i ∈ s, bdParam k m d i ^ N i) =
      (∑ i ∈ s, (N i : ChartRing k m d) * q i) * ∏ i ∈ s, bdParam k m d i ^ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih,
        hpow _ (q a) (hq a) (N a), smul_eq_mul, smul_eq_mul]
      ring
  have hne0 : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  have hne : (∏ i, bdParam k m d i ^ N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne0 i)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (c : ChartRing k m d),
      gs (r ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom c) =
        GlobalTheory.HeatMod.germConstHom (r ≫ P.D.toPre.P.A.hom) z c := fun r z c =>
    (GlobalTheory.HeatTermLin.gs_constFn _ r z c).symm.trans (GlobalTheory.HeatMod.gs_constFn_eq_germConstHom _ r z c)
  have key := GlobalTheory.T.secB_eq_everywhere_of_generic_agree_const (ChartRing k m d) P.D.toPre e (α + e • mu) σ₁u''
    (σ₁u' - constFn P.D.toPre.P.A.hom ⊤ (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i) • σ₁u)
    (∏ i, bdParam k m d i ^ N i) hne (by
      intro z J hJ
      have a1 := hP z J hJ
      have a2 := hU z J hJ
      have a3 := hv' _ (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J hJ
      rw [GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ]
      rw [hDt] at a1
      simp only [hg] at a1 a3 ⊢
      simp only [map_mul, map_natCast, map_ofNat] at a1 ⊢
      linear_combination a2 + a3 - a1)
  intro Z x z J hJ
  rw [key Z x z J hJ, GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ, hg]

end GlobalTheory.Heat
