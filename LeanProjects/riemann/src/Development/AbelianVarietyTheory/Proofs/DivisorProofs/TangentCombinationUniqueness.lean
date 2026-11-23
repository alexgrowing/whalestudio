import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMorphismEqOfLocalAgreement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberMorphismEqOfLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigBasisCover

attribute [local instance] Over.cartesianMonoidalCategory

open MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

omit [NumberField E] [IsCMField E] in

theorem sp_dual_eps {K L : Type} [CommRing K] [CommRing L] (ρ : K →+* L) (a : K) :
    spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (epsMul a) = spMap (epsMul (ρ a)) ≫ spMap (Formalism.L2.Pj.dualMap ρ) := by
  rw [spMap_comp', spMap_comp', ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_epsMul]

theorem isEigTan_map {K L : Type} [CommRing K] [CommRing L] (ρ : K →+* L) (φ : c.F →+* K) {y : Sp K ⟶ Z.X}
    {τ : E →+* ℂ} {w : Sp (DualNumber K) ⟶ Z.t.G.left} (h : IsEigTan Z φ y τ w) :
    IsEigTan Z (ρ.comp φ) (spMap ρ ≫ y) τ (spMap (Formalism.L2.Pj.dualMap ρ) ≫ w) := by
  refine ⟨GlobalTheory.FactorDepth.isTanAtG_map Z.t ρ h.1, fun a => ?_⟩
  rw [Category.assoc, h.2 a, ← Category.assoc, sp_dual_eps, Category.assoc]

theorem comb_pull {K L M : Type} [CommRing K] [CommRing L] [CommRing M] (f : K →+* L) (g : L →+* M)
    {y : Sp K ⟶ Z.X} {m : ℕ} {u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} {cf : Fin m → L}
    {w : Sp (DualNumber K) ⟶ Z.t.G.left}
    (h : IsCombAtG Z.t (spMap f ≫ y) (fun i => spMap (Formalism.L2.Pj.dualMap f) ≫ u i) cf
      (spMap (Formalism.L2.Pj.dualMap f) ≫ w)) :
    IsCombAtG Z.t (spMap (g.comp f) ≫ y) (fun i => spMap (Formalism.L2.Pj.dualMap (g.comp f)) ≫ u i) (fun i => g (cf i))
      (spMap (Formalism.L2.Pj.dualMap (g.comp f)) ≫ w) := by
  have h' := GlobalTheory.LatDRFree.comb_map Z.t g h
  simp only [← Category.assoc, spMap_comp', ← ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp] at h'
  exact h'

theorem isEigBasis_of_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [CommRing K] (φ : c.F →+* K) (y : Sp K ⟶ Z.X) (τ : E →+* ℂ) {m : ℕ} (u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)) {s : Set K}, Ideal.span s = ⊤ → (∀ a : s, IsEigBasis Z ((algebraMap K (Localization.Away (a : K))).comp φ) (spMap (algebraMap K (Localization.Away (a : K))) ≫ y) τ (fun i => spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ u i)) → (∀ a b : s, IsEigBasis Z ((algebraMap K (Localization.Away ((a : K) * b))).comp φ) (spMap (algebraMap K (Localization.Away ((a : K) * b))) ≫ y) τ (fun i => spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away ((a : K) * b)))) ≫ u i)) → IsEigBasis Z φ y τ u := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z K _ φ y τ m u s hs h1 h2
  have hEig : ∀ i, IsEigTan Z φ y τ (u i) := by
    intro i
    refine ⟨⟨?_, ?_⟩, fun e => ?_⟩
    · refine GlobalTheory.ArLieBase.hom_ext_dualNumber_away hs fun a => ?_
      have h := ((h1 a).1 i).1.1
      simp only [Category.assoc] at h ⊢
      rw [h, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_alg]
    · refine GlobalTheory.spec_hom_ext_of_span_eq_top hs fun a => ?_
      have h := ((h1 a).1 i).1.2
      have e : (TrivSqZeroExt.fstHom (Localization.Away (a : K)) (Localization.Away (a : K)) (Localization.Away (a : K))).toRingHom.comp
          (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) =
          (algebraMap K (Localization.Away (a : K))).comp (TrivSqZeroExt.fstHom K K K).toRingHom := by
        refine RingHom.ext fun z => ?_
        simp [Formalism.L2.Pj.dualMap]
      rw [← Category.assoc, spMap_comp', ← e, ← spMap_comp', Category.assoc, h]
      let ψ : Over.mk (spMap (algebraMap K (Localization.Away (a : K))) ≫ y) ⟶ Over.mk y :=
        Over.homMk (spMap (algebraMap K (Localization.Away (a : K)))) rfl
      exact (congrArg (fun g => g.left) (MonObj.comp_one ψ : ψ ≫ (1 : Over.mk y ⟶ Z.t.G) = 1)).symm
    · refine GlobalTheory.ArLieBase.hom_ext_dualNumber_away hs fun a => ?_
      have h := ((h1 a).1 i).2 e
      have k := sp_dual_eps (algebraMap K (Localization.Away (a : K))) (φ (embK c τ e))
      simp only [Category.assoc] at h
      rw [h, ← Category.assoc, ← Category.assoc, k]
  refine ⟨hEig, fun w hw => ?_⟩
  have hw' : ∀ a : s, IsEigTan Z ((algebraMap K (Localization.Away (a : K))).comp φ)
      (spMap (algebraMap K (Localization.Away (a : K))) ≫ y) τ
      (spMap (Formalism.L2.Pj.dualMap (algebraMap K (Localization.Away (a : K)))) ≫ w) :=
    fun a => isEigTan_map Z _ φ hw
  choose cA hcA using fun a : s => (h1 a).2 _ (hw' a)
  have compat : ∀ (a b : s) (i : Fin m), IsLocalization.Away.awayToAwayRight (S := Localization.Away (a : K))
      (P := Localization.Away ((a : K) * b)) (a : K) (b : K) (cA a i) =
      IsLocalization.Away.awayToAwayLeft (S := Localization.Away (b : K))
      (P := Localization.Away ((a : K) * b)) (b : K) (a : K) (cA b i) := by
    intro a b i
    have hr : (IsLocalization.Away.awayToAwayRight (S := Localization.Away (a : K))
        (P := Localization.Away ((a : K) * b)) (a : K) (b : K)).comp (algebraMap K (Localization.Away (a : K))) =
        algebraMap K (Localization.Away ((a : K) * b)) :=
      RingHom.ext fun z => IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away (a : K))
        (P := Localization.Away ((a : K) * b)) (a : K) (b : K) z
    have hl : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (b : K))
        (P := Localization.Away ((a : K) * b)) (b : K) (a : K)).comp (algebraMap K (Localization.Away (b : K))) =
        algebraMap K (Localization.Away ((a : K) * b)) :=
      RingHom.ext fun z => IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away (b : K))
        (P := Localization.Away ((a : K) * b)) (b : K) (a : K) z
    have Ca := comb_pull Z _ (IsLocalization.Away.awayToAwayRight (S := Localization.Away (a : K))
        (P := Localization.Away ((a : K) * b)) (a : K) (b : K)) (hcA a).1
    have Cb := comb_pull Z _ (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (b : K))
        (P := Localization.Away ((a : K) * b)) (b : K) (a : K)) (hcA b).1
    rw [hr] at Ca
    rw [hl] at Cb
    exact congrFun (((h2 a b).2 _ (isEigTan_map Z _ φ hw)).unique Ca Cb) i
  choose cf hcf using fun i : Fin m =>
    Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs (fun a => cA a i) (fun a b => compat a b i)
  have hut : ∀ k, IsTanAtG Z.t y (u k) := fun k => (hEig k).1
  obtain ⟨w', -, hw'c⟩ := GlobalTheory.ShFam.Pad.Guard.exists_comb hut cf
  have hww : w' = w := by
    refine GlobalTheory.ArLieBase.hom_ext_dualNumber_away hs fun a => ?_
    have e1 := GlobalTheory.LatDRFree.comb_map Z.t (algebraMap K (Localization.Away (a : K))) hw'c
    have e2 : (fun i => algebraMap K (Localization.Away (a : K)) (cf i)) = cA a := funext fun i => (hcf i).1 a
    rw [e2] at e1
    exact GlobalTheory.ShFam.Pad.Guard.comb_unique (fun k => ((h1 a).1 k).1) e1 (hcA a).1
  refine ⟨cf, hww ▸ hw'c, fun d hd => ?_⟩
  funext i
  have hda : ∀ a : s, (fun j => algebraMap K (Localization.Away (a : K)) (d j)) = cA a :=
    fun a => (hcA a).2 _ (GlobalTheory.LatDRFree.comb_map Z.t _ hd)
  exact (hcf i).2 (d i) fun a => congrFun (hda a) i

end GlobalTheory.EigBasisCover
