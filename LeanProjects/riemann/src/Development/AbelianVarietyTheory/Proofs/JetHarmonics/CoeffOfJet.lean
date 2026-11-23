import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.IntegralGerm

section Val

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem gs_comp (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem sval_comp {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y') (h : Y' ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) fun ψ => J (r ≫ ψ)) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_secLin (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    {c : Fin n → Γ(Y', ⊤)} (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  have e := (FieldBaseChange.secLin_iff_val hL s₁ s h c).1 H (r z) (fun ψ => J (r ≫ ψ)) fun ψ => hJ (r ≫ ψ)
  have e₁ := sval_comp s₁ r (𝟙 _) z hJ
  rw [Category.comp_id, e, map_sum] at e₁
  refine e₁.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← gs_stalkMap r z ⊤ trivial, Category.id_comp, ← sval_comp (s i) r h z hJ]

theorem exists_value (hL : L.IsLB) {q : ℕ} (s : H0 L q) (h : Y ⟶ X)
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (1 : ℤ)))) (ht : t.IsGen) :
    ∃ u : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s (r ≫ h) z J = gs r z ⊤ u * (val t r z J ^ q).val := by
  obtain ⟨w, hw⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ hh => by simp [Fintype.prod_sum_type])
    (pullMulSec s h (LB.invGen L _ _ (GeneratorPullback.powGen L _ _ t q))
      (invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht q)))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (K := PEmpty) (Y := Y) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (w.f PEmpty.elim), fun Z r z J hJ => ?_⟩
  have e := hw Z r z J hJ
  have ep : val (GeneratorPullback.powGen L _ _ t q) r z J = val t r z J ^ q := map_pow _ _ _
  rw [sval_pullMulSec _ _ _ _ _ z hJ, val_inv, ep, sval_of w _ z J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg (· * _) ((gs_res r z le trivial _).trans e).symm)
  rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end Val

theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (spMap f) y ⊤ (toΓ A a) = gs (𝟙 _) y ⊤ (toΓ B (f a)) := by
  have e := FieldBaseChange.constVal_specMap (𝟙 (Sp B)) f y a
  rw [Category.id_comp] at e
  exact e

theorem toΓ_surjective (A : Type) [CommRing A] : Function.Surjective (toΓ A) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective

theorem coeff_of_jet {V F κ : Type} [CommRing V] [CommRing F] (g : V →+* F) [Fintype κ] [DecidableEq κ]
    (f : MvPowerSeries κ F) (e : κ →₀ ℕ) {n : ℕ} (c : Fin n → F) (a : Fin n → Jet V κ e.degree)
    (h : psJet e.degree f = ∑ i, algebraMap F (Jet F κ e.degree) (c i) * jetCoef g κ e.degree (a i)) :
    ∃ b : Fin n → V, MvPowerSeries.coeff e f = ∑ i, c i * g (b i) := by
  choose p hp using fun i => Ideal.Quotient.mk_surjective (a i)
  refine ⟨fun i => MvPolynomial.coeff e (p i), ?_⟩
  have h1 : psJet e.degree f = Ideal.Quotient.mk _ (∑ i, MvPolynomial.C (c i) * MvPolynomial.map g (p i)) := by
    rw [h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hp]
    rfl
  rw [psJet, Ideal.Quotient.eq] at h1
  have h2 := GermFun.coeff_eq_zero_of_mem h1 (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ le_rfl, sub_eq_zero] at h2
  rw [h2, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → AIntSt := by
  intro hLaw _ _ hT V _ _ _ _ ϖ hϖ D A G _ _ U κ _ _ z _ τ hτ F _ _ _ _ v hv q hq σ' s f hE hG hs e
  obtain ⟨n, c, σ, hc, hlin⟩ := IntegralCombination.main hLaw.globalFns hT V ϖ hϖ D A G U F v hv q hq σ' s hE hs
  obtain ⟨zF, h1, h2, h3⟩ := hG e.degree
  have hL := U.LG.isLB
  choose u hu using fun i => exists_value hL (σ i) (z e.degree).left (τ e.degree) (hτ e.degree)
  choose a ha using fun i => toΓ_surjective (Jet V κ e.degree) (u i)
  obtain ⟨b, hb⟩ := coeff_of_jet (algebraMap V F) f e c a (GermFun.toΓ_injective _ (fn_ext fun y _ => by
    choose J hJ using fun χ : Sp (Jet F κ e.degree) ⟶ G.left => exists_chart hL (χ y)
    have e₁ := (h3 y J hJ).symm.trans (sval_secLin hL hlin zF y hJ)
    refine (Units.mul_left_inj _).1 (e₁.trans ?_)
    rw [map_sum, gs_eq _ y ⊤ trivial, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← gs_eq _ y ⊤ trivial, map_mul, gs_mul _ y ⊤ trivial, h2, hu i _ _ y J hJ, ← ha, gs_spMap, _root_.mul_assoc,
      FieldBaseChange.gs_scal, h1]
    exact congrArg (· * _) (gs_spMap _ y _)))
  rw [hb]
  refine v.map_le_sum fun i _ => ?_
  rw [AddValuation.map_mul, IsScalarTower.algebraMap_apply V (FractionRing V) F]
  exact add_nonneg (hc i) (GC.v_alg_nonneg hϖ hv _)

end GlobalTheory.IntegralGerm
