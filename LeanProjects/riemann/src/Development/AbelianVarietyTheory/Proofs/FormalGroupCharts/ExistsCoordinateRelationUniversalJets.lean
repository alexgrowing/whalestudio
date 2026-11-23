import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqLoc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1

variable {V : Type} [CommRing V]

theorem uniq {G : Over (Sp V)} [GrpObj G] {κ : Type} {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A : Type} [CommRing A] [Algebra V A] (aug : A →ₐ[V] V) (m : ℕ) (hk : RingHom.ker aug ^ (m + 1) = ⊥)
    {ψ₁ ψ₂ : Jet V κ m →ₐ[V] A} (h1 : aug.comp ψ₁ = jetAug) (h2 : aug.comp ψ₂ = jetAug)
    (e : Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₂ ≫ x m) : ψ₁ = ψ₂ := by
  have hy : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m) = 1 := by
    rw [← Category.assoc, GermD.homAt_comp, h1, hx.2.1]
  exact (hx.2.2 A aug m hk _ hy).unique ⟨h1, rfl⟩ ⟨h2, e⟩

theorem jetSubstP_trunc {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (φ : κ → MvPowerSeries κ' V) :
    jetSubstP m (fun p => psTrunc m (φ p)) = jetSubstPS (m := m) φ := rfl

theorem aug_X {κ : Type} (m : ℕ) (j : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = 0 := ExpUniqJet.augmentation_jet_variable m j

theorem aug_comp_subst {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (m : ℕ)
    (φ : κ → MvPowerSeries κ' V) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    (jetAug : Jet V κ' m →ₐ[V] V).comp (jetSubstPS (m := m) φ) = jetAug := by
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ hφ, GaugeR.jetAug_psJet, hφ, aug_X]

theorem exists_coord {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    (hx' : GlobalTheory.PowGerm.IsUnivJ G κ' x') :
    ∃ φ : κ → MvPowerSeries κ' V, (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) ∧
      ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m := by
  have h := fun m => (hx.2.2 (Jet V κ' m) jetAug m (ExpUniqLoc.ker_aug_pow le_rfl) (x' m) (hx'.2.1 m)).exists
  choose ψ hψa hψ using h
  have hc : ∀ m, (jetTrunc : Jet V κ' (m + 1) →ₐ[V] Jet V κ' m).comp (ψ (m + 1)) =
      (ψ m).comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) := by
    intro m
    refine uniq hx (jetAug : Jet V κ' m →ₐ[V] V) (m + 1) (ExpUniqLoc.ker_aug_pow (by omega)) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, ExpUniqLoc.aug_comp_trunc, hψa]
    · rw [← AlgHom.comp_assoc, hψa, ExpUniqLoc.aug_comp_trunc]
    · rw [← GermD.homAt_comp, ← GermD.homAt_comp, Category.assoc, Category.assoc, hx.1, ← hψ, ← hψ, hx'.1]
  have hs := fun i : κ => GaugeR.exists_ps_of_compat
    (fun m => ψ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) (fun m => DFunLike.congr_fun (hc m) _)
  choose φ hφ using hs
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := by
    intro i
    rw [← GaugeR.jetAug_psJet 0, hφ, ← AlgHom.comp_apply, hψa, aug_X]
  refine ⟨φ, h0, fun m => ?_⟩
  have : jetSubstPS (m := m) φ = ψ m := by
    apply GermD.jet_hom_ext
    intro i
    rw [ExpChartJet.jetSubstPS_mk m φ h0, hφ]
  rw [this]
  exact hψ m

theorem subst_eq_X {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    {φ : κ → MvPowerSeries κ' V} (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m)
    {φi : κ' → MvPowerSeries κ V} (h0i : ∀ i, MvPowerSeries.constantCoeff (φi i) = 0)
    (hφi : ∀ m, x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φi) ≫ x' m) (i : κ) :
    MvPowerSeries.subst φi (φ i) = MvPowerSeries.X i := by
  apply GermFun.psJet_inj
  intro m
  have e : (jetSubstPS (m := m) φi).comp (jetSubstPS (m := m) φ) = AlgHom.id V _ := by
    refine uniq hx (jetAug : Jet V κ m →ₐ[V] V) m (ExpUniqLoc.ker_aug_pow le_rfl) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, aug_comp_subst m φi h0i, aug_comp_subst m φ h0]
    · rfl
    · rw [← GermD.homAt_comp, Category.assoc, ← hφ, ← hφi, GermD.homAt_id, Category.id_comp]
  have e' := DFunLike.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ h0, ExpChartJet.jetSubstPS_psJet m φi h0i] at e'
  rw [e', ← MvPolynomial.coe_X]
  exact (GaugeR.psJet_eq_mk m _ _ fun e _ => (MvPolynomial.coeff_coe _ _).symm).symm

end GlobalTheory.ChartCmp.Coord

namespace GlobalTheory.ChartCmp

theorem exists_coordRel_of_isUnivJ : ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x' → ∃ φ φi : Pt V 1 d, IsInvPair φ φi ∧ CoordRel x x' φ ∧ CoordRel x' x φi := by
  intro V _ G _ d x x' hx hx'
  obtain ⟨φ, h0, hφ⟩ := Coord.exists_coord hx hx'
  obtain ⟨φi, h0i, hφi⟩ := Coord.exists_coord hx' hx
  have key : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V, (fun p : Fin 1 × Fin d => f (0, p.2)) = f := by
    intro f
    funext p
    rw [show ((0 : Fin 1), p.2) = p from Prod.ext (Subsingleton.elim _ _) rfl]
  have key2 : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V,
      (fun p : Fin 1 × Fin d => (![fun j => f (0, j)] : Fin 1 → Pt V 1 d) p.1 p.2) = f := by
    intro f
    funext p
    obtain ⟨a, b⟩ := p
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun j => φ (0, j), fun j => φi (0, j), ⟨fun i => h0 _, fun i => h0i _, ?_, ?_⟩, fun m => ?_, fun m => ?_⟩
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx h0 hφ h0i hφi _
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx' h0i hφi h0 hφ _
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φ (0, p.2)), key]
    exact hφ m
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φi (0, p.2)), key]
    exact hφi m

end GlobalTheory.ChartCmp
