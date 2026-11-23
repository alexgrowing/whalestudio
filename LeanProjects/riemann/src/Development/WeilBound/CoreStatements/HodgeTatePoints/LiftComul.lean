import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (spMap_comp spMap_id)

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

omit [GrpObj G] in
theorem spc {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap (ψ.comp φ) ≫ y = spMap ψ ≫ spMap φ ≫ y := by
  rw [← Category.assoc, spMap_comp]

omit [GrpObj G] in
theorem spc' {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap ψ ≫ spMap φ ≫ y = spMap (ψ.comp φ) ≫ y := (spc ψ φ y).symm

theorem tors_pow (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] (φ : T.A →ₐ[R] S) :
    (spMap φ ≫ T.y) ^ p = 1 := by
  rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]

theorem tors_ext (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] {φ φ' : T.A →ₐ[R] S}
    (h : spMap φ ≫ T.y = spMap φ' ≫ T.y) : φ = φ' := by
  exact (T.univ S _ (tors_pow T φ)).unique rfl h.symm

theorem lift_comul (T : TorsRep G p) (Δ : T.A →ₐ[R] TensorProduct R T.A T.A)
    (hΔ : spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y))
    {S : Type} [CommRing S] [Algebra R S] (F : TensorProduct R T.A T.A →ₐ[R] S) :
    spMap (F.comp Δ) ≫ T.y = (spMap (F.comp Algebra.TensorProduct.includeLeft) ≫ T.y) *
      (spMap (F.comp Algebra.TensorProduct.includeRight) ≫ T.y) := by
  rw [spc, hΔ, MonObj.comp_mul, spc', spc']

end

theorem tors_alg : ∀ (R : Type) [CommRing R] (p : ℕ), ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ T : TorsRep G p, ∃ (Δ : T.A →ₐ[R] TensorProduct R T.A T.A) (ε : T.A →ₐ[R] R) (s : T.A →ₐ[R] T.A), spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) ∧ spMap ε ≫ T.y = 1 ∧ (spMap s ≫ T.y) * T.y = 1 ∧ (Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp ((Algebra.TensorProduct.map Δ (AlgHom.id R T.A)).comp Δ) = (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp Δ ∧ (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp Δ = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp Δ = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp Δ = (Algebra.ofId R T.A).comp ε ∧ (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp Δ = Δ := by
  intro R _ p G _ _ T
  set iL : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeLeft with hiL
  set iR : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeRight with hiR
  have hz : ((spMap iL ≫ T.y) * (spMap iR ≫ T.y)) ^ p = 1 := by
    rw [mul_pow, tors_pow, tors_pow, _root_.one_mul]
  obtain ⟨Δ, hΔ, -⟩ := T.univ _ _ hz
  obtain ⟨ε, hε, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  have hz' : (T.y⁻¹) ^ p = 1 := by rw [inv_pow, T.y_p, inv_one]
  obtain ⟨s, hs, -⟩ := T.univ T.A _ hz'
  refine ⟨Δ, ε, s, hΔ, hε, by rw [hs, _root_.inv_mul_cancel], ?_, ?_, ?_, ?_, ?_⟩
  · apply tors_ext T
    rw [← AlgHom.comp_assoc, lift_comul T Δ hΔ, lift_comul T Δ hΔ]
    have e1 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iL = ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp Δ := by
      ext x; simp [hiL]
    have e2 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iR := by
      ext x; simp [hiR, Algebra.TensorProduct.one_def]
    have e3 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL]
    have e4 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp Δ := by
      ext x; simp [hiR]
    have e5 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL, Algebra.TensorProduct.one_def]
    have e6 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iL := by
      ext x; simp [hiL, hiR, Algebra.TensorProduct.one_def]
    rw [e1, e2, lift_comul T Δ hΔ, e5, e6, e3, e4, lift_comul T Δ hΔ, _root_.mul_assoc]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iL = (Algebra.TensorProduct.includeLeft : R →ₐ[R] TensorProduct R R T.A).comp ε := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iR = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.one_mul]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iL = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iR = (Algebra.TensorProduct.includeRight : R →ₐ[R] TensorProduct R T.A R).comp ε := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.mul_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iL = s := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iR = AlgHom.id R T.A := by
      ext x; simp [hiR]
    rw [e1, e2, spMap_id, Category.id_comp, hs, _root_.inv_mul_cancel, spc, hε, MonObj.comp_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ, hΔ]
    have e1 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iL = iR := by
      ext x; simp [hiL, hiR]
    have e2 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iR = iL := by
      ext x; simp [hiL, hiR]
    rw [e1, e2, _root_.mul_comm]

end PositivityTheory.HtPt.Rf
