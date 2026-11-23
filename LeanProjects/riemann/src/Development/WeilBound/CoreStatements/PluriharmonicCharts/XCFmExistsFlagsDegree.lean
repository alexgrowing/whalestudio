import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AdjoinLow
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

set_option synthInstance.maxHeartbeats 400000 in
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem PositivityTheory.Xgp.c_fm_exists_flags_degree.core {F₀ Ω G I : Type} [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω]
    [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] [Algebra.IsAlgebraic F₀ Ω] (x : I → G)
    (hx : AlgebraicIndependent Ω x) (hx₀ : AlgebraicIndependent F₀ x)
    (ht : IntermediateField.adjoin Ω (Set.range x) = ⊤) :
    Module.finrank (IntermediateField.adjoin F₀ (Set.range x)) G = Module.finrank F₀ Ω := by
  letI : Algebra (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) :=
    FractionRing.liftAlgebra _ _
  haveI : IsScalarTower (MvPolynomial I F₀) (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have h := Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R := F₀) (S := Ω) I
  rw [Cardinal.lift_id] at h
  have h' : Module.finrank (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) =
      Module.finrank F₀ Ω := congrArg Cardinal.toNat h
  rw [← h']
  let j : FractionRing (MvPolynomial I Ω) ≃ₐ[Ω] G :=
    hx.aevalEquivField.trans ((IntermediateField.equivOfEq ht).trans IntermediateField.topEquiv)
  have hj : ∀ a, j (algebraMap (MvPolynomial I Ω) _ a) = MvPolynomial.aeval x a :=
    fun a => hx.aevalEquivField_algebraMap_apply_coe a
  refine (Algebra.finrank_eq_of_equiv_equiv hx₀.aevalEquivField.toRingEquiv j.toRingEquiv ?_).symm
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial I F₀)) (RingHom.ext fun a => ?_)
  show ((hx₀.aevalEquivField (algebraMap _ _ a) : _) : G) =
    j (algebraMap (FractionRing (MvPolynomial I F₀)) _ (algebraMap (MvPolynomial I F₀) _ a))
  rw [hx₀.aevalEquivField_algebraMap_apply_coe, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (MvPolynomial I F₀) (MvPolynomial I Ω), hj]
  exact (MvPolynomial.aeval_map_algebraMap Ω x a).symm

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_degree : ∀ (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (d : ℕ), 0 < d → Module.finrank F₀ Ω = d → IsGenFam Ω G u → AlgebraicIndependent F₀ (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin F₀ (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) G = d := by
  intro F₀ Ω G _ _ _ _ _ _ _ S _ r u d hd hr hu
  haveI : Module.Finite F₀ Ω := Module.finite_of_finrank_pos (hr ▸ hd)
  have h₀ := hu.2.2.1.restrictScalars (R := F₀) (algebraMap F₀ Ω).injective
  refine ⟨h₀, ?_⟩
  rw [PositivityTheory.Xgp.GenFam.adjoin_low F₀ u hu.1 hu.2.1, ← hr]
  refine PositivityTheory.Xgp.c_fm_exists_flags_degree.core _ hu.2.2.1 h₀ ?_
  rw [← PositivityTheory.Xgp.GenFam.adjoin_low Ω u hu.1 hu.2.1]
  exact hu.2.2.2
