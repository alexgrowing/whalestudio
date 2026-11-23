import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLawsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexPrimeMemNonunits

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ArcWitness

theorem mem_valuationSubring_of_pow_mem {K : Type} [Field K] (V : ValuationSubring K) {x : K} {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ∈ V) : x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rwa [map_pow, pow_le_one_iff hn] at h

def restrictArcIn {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {c : Coeff l} {O k : Type} [CommRing O] [CommRing k] [IsDomain k] (β : O →+* c.F) {bF : c.F →+* k}
    (a : ArcIn D l (RingHom.id c.F) k bF) : ArcIn D l β k (bF.comp β) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom F _ _ _ r z hr hz := a.geom F (β r) (β z) hr hz

theorem exists_arcWit : PartI → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (bF : c.F →+* ℂ) (_ : Algebra (FractionRing ℂ) ℂ) (_ : IsScalarTower ℂ (FractionRing ℂ) ℂ) (a : ArcIn D l (c.V W₀).subtype ℂ (bF.comp (c.V W₀).subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty), bF (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 ∧ IsTypeFn H D.p D.q ty ∧ (∃ r z : c.V W₀, (((c.V W₀).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W₀).subtype z : c.F) : ℂ) = zeta l.A) ∧ χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp (c.V W₀).subtype) ∧ (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) ∧ (∀ x : Sp (PowerSeries ℂ), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ Nontrivial W.P.D.toPre.X ∧ 0 < Fu.n := by
  intro hP
  let H := HostModel.host
  let D := HostModel.hypDatum H
  have hD : 1 ≤ D.p + D.q := by simp [D]
  let Xo : ∀ l : Level H, Moduli D l := fun l => (GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level _ H D l hD).some
  obtain ⟨W₀, hW₀⟩ := GlobalTheory.exists_valuationSubring_complex_prime_mem_nonunits 2 Nat.prime_two
  obtain ⟨l₀, -, -, hi⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx _ H 5 (by norm_num)
  obtain ⟨i, -⟩ := hi 2 Nat.prime_two
  obtain ⟨Y, hY, -⟩ := hP.2 _ H D hD Xo
  have h4 := ((hY 2 W₀ Nat.prime_two hW₀).2 i).2.2
  let bF : i.c.F →+* ℂ := i.c.F.val.toRingHom
  let a := restrictArcIn (i.c.V W₀).subtype (HostModel.arcIn i.c ℂ bF)
  obtain ⟨χ, hχ, -⟩ := h4 ℂ _ 1 a (Or.inl ⟨Field.toIsField ℂ, rfl⟩)
  obtain ⟨h1, h2, h3, hA⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Model.hasArcData_iff _ _ _ _ _ _).1 hA
  obtain ⟨g, ty, hty⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist _ H D).1
  obtain ⟨Fu⟩ := GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws _ H D i.l (Xo i.l) (bF.comp (IntermediateField.inclusion i.c.le).toRingHom) g ty hD rfl hty
  haveI : FaithfulSMul ℂ ℂ := inferInstance
  refine ⟨_, _, _, _, H, D, i.l, Xo i.l, i.c, W₀, Y 2 W₀ Nat.prime_two hW₀ i, bF, FractionRing.liftAlgebra ℂ ℂ,
    FractionRing.isScalarTower_liftAlgebra ℂ ℂ, a, χ, W, g, ty, Fu, rfl, hty, ?_, h1, ?_, h2, ?_, Fu.n_pos⟩
  · have hr : H.rt0 ∈ W₀ := mem_valuationSubring_of_pow_mem W₀ two_ne_zero (by
      rw [H.sqrt_neg_disc_sq]
      exact neg_mem (natCast_mem W₀ _))
    have hz : zeta i.l.A ∈ W₀ := mem_valuationSubring_of_pow_mem W₀ i.l.A_pos.ne' (by
      rw [(HostModel.isPrimitiveRoot_zeta i.l.A_pos).pow_eq_one]
      exact one_mem W₀)
    exact ⟨⟨⟨_, HostModel.sqrtNegDisc_mem_coeffField i.c⟩, hr⟩, ⟨⟨_, HostModel.zeta_A_mem_coeff i.c⟩, hz⟩, rfl, rfl⟩
  · intro x hx
    exact h3 x (by rwa [map_one, _root_.one_mul])
  · haveI := a.nontriv
    exact W.e.injective.nontrivial

end GlobalTheory.ArcWitness
