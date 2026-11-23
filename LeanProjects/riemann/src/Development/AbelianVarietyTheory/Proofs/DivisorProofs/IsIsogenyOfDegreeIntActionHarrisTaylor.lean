import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLTorsionEqPowOfTateSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeOfFibreRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFinrankEqNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismFiniteOfGeometricFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteFlatGeometricFibresOverBaseStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTTors

theorem isIsogDeg_of_geomFibres (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (φ : A ⟶ A)
    (d : ℕ) (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
      GlobalTheory.IwLevel.IsIsogDeg ((Over.pullback t).map φ) d) : GlobalTheory.IwLevel.IsIsogDeg φ d := by
  have := hA.smooth
  have hfin : IsFinite φ.left := GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres S A hA φ fun k _ _ t => (h k t).fin
  have hflat : Flat φ.left :=
    GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base S A A φ inferInstance inferInstance inferInstance hfin fun k _ _ t => (h k t).flat
  refine ⟨hfin, hflat, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres φ fun k _ _ t => (h k t).surj, fun y => ?_⟩
  let K := AlgebraicClosure (A.left.residueField y)
  let u : Sp K ⟶ A.left := spMap (algebraMap (A.left.residueField y) K) ≫ A.left.fromSpecResidueField y
  let t := u ≫ A.hom
  let q : Sp K := (⊥ : PrimeSpectrum K)
  let v : Sp K ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hP := GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hP (v q)
  have hv : pullback.fst A.hom t (v q) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst A.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply y _)
  rw [hv] at e
  rw [← e]
  exact (h K t).rank _

theorem isIsogDeg_fibre (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A)
    (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ) (hl : l.Prime) (hl0 : (l : k) ≠ 0)
    (hcard : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F))
    (c : 𝓞 F) (hc : c ≠ 0) : GlobalTheory.IwLevel.IsIsogDeg (ρ.act c) ((Algebra.norm ℤ c).natAbs ^ d) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow k A hA F ρ l d hl hl0 hcard c hc
  exact GlobalTheory.T.isogeny_degree_of_fibre_rank k A hA _ (ρ.hom c) h1 _ h2

def pullAct {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {S : Scheme.{0}} {A : Over S} [GrpObj A]
    [IsCommMonObj A] (act : GlobalTheory.UPel.HT.OActN D.O A) {T : Scheme.{0}} (t : T ⟶ S) :
    OAct (𝓞 D.F) ((Over.pullback t).obj A) where
  act c := (Over.pullback t).map (act.act (algebraMap (𝓞 D.F) D.O c))
  hom c := by have := act.hom (algebraMap (𝓞 D.F) D.O c); infer_instance
  one := by rw [map_one, act.one, CategoryTheory.Functor.map_id]
  mul a b := by rw [mul_comm a b, map_mul, act.mul, Functor.map_comp]
  add a b := by
    rw [map_add, act.add]
    exact map_mul (Over.pullback t).homMonoidHom _ _

theorem isIsogDeg_intAct : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (c : 𝓞 D.F),
    c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n)) := by
  intro p _ D R _ b N S s o c hc
  refine isIsogDeg_of_geomFibres S o.A o.ab _ _ fun k _ _ t => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ s)
  have hβ : t ≫ s = spMap φ.hom := by rw [← hφ]; rfl
  obtain ⟨I, -⟩ := o.geom k t φ.hom hβ
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hlp' : l ≠ p := by omega
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out)).2 hlp'
  have hl0 : (l : k) ≠ 0 := by
    have := (b.unit l hcop).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hcount := GlobalTheory.T.card_lTorsion_eq_pow_of_tateSimilitude p D k _ _ _ I l hl hlp'
  let e := GlobalTheory.TorsionLift.ptsEquiv t o.A (𝟙_ (Over (Sp k))) t (Category.id_comp t)
  have hc2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback t).obj o.A // x ^ l = 1} =
      l ^ ((D.m * D.n) * Module.finrank ℚ D.F) := by
    rw [← hcount]
    refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
    show x ^ l = 1 ↔ e x ^ l = 1
    rw [← map_pow, map_eq_one_iff e e.injective]
  exact isIsogDeg_fibre k _ (GlobalTheory.isAbelianScheme_pullback_obj t o.A o.ab) D.F (pullAct o.act t) l _ hl hl0 hc2 c hc

end GlobalTheory.HTTors
