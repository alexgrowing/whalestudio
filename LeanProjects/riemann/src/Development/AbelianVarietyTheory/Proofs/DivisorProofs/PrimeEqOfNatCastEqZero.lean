import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem prime_eq_of_natCast_eq_zero {K : Type*} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : (p : K) = 0) (h2 : (q : K) = 0) : p = q := by
  have a := ringChar.dvd h1
  have b := ringChar.dvd h2
  have hne : ringChar K ≠ 1 := CharP.ringChar_ne_one
  have e1 := (hp.eq_one_or_self_of_dvd _ a).resolve_left hne
  have e2 := (hq.eq_one_or_self_of_dvd _ b).resolve_left hne
  rw [← e1, ← e2]

theorem natCast_residueField_cPt {X : Scheme.{0}} {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ((p : ℕ) : X.residueField (y (cPt p))) = 0 := by
  let φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of (OO p)) y).hom
  have hinj := (IsLocalRing.ResidueField.map φ).injective
  refine hinj ((map_natCast _ p).trans ?_)
  exact (natCast_residueField_OO (p := p)).trans (map_zero _).symm

theorem eq_zero_of_val_cen_eq_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z) (b : Ω), b ∈ M.O (y₀ (cPt p)) → (∀ y : Sp (OO p) ⟶ M.Z, M.Cen U (y₀ (cPt p)) y → M.val (gPt p ≫ y) b = 0) → b = 0 := by
  intro o Ω _ _ _ hb M hN U hU p _ y₀ b hb0 hv
  by_contra hne
  obtain ⟨V, f, hzV, hf⟩ := hb0
  have hD : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : f = 0 := (basicOpen_eq_bot_iff f).1 (SetLike.coe_injective h)
    apply hne
    rw [← hf, ← M.res_apply V ⟨_, hzV⟩, h0, map_zero]
  have hW : ((U ⊓ M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf hU hD
  have := hb.ded
  have := hb.ft
  have := hb.char
  have : CharZero o := (RingHom.charZero_iff hb.inj).2 hb.char
  let π : M.Z ⟶ Spec (.of ℤ) := M.s ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom o))
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    refine Flat.SpecMap_iff.2 ?_
    have : FaithfulSMul ℤ o := inferInstance
    exact (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat π := inferInstance
  have := M.lft
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap (A := ℤ) (B := o)).2 hb.ft
  have : LocallyOfFiniteType π := inferInstance
  have hz : IsClosed ({y₀ (cPt p)} : Set M.Z) := isClosed_singleton_cPt y₀
  obtain ⟨p', hp', y, hy, hyW⟩ := GlobalTheory.padicAlgCl_integral_points.1 M.Z π (y₀ (cPt p)) hz _ hW
  have e : p = p' := prime_eq_of_natCast_eq_zero (Fact.out) hp'.out (natCast_residueField_cPt y₀)
    (hy ▸ natCast_residueField_cPt y)
  subst e
  have h0 := hv y ⟨hy, hyW.trans (fun _ h => h.1)⟩
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hξ : (gPt p ≫ y) w ∈ M.Z.basicOpen f := (hyW ⟨w, rfl⟩).2
  have hξV : (gPt p ≫ y) w ∈ V := M.Z.basicOpen_le f hξ
  subst hf
  exact (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w) ⟨_, RatModel.valF_mem_O hξV f⟩).2
    ((RatModel.isUnit_valF_iff hξV f).2 hξ) h0

end GlobalTheory.Poinc

end
