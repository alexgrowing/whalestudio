import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_isGt_specialFibre (hB : GtBaseChangeSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) :
    ∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := by
  obtain ⟨E₀, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V (IsLocalRing.maximalIdeal V) D 0 G ⟨g⟩
  have hle : IsLocalRing.maximalIdeal V ^ (0 + 1) ≤ RingHom.ker (IsLocalRing.residue V) := by
    rw [zero_add, pow_one, IsLocalRing.ker_residue]
  let c : V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue V) fun a ha => (RingHom.mem_ker).1 (hle ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hB _ _ (spMap c) E₀ _ hE
  have hc : spMap c ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap (IsLocalRing.residue V) := by
    rw [show thick V (IsLocalRing.maximalIdeal V) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have gp := ((isGrpPullback_pullback (thickObj V (IsLocalRing.maximalIdeal V) 0 G) (spMap c)).comp
    (isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) 0))).congr hc rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso gp (isGrpPullback_pullback G (spMap (IsLocalRing.residue V)))
  exact ⟨E₁, isGt_of_iso e hE₁⟩

theorem utest_dim_and_split : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), u.A.g = S.g ∧ u.D.toPre.P.g + Module.finrank ℤ u.D.toPre.X = S.g ∧ SmoothOfRelativeDimension S.g u.G.hom ∧ 4 ≤ S.N ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField u.V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue u.V))).obj u.G) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hsm : SmoothOfRelativeDimension S.g u.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 (ρ.g_eq ▸ ρ.P.smoothDim)
  have hg : u.A.g = S.g :=
    H1.dim_unique u.A.A.hom u.A.smoothDim hsm (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))
  refine ⟨hg, ?_, ?_, ?_, exists_isGt_specialFibre hL.2.2.1.gtBaseChange _ _ (u.U.gt 0)⟩
  · have h := GlobalTheory.UT.dim_eq_rank_add_dim hL u.V _ hA u.D u.A u.G u.semi u.U
    rw [← hg, add_comm]
    exact h.symm
  · have := u.semi.smooth
    have := u.semi.geomConnected
    refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic u.V u.G S.g ?_
    have w : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd u.G.hom (jK u.V) := Over.w u.U.gen.hom
    have : IsIso u.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map u.U.gen.hom))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩) hsm
  · rw [ρ.N_eq]
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    exact Nat.pow_le_pow_left h₁ 2

end GlobalTheory.ZH
