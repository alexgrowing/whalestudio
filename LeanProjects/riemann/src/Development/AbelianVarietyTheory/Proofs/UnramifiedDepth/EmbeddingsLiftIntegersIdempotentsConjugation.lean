import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem existsUnique_lift_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {OE : Type} [CommRing OE] [Module.Finite ℤ OE]
    (τ : OE →+* C) : ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ := by
  have h : ∀ x : OE, ∃ y : O, algebraMap O C y = τ x := fun x => by
    have h1 : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    have h2 : IsIntegral ℤ (τ x) := h1.map τ.toIntAlgHom
    have h3 : IsIntegral O (τ x) := h2.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h3)
  choose f hf using h
  refine ⟨{ toFun := f
            map_one' := hv.hom_inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hv.hom_inj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hv.hom_inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hv.hom_inj (by rw [hf, map_add, map_add, hf, hf]) }, ?_, ?_⟩
  · exact RingHom.ext hf
  · intro g hg
    refine RingHom.ext fun x => hv.hom_inj ?_
    change algebraMap O C (g x) = algebraMap O C (f x)
    rw [hf, ← hg]
    rfl

theorem embeddings_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  refine ⟨existsUnique_lift_integers hv, fun e τ he => ?_, ?_⟩
  · have h : IsIdempotentElem (tauExt τ e) := by
      unfold IsIdempotentElem
      rw [← map_mul, he]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h
  · intro _ τ x
    have h2 : sig p OE x = sigE p OE x := rfl
    refine ⟨?_, h2⟩
    rw [← h2]
    clear h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tauExt, sig]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end GlobalTheory.ChF
