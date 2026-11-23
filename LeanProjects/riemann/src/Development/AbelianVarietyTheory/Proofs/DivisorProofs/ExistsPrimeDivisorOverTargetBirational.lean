import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hb E'
  have e := GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s
  have hc : ∀ a, Cartier.constFn p a ∈ E'.ring.comap (functionFieldMap s) := fun a => by
    show functionFieldMap s (Cartier.constFn p a) ∈ E'.ring
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  let ψ : E'.ring.comap (functionFieldMap s) →+* E'.ring :=
    (functionFieldMap s).restrict _ E'.ring fun _ hx => hx
  have hψb : Function.Bijective ψ := by
    refine ⟨fun x y h => Subtype.ext (hb.1 (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hb.2 (y : Y.functionField)
    exact ⟨⟨x, show functionFieldMap s x ∈ E'.ring from hx ▸ y.2⟩, Subtype.ext hx⟩
  let eq : E'.ring.comap (functionFieldMap s) ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  have hdvr : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap s)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eq.symm
  have hcomp : eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem) =
      (Cartier.constFn p).codRestrict _ hc := by
    refine RingHom.ext fun a => eq.injective ?_
    rw [RingHom.comp_apply]
    erw [RingEquiv.apply_symm_apply]
    exact Subtype.ext (RingHom.congr_fun e a).symm
  have hess : ((Cartier.constFn p).codRestrict _ hc).EssFiniteType := by
    rw [← hcomp]
    have h1 := E'.essFiniteType
    letI := ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem).toAlgebra
    letI := (eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem)).toAlgebra
    haveI : Algebra.EssFiniteType k E'.ring := h1
    let f : E'.ring →ₐ[k] E'.ring.comap (functionFieldMap s) :=
      { eq.symm.toRingHom with commutes' := fun _ => rfl }
    exact Algebra.EssFiniteType.of_surjective f eq.symm.surjective
  exact ⟨⟨E'.ring.comap (functionFieldMap s), hc, hdvr, hess⟩, fun _ => Iff.rfl⟩

end GlobalTheory.Discrepancy
