import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointOfValuesInSmallAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseValueMemDescendedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.canon_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn
  obtain ⟨ε', τ₀, hε', hFB, hTau⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  refine ⟨Cn.N, fun k => Cn.ψ (MvPolynomial.X k), ε', τ₀, fun i => Cn.bd i, ?_, fun k => Cn.tor k, hTau, ?_⟩
  · intro i
    rw [hε', Cn.cone i]
  · intro K _ _ ev k₀ hk₀ hemb hsep
    obtain ⟨h1, h2, h3⟩ := hsep
    have hbase : ∀ a, ev ((Cn.ψ.comp MvPolynomial.C) a) ∈ k₀ :=
      GlobalTheory.T.canonicalFamily_base_value_mem_descended_point Cn.L C.P.D.toPre C.P.oD (Cn.ψ.comp MvPolynomial.C) (fun k => Cn.ψ (MvPolynomial.X k))
        (fun k => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) Cn.e Cn.data K ev k₀ hk₀ h2
    have htor := h3 Cn.L.W (Cn.ψ.comp MvPolynomial.C) hFB hbase
    have hX : ∀ k, ev (Cn.ψ (MvPolynomial.X k)) ∈ k₀ := by
      rintro (i | i)
      · have := h1 i
        simp only at this
        rw [this]; exact k₀.zero_mem
      · exact htor i
    have hall : ∀ a : MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W, ev (Cn.ψ a) ∈ k₀ := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C a => exact hbase a
      | add p q hp hq => rw [map_add, map_add]; exact k₀.add_mem hp hq
      | mul_X p k hp => rw [map_mul, map_mul]; exact k₀.mul_mem hp (hX k)
    have hft : ((MvPolynomial.C : Cn.L.W →+* MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W).comp Cn.L.b).EssFiniteType := by
      refine RingHom.EssFiniteType.comp Cn.L.ft ?_
      exact (RingHom.FiniteType.essFiniteType (by
        rw [← MvPolynomial.algebraMap_eq]
        exact RingHom.finiteType_algebraMap.mpr inferInstance))
    exact GlobalTheory.T.closedPoint_of_values_in_small_algClosed c.F (MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W) R K (MvPolynomial.C.comp Cn.L.b) hft Cn.ψ Cn.compl
      ev k₀ hemb hall
