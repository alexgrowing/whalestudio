import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRigiditySndEqZeroCanonicalChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Rigid

theorem isLocalHom_of_fst {R : Type} [CommRing R] [IsLocalRing R] {k : Type} [Field k] (θ : R →+* DualNumber k)
    (h : ∀ r ∈ maximalIdeal R, (θ r).fst = 0) : IsLocalHom θ := by
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  have hm : r ∈ maximalIdeal R := (mem_maximalIdeal r).mpr hn
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, h r hm] at hr
  exact not_isUnit_zero hr

end GlobalTheory.UCanon.Rigid

theorem GlobalTheory.UCanon.isRigid_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hmax hs hc
  have hbase := GlobalTheory.T.base_rigidity_tangent_vector_constant Xo c φ R hB C Cn k ρ a hc
  have htor := GlobalTheory.T.torus_rigidity_snd_eq_zero_canonicalChart Xo c φ R hB C Cn k ρ a hc hbase
  have h₁ : IsLocalHom ρ := GlobalTheory.UCanon.Rigid.isLocalHom_of_fst ρ hmax
  have h₂ : IsLocalHom (GlobalTheory.RigChart.constHom ρ) := by
    refine GlobalTheory.UCanon.Rigid.isLocalHom_of_fst _ fun r hr => ?_
    simp [GlobalTheory.RigChart.constHom, hmax r hr]
  have hψ : ρ.comp Cn.ψ = (GlobalTheory.RigChart.constHom ρ).comp Cn.ψ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      have := congrArg (fun f => f x) hbase
      simpa [GlobalTheory.RigChart.constHom] using this
    · rintro (i | j)
      · simp [GlobalTheory.RigChart.constHom, Cn.bd, hs]
      · apply TrivSqZeroExt.ext
        · simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
        · simpa [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl] using htor j
  have heq := GlobalTheory.TChart.cuniq _ R (DualNumber k) Cn.ψ Cn.compl ρ (GlobalTheory.RigChart.constHom ρ) h₁ h₂ hψ
  intro r
  rw [heq]
  simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
