import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models

namespace GlobalTheory.FiniteStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem aut_bar (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

@[reducible] def twist (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {S : Scheme.{0}} (t : SAB H S) : SAB H S where
  G := t.G
  semi := t.semi
  act :=
    { act := fun a => t.act.act (σ a)
      hom := fun a => t.act.hom _
      one := by rw [map_one, t.act.one]
      mul := fun a b => by rw [map_mul, t.act.mul]
      add := fun a b => by rw [map_add, t.act.add] }
  PP := t.PP
  cub := t.cub
  sym := t.sym
  adj a := by
    have := t.adj (σ a)
    rwa [← aut_bar] at this
  prim := by
    have := t.prim
    rwa [← hσ] at this

def twistCpt (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O]
    {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) : Cpt c (twist σ hσ t) β :=
  ⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, twist σ hσ C.t,
    ⟨C.m.cm, C.m.cart, C.m.base, fun a => C.m.act (σ a), C.m.lin⟩, C.ab_gen⟩

theorem exists_ext {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O]
    {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) (hβ : IsDedFrac β) (hO : Algebra.FiniteType ℤ O)
    (hs : IsFinite C.s) (γ : F →+* F) (γ₀ : O →+* O) (hγ : ∀ x, β (γ₀ x) = γ (β x)) (r : U ⟶ U)
    (hr : r ≫ c = c ≫ spMap γ) : ∃ ρ : C.X ⟶ C.X, ρ ≫ C.s = C.s ≫ spMap γ₀ ∧ C.j ≫ ρ = r ≫ C.j := by
  obtain ⟨-, h1, h2, h3, h4⟩ := C.arith_and_proOpen hβ hO
  have hj : C.j ≫ C.s = c ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have e : spMap β ≫ spMap γ₀ = spMap γ ≫ spMap β := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hγ x
  have : IsLocallyNoetherian C.X := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
    letI := β.toAlgebra
    exact (GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense).1
  obtain ⟨ρ, ⟨k1, k2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C.X U _ C.X C.j C.normal h1 h2 h3 h4
    C.s (C.s ≫ spMap γ₀) (r ≫ C.j) inferInstance (by
      rw [Category.assoc, hj, reassoc_of% hj, reassoc_of% hr, e])
  exact ⟨ρ, k2, k1⟩

end GlobalTheory.FiniteStable
