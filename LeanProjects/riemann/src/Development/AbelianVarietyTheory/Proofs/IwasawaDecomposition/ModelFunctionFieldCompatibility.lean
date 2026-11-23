import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ModelFn

open SmallSec

theorem ratVal_eq {Z : Scheme.{0}} [IsIntegral Z] {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (y : CxPts q σ) (f : Z.functionField) : ratVal f y = valAt y.1 f := by
  by_cases hf : RegAt (under y) f
  · exact ratVal_eq_valAt y hf
  · rw [ratVal, valAt, dif_neg hf, dif_neg hf]

theorem valAt_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint Y) ⤳ genericPoint X) {K : Type} [Field K] (y : Sp K ⟶ Y) (f : X.functionField) :
    valAt (y ≫ j) f = valAt y (fnMap j hη f) := by
  by_cases hf : RegAt (j (below y)) f
  · exact (valAt_fnMap j hη y hf).symm
  · have h₁ : ¬ RegAt (below (y ≫ j)) f := hf
    rw [valAt, valAt, dif_neg h₁, dif_neg (mt (regAt_fnMap_iff j hη).1 hf)]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y), haveI := M.ar.isIntegral; ∃ ρ : M.X.functionField ≃+* Y.Fn, (∀ (U : M.X.Opens) (hU : genericPoint M.X ∈ U) (hU' : genericPoint Y.X ∈ M.j ⁻¹ᵁ U) (s : Γ(M.X, U)), ρ (fnOf U hU s) = fnOf (M.j ⁻¹ᵁ U) hU' (M.j.app U s)) ∧ M.j (genericPoint Y.X) = genericPoint M.X ∧ (∀ (x : Y.X) (f : M.X.functionField), RegAt (M.j x) f ↔ RegAt x (ρ f)) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Y.X) (f : M.X.functionField), valAt (y ≫ M.j) f = valAt y (ρ f)) ∧ ∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))), y'.1 = y.1 ≫ M.j → ∀ f : M.X.functionField, ratVal f y' = ratVal (ρ f) y := by
  intro F _ _ Y M
  have := M.ar.isIntegral
  have := isPreimmersion_j M
  have hη := j_gen_specializes M
  refine ⟨RingEquiv.ofBijective (fnMap M.j hη) ⟨(fnMap M.j hη).injective, fnMap_surjective M.j hη⟩,
    fun U hU hU' s => fnMap_fnOf M.j hη hU hU' s,
    (hη.antisymm (genericPoint_specializes _)).eq,
    fun x f => (regAt_fnMap_iff M.j hη).symm,
    fun K _ y f => valAt_comp M.j hη y f, fun σ y y' h f => ?_⟩
  rw [ratVal_eq, ratVal_eq, h]
  exact valAt_comp M.j hη y.1 f

end GlobalTheory.TrueGeo.ModelFn
