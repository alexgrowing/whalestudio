import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.Vanishing

namespace GlobalTheory.HSShort

variable {F : Type} [Field F] [NumberField F]

abbrev Tot (G : Geo F) : Type := ∀ j, G.Sec j

def shiftAt (G : Geo F) (u : Fin G.N → F) : ∀ j, Tot G →ₗ[F] G.Sec j
  | 0 => 0
  | j + 1 => G.mulW j u ∘ₗ LinearMap.proj j

def shift (G : Geo F) : (Fin G.N → F) →ₗ[F] Module.End F (Tot G) where
  toFun u := LinearMap.pi (shiftAt G u)
  map_add' u v := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]
  map_smul' c u := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]

def incl (X : Data F) (j : ℕ) : X.V j →ₗ[F] Tot X.toGeo := LinearMap.single F _ j ∘ₗ (X.V j).subtype

theorem incl_injective (X : Data F) (j : ℕ) : Function.Injective (incl X j) := fun a b h =>
  Subtype.ext (by simpa [incl] using congrFun h j)

def inclEquiv (X : Data F) (j : ℕ) : X.V j ≃ₗ[F] LinearMap.range (incl X j) := LinearEquiv.ofInjective _ (incl_injective X j)

def sysOf (X : Data F) (Λ₀ : ℝ) : Sys F (Tot X.toGeo) where
  N := X.N
  n := X.n
  D := X.D
  T := X.T
  w := X.w
  fr := X.A
  mul := shift X.toGeo
  V j := LinearMap.range (incl X j)
  M j := (X.M j).map ((inclEquiv X j).toLinearMap.restrictScalars (𝓞 F))
  nm j := comap (X.nm j) (inclEquiv X j).symm.toLinearMap (inclEquiv X j).symm.injective
  beta := X.beta
  abelian₂ := X.abelian₂
  Lam0 := Λ₀
  LamD := X.LamD
  LamT := X.LamT

def totExt (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    Tot G →ₛₗ[algebraMap F E] Tot (G.baseChange E) where
  toFun x j := G.toExt E j (x j)
  map_add' x y := funext fun j => map_add _ _ _
  map_smul' c x := funext fun j => map_smulₛₗ (G.toExt E j) c (x j)

section Split

variable {X : Data F} {s : Fin X.D → Fin X.N → F} {hs : X.IsGood s} {δ : ℕ}

def totRes (Co : Coord X.toGeo hs δ) : Tot X.toGeo →ₗ[F] (Fin δ → F) :=
  (Co.ev 0).toLinearMap ∘ₗ hs.res 0 ∘ₗ LinearMap.proj 0

variable (X s) in

def totFil (a : ℕ) : Submodule F (Tot X.toGeo) := (filV X s a).map (incl X X.T)

def totSym (Co : Coord X.toGeo hs δ) (a : ℕ) : totFil X s a →ₗ[F] (MonoDeg (Fin X.D) a × Fin δ → F) :=
  symV Co a ∘ₗ (Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)).symm.toLinearMap

end Split

example (G : Geo F) (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

end GlobalTheory.HSShort
