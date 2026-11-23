import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def extJ (σ : L →+* ℂ) (jK : M →ₛₗ[σ.comp (algebraMap K L)] W) : L ⊗[K] M →ₛₗ[σ] W :=
  letI : Module K W := Module.compHom W (σ.comp (algebraMap K L))
  let B : L →ₗ[K] M →ₗ[K] W := LinearMap.mk₂ K (fun a m => σ a • jK m)
    (fun a a' m => by rw [map_add, add_smul])
    (fun k a m => by
      show σ (k • a) • jK m = (σ (algebraMap K L k)) • (σ a • jK m)
      rw [Algebra.smul_def, map_mul, mul_smul])
    (fun a m m' => by rw [map_add, smul_add])
    (fun k a m => by
      show σ a • jK (k • m) = (σ (algebraMap K L k)) • (σ a • jK m)
      rw [map_smulₛₗ, RingHom.comp_apply, smul_comm])
  { toFun := TensorProduct.lift B
    map_add' := map_add _
    map_smul' := fun a x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        show σ (a • b) • jK m = σ a • (σ b • jK m)
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

theorem incl_injective : Function.Injective (incl (K := K) (L := L) (M := M)) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (incl (K := K) (L := L) (M := M)) =
      ((Algebra.linearMap K L).rTensor M).comp (TensorProduct.lid K M).symm.toLinearMap := by
    ext m; simp [incl]
  rw [h2]
  exact h1.comp (TensorProduct.lid K M).symm.injective

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

def formsLOf (Comp : (LL →+* ℂ) → Type) (X : ∀ σ, Comp σ → Data E r) (la : ∀ σ c, Wt (X σ c).Ψ r)
    (rd : ∀ σ : LL →+* ℂ, C →ₛₗ[σ.comp (algebraMap K LL)] FDSec (X σ)) (V : (LL →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame (X σ k).Ψ r) (mu : ∀ σ, GA D (V σ) → ℂ)
    (hL2 : ∀ σ, JMemL2 (V σ) (σ.comp (algebraMap K LL)) (rd σ) (dict σ) (mu σ))
    (hRd : ∀ σ, RdHolCusp (σ.comp (algebraMap K LL)) (la σ) (rd σ))
    [NumberField K] (Pt : HeightOneSpectrum (𝓞 K) → Type) (nrmC : ∀ lp, Pt lp → C → ℝ)
    (h0 : ∀ lp y f, 0 ≤ nrmC lp y f) (hz : ∀ lp y, nrmC lp y 0 = 0)
    (ha : ∀ lp y f g, nrmC lp y (f + g) ≤ max (nrmC lp y f) (nrmC lp y g))
    (hs : ∀ lp y (x : K) f, nrmC lp y (x • f) = FinitePlace.mk lp x * nrmC lp y f)
    {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) (chiC : G0 →* Kˣ) :
    Formalism.IndefR.Arith.FormsL LL K (LL ⊗[K] C) (fun σ => ↥(SS (V σ) (la σ) (dict σ) (mu σ))) G0 where
  WK := LinearMap.range (incl (K := K) (L := LL) (M := C))
  Pt := Pt
  nrm lp y w := nrmC lp y ((LinearEquiv.ofInjective _ incl_injective).symm w)
  nrm_nonneg lp y w := h0 lp y _
  nrm_zero lp y := by rw [map_zero]; exact hz lp y
  nrm_add lp y w w' := by rw [map_add]; exact ha lp y _ _
  nrm_smul lp y x w := by rw [map_smul]; exact hs lp y x _
  towKs := inferInstance
  ρ := rhoOf LL ρC
  chi := (Units.map (algebraMap K LL).toMonoidHom).comp chiC
  j σ := extJ σ (jSS (V σ) (σ.comp (algebraMap K LL)) (la σ) (rd σ) (dict σ) (mu σ) (hL2 σ) (hRd σ))

def mapX {WL : Type} [AddCommGroup WL] [Module LL WL] [Module K WL] [NumberField K]
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] {G0 : Type} [Group G0]
    (A : Formalism.IndefR.Arith.FormsL LL K WL W G0) (u : ∀ σ, W σ ≃ₗ[ℂ] W' σ) :
    Formalism.IndefR.Arith.FormsL LL K WL W' G0 :=
  { A with j := fun σ => (u σ).toLinearMap.comp (A.j σ) }

def BaseEmbeddingInclusion (F : IntermediateField ℚ ℂ) [Algebra F LL] (σ₀ : LL →+* ℂ) : Prop :=
  ∀ x : F, σ₀ (algebraMap F LL x) = (x : ℂ)

end Forms

end Formalism.L2.Pj
