import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
namespace GlobalTheory.WeilL2Words
open NumberField IsDedekindDomain

theorem adeleOfMixedSpaceComponent_add (F : Type) [Field F] [NumberField F] (z w : mixedEmbedding.mixedSpace F) :
    arch1 F (z + w) = arch1 F z + arch1 F w :=
  Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z w) (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem mul_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    a * arch1 F z = arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * z) := by
  refine Prod.ext ?_ ?_
  · change a.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

theorem adeleOfMixedSpaceComponent_zero (F : Type) [Field F] [NumberField F] : arch1 F 0 = 0 :=
  Prod.ext (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) rfl

theorem add_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (a + arch1 F z).1 = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 + z ∧
    (a + arch1 F z).2 = a.2 := by
  constructor
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = _
    rw [map_add, RingEquiv.apply_symm_apply]
  · exact add_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

def arch1Hom (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →+ AdeleRing (𝓞 F) F where
  toFun := arch1 F
  map_zero' := adeleOfMixedSpaceComponent_zero F
  map_add' := adeleOfMixedSpaceComponent_add F

theorem adeleOfMixedSpaceComponent_finsetSum (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (z : ι → mixedEmbedding.mixedSpace F) :
    arch1 F (∑ i ∈ s, z i) = ∑ i ∈ s, arch1 F (z i) :=
  map_sum (arch1Hom F) z s

theorem dotProduct_arch (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : κ → AdeleRing (𝓞 F) F)
    (y : κ → mixedEmbedding.mixedSpace F) :
    a ⬝ᵥ arch F y = arch1 F (∑ k, InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 * y k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  exact Finset.sum_congr rfl fun k _ => mul_arch1' F (a k) (y k)

theorem fst_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (arch1 F z).1 = z :=
  RingEquiv.apply_symm_apply _ z

theorem dS_sum_pureA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro F _ _ _ κ _ ψ hψ m g f h
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Complex.ofRealCLM.toLinearMap.comp (ℓ.comp M))
  have hL : ∀ X, L X = ((ℓ (∑ k, X k * h.2 k) : ℝ) : ℂ) := by
    intro X
    simp [L, M]
  have hg : (fun X => (2 * Real.pi * Complex.I) * L X).HasTemperateGrowth :=
    ((2 * Real.pi * Complex.I) • L).hasTemperateGrowth
  refine ⟨fun i => SchwartzMap.smulLeftCLM ℂ (fun X => (2 * Real.pi * Complex.I) * L X) (f i) +
    LineDeriv.lineDerivOp h.1 (f i), ?_⟩
  funext a
  set X : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 with hX
  set Y : κ → FiniteAdeleRing (𝓞 F) F := fun k => (a k).2 with hY
  set c : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 with hc
  set A : ℝ := ℓ (∑ k, X k * h.2 k) with hA
  set B : ℝ := ℓ (c * ∑ k, h.1 k * h.2 k) with hB
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) *
        ∑ i, f i (X + t • h.1) * g i Y := by
    funext t
    unfold GlobalTheory.WeilM.schr
    congr 1
    · have e0 : (archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2 =
          arch1 F (∑ k, (t • h.1) k * (t • h.2) k) := by
        rw [archPair, dotProduct_arch]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (· * (t • h).2 k) (fst_arch1 F ((t • h).1 k))
      have e1 : a ⬝ᵥ (archPair F (t • h)).2 + ⅟(2 : AdeleRing (𝓞 F) F) * ((archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2)
          = arch1 F (t • (∑ k, X k * h.2 k) + t ^ 2 • (c * ∑ k, h.1 k * h.2 k)) := by
        rw [e0, mul_arch1', archPair, dotProduct_arch, ← adeleOfMixedSpaceComponent_add]
        congr 1
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, Finset.smul_sum,
          Finset.mul_sum, smul_smul, pow_two]
        rfl
      rw [e1, hℓ, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hx : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((a + (archPair F (t • h)).1) k).1) = X + t • h.1 :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).1
      have hy : (fun k => ((a + (archPair F (t • h)).1) k).2) = Y :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).2
      unfold GlobalTheory.WeilM.pureA
      rw [hx, hy]

  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((f i).hasFDerivAt (X + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add X)).mul_const (g i Y))
  have hT := hφ.cexp.fun_mul hS
  unfold dS
  rw [key]
  refine (HasDerivAt.deriv hT).trans ?_
  simp only [Finset.sum_apply, GlobalTheory.WeilM.pureA, SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  simp only [hL, ← hA]
  simp only [← hX, ← hY, ← hA, id, zero_smul, add_zero, one_smul, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, Function.comp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [show ((0:ℝ) ^ (2 - 1)) = 0 by norm_num, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  ring
end GlobalTheory.WeilL2Words
