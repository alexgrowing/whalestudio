import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFiniteParts

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory
namespace GlobalTheory.WeilL2Words
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adeleJoin_archPart (a : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F (archPart F a) (fun i => (a i).2) = a := by
  funext i
  simp only [GlobalTheory.WeilCont.adeleJoin, archPart, RingEquiv.symm_apply_apply]
  rfl

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i + v i)
    rw [map_add]
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x u : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ arch F u = arch1 F (∑ i, x i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem arch_dot_arch (v u : κ → mixedEmbedding.mixedSpace F) :
    arch F v ⬝ᵥ arch F u = arch1 F (∑ i, v i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem schA_exists_sum {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem ell_half (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (z : mixedEmbedding.mixedSpace F) :
    ℓ (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * z) = ℓ z / 2 := by
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1
  have hc : c + c = 1 := by
    rw [← map_add]
    have : (⅟(2 : AdeleRing (𝓞 F) F)).1 + (⅟(2 : AdeleRing (𝓞 F) F)).1 = (⅟(2 : AdeleRing (𝓞 F) F) + ⅟2).1 := rfl
    rw [this, invOf_two_add_invOf_two]
    exact map_one _
  have h2 : ℓ (c * z) + ℓ (c * z) = ℓ z := by rw [← map_add, ← add_mul, hc, one_mul]
  linarith

theorem schr_archPair_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.schr ψ (archPair F h) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      Complex.exp (2 * Real.pi * Complex.I * ((ℓ (∑ i, x i * h.2 i) : ℂ) + (ℓ (∑ i, h.1 i * h.2 i) : ℂ) / 2)) *
        Φ (GlobalTheory.WeilCont.adeleJoin F (x + h.1) y) := by
  simp only [GlobalTheory.WeilM.schr, archPair]
  rw [adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch, mul_arch1', ← adeleOfMixedSpaceComponent_add, hℓ, map_add, ell_half]
  congr 2
  push_cast
  ring

theorem hasDerivAt_schr_pureA (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y))
      ((2 * Real.pi * Complex.I * (ℓ (∑ i, x i * h.2 i) : ℂ) * f x + fderiv ℝ f x h.1) * g y) 0 := by
  set A : ℝ := ℓ (∑ i, x i * h.2 i)
  set B : ℝ := ℓ (∑ i, h.1 i * h.2 i) / 2
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) * (f (x + t • h.1) * g y) := by
    funext t
    rw [schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin]
    congr 2
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, A, B]
    have e1 : ∑ i, x i * (t • h.2 i) = t • ∑ i, x i * h.2 i := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    have e2 : ∑ i, (t • h.1 i) * (t • h.2 i) = (t ^ 2) • ∑ i, h.1 i * h.2 i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    rw [e1, e2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := ((f.hasFDerivAt (x + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add x)).mul_const (g y)
  have hT := hφ.cexp.fun_mul hS
  refine hT.congr_deriv ?_
  simp only [id, Function.comp, zero_smul, add_zero, one_smul, zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_pow]
  ring

omit [Invertible (2 : AdeleRing (𝓞 F) F)] in
theorem schr_sum' [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) {n : ℕ} (Φ : Fin n → (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (∑ i, Φ i) = ∑ i, GlobalTheory.WeilM.schr ψ w (Φ i) := by
  funext x
  simp [GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]

theorem hasDerivAt_schr_sum (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
        (GlobalTheory.WeilCont.adeleJoin F x y))
      (∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y) 0 := by
  have e : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y)) = fun t => ∑ i, GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y) := by
    funext t
    rw [schr_sum', Finset.sum_apply]
  rw [e]
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_schr_pureA F ψ ℓ hℓ h (f i) (g i) x y

theorem differentiableAt_schr {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (a : κ → AdeleRing (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0 := by
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, -, rfl⟩ := schA_exists_sum F hΦ
  rw [← adeleJoin_archPart F a]
  exact (hasDerivAt_schr_sum F ψ ℓ hℓ h f g _ _).differentiableAt

theorem dS_sum_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y) =
      ∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y :=
  (hasDerivAt_schr_sum F ψ ℓ hℓ h f g x y).deriv

theorem dS_mem_schA {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hΦ
  obtain ⟨f', hf'⟩ := dS_sum_pureA F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

end GlobalTheory.WeilL2Words
