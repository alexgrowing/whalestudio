import Mathlib
import GroundTheory.AutomorphicForms.GL2.GodementSectionSplit
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open scoped NumberField.AdeleRing Classical

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

variable (K) in

def integralInd : FiniteAdeleRing (𝓞 K) K → ℂ :=
  (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1

variable (K) in

def integralInd2 : (Fin 2 → FiniteAdeleRing (𝓞 K) K) → ℂ :=
  finiteTensor2 fun _ ↦ integralInd K

theorem isClopen_integralFiniteAdeles :
    IsClopen (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) :=
  ⟨AddSubgroup.isClosed_of_isOpen (integralFiniteAdeles (𝓞 K) K).toAddSubgroup
    isOpen_integralFiniteAdeles, isOpen_integralFiniteAdeles⟩

theorem integralInd_mem : integralInd K ∈ finiteSchwartzBruhat K := by
  refine ⟨?_, HasCompactSupport.intro (isCompact_integralFiniteAdeles K) fun x hx ↦
    Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ integralFiniteAdeles (𝓞 K) K
  · refine ⟨_, isClopen_integralFiniteAdeles.isOpen, hx, fun y hy ↦ ?_⟩
    simp only [integralInd, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, isClopen_integralFiniteAdeles.compl.isOpen, hx, fun y hy ↦ ?_⟩
    simp only [integralInd, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem integralInd2_mem : integralInd2 K ∈ finiteSchwartzBruhat2 K :=
  finiteTensor2_mem fun _ ↦ integralInd_mem

theorem integralInd_apply (x : FiniteAdeleRing (𝓞 K) K) :
    integralInd K x = if x ∈ integralFiniteAdeles (𝓞 K) K then 1 else 0 := by
  by_cases hx : x ∈ integralFiniteAdeles (𝓞 K) K
  · simp [integralInd, hx]
  · simp [integralInd, hx]

theorem vecMul_mem_integral_iff {k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hk : k ∈ AdelicGLn.integralFiniteGL K 2) (b : FiniteAdeleRing (𝓞 K) K) :
    (∀ j, (![0, b] ᵥ* (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) j ∈
      integralFiniteAdeles (𝓞 K) K) ↔ b ∈ integralFiniteAdeles (𝓞 K) K := by
  obtain ⟨hk1, hk2⟩ := (AdelicGLn.mem_integralFiniteGL_iff K 2).1 hk
  have hv : ∀ (x : Fin 2 → FiniteAdeleRing (𝓞 K) K) (A : Matrix (Fin 2) (Fin 2) _),
      (x ᵥ* A) = fun j ↦ x 0 * A 0 j + x 1 * A 1 j := fun x A ↦ by
    ext j; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have he : ![0, b] ᵥ* (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ᵥ*
        ((k⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) _) = ![0, b] := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.vecMul_one]
    have h1 := congrFun he 1
    rw [hv] at h1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    rw [← h1]
    exact add_mem (mul_mem (h 0) (hk2 0 1)) (mul_mem (h 1) (hk2 1 1))
  · intro hb j
    rw [hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add]
    exact mul_mem hb (hk1 1 j)

theorem integralInd2_vecMul {k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hk : k ∈ AdelicGLn.integralFiniteGL K 2) (b : FiniteAdeleRing (𝓞 K) K) :
    integralInd2 K (![0, b] ᵥ* (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) =
      integralInd K b := by
  rw [integralInd2, finiteTensor2_apply, integralInd_apply, integralInd_apply, integralInd_apply]
  have h := vecMul_mem_integral_iff hk b
  by_cases hb : b ∈ integralFiniteAdeles (𝓞 K) K
  · have h' := h.2 hb
    simp [hb, h' 0, h' 1]
  · have h' : ¬ ∀ j, (![0, b] ᵥ* (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) j ∈
        integralFiniteAdeles (𝓞 K) K := fun h'' ↦ hb (h.1 h'')
    rw [Fin.forall_fin_two] at h'
    by_cases h0 : (![0, b] ᵥ* (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) 0 ∈
        integralFiniteAdeles (𝓞 K) K
    · have h1 : (![0, b] ᵥ* (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) 1 ∉
          integralFiniteAdeles (𝓞 K) K := fun h1 ↦ h' ⟨h0, h1⟩
      simp [hb, h0, h1]
    · simp [hb, h0]

theorem hasSum_integral_finiteIdeleMeasure_of_invariant {F : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ}
    (hFi : Integrable F (finiteIdeleMeasure K))
    (hF : ∀ x, ∀ w ∈ finiteIntegralUnits K, F (x * w) = F x) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦ F c.out)
      (∫ x, F x ∂finiteIdeleMeasure K) := by
  set W := finiteIntegralUnits K
  have hWo : IsOpen (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := isOpen_finiteIntegralUnits K
  have hc : Countable ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := countable_quotient_of_isOpen hWo
  have : DiscreteTopology ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := QuotientGroup.discreteTopology hWo
  set S : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W → Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    fun c ↦ QuotientGroup.mk ⁻¹' {c}
  have hSm : ∀ c, MeasurableSet (S c) := fun c ↦
    (isOpen_discrete ({c} : Set ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W))).preimage
      QuotientGroup.continuous_mk |>.measurableSet
  have hSW : ∀ c, S c = (fun b ↦ c.out⁻¹ * b) ⁻¹' (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    intro c
    ext b
    simp only [S, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [eq_comm, QuotientGroup.eq]
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro c d hcd
    refine Set.disjoint_left.2 fun p hp hq ↦ hcd ?_
    exact hp.symm.trans hq
  have hu : ⋃ c, S c = Set.univ :=
    Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨(p : _ ⧸ W), rfl⟩
  have h := hasSum_integral_iUnion hSm hd hFi.integrableOn
  rw [hu, Measure.restrict_univ] at h
  have hval : ∀ c, ∫ x in S c, F x ∂finiteIdeleMeasure K = F c.out := by
    intro c
    have hconst : ∀ b ∈ S c, F b = F c.out := by
      intro b hb
      rw [hSW c] at hb
      have hb' : c.out⁻¹ * b ∈ W := hb
      have := hF c.out _ hb'
      rwa [mul_inv_cancel_left] at this
    rw [setIntegral_congr_fun (hSm c) hconst, setIntegral_const, Measure.real, hSW c,
      measure_preimage_mul, finiteIdeleMeasure_finiteIntegralUnits]
    simp
  simp only [hval] at h
  exact h

end

end GroundTheory.Automorphic.GodementSection
