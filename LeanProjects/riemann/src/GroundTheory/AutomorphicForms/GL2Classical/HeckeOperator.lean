import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCosets
import GroundTheory.AutomorphicForms.GL2Classical.Automorphic
import GroundTheory.AutomorphicForms.HeckeAlgebraLevel

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped Pointwise MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ] {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem heckeAct_indicator_eq_sum {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {U : Set G} (S : Finset G) (hU : ∀ g, g ∈ U ↔ ∃ s ∈ S, s⁻¹ * g ∈ K)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s⁻¹ * t ∈ K → s = t) {v : V} (hv : v ∈ fixedVectors ρ K) :
    heckeAct μ ρ (U.indicator fun _ => (1 : ℂ)) v =
      ((μ.real (K : Set G) : ℝ) : ℂ) • ∑ s ∈ S, ρ s v := by
  have hUeq : U = ⋃ s ∈ S, s • (K : Set G) := by
    ext g
    simp only [hU, Set.mem_iUnion, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe,
      exists_prop]
  have hUc : IsCompact U := by
    rw [hUeq]; exact S.isCompact_biUnion fun s _ => hKc.smul s
  have hUo : IsOpen U := by
    rw [hUeq]; exact isOpen_biUnion fun s _ => hKo.smul s
  have hf := indicator_mem_locallyConstantCompactSupport (R := ℂ) hUc hUo (1 : ℂ)
  have hvs := smooth_of_mem_fixedVectors hKo hv
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ hf hvs φ, map_smul, map_sum]
  have hmeas : ∀ s : G, MeasurableSet (s • (K : Set G)) := fun s => (hKo.smul s).measurableSet
  have hpt : ∀ g, U.indicator (fun _ => (1 : ℂ)) g * φ (ρ g v) =
      ∑ s ∈ S, (s • (K : Set G)).indicator (fun _ => φ (ρ s v)) g := by
    intro g
    by_cases hg : g ∈ U
    · obtain ⟨s₀, hs₀, hk⟩ := (hU g).1 hg
      rw [Set.indicator_of_mem hg, one_mul, Finset.sum_eq_single s₀]
      · rw [Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hk)]
        congr 1
        conv_lhs => rw [← mul_inv_cancel_left s₀ g]
        rw [map_mul, Module.End.mul_apply, hv _ hk]
      · intro s hs hne
        refine Set.indicator_of_notMem (fun h => hne ?_) _
        have h' : s⁻¹ * g ∈ K := Set.mem_smul_set_iff_inv_smul_mem.1 h
        exact hS s hs s₀ hs₀ (by
          have := mul_mem h' (inv_mem hk)
          simpa [mul_assoc] using this)
      · intro h; exact absurd hs₀ h
    · rw [Set.indicator_of_notMem hg, zero_mul]
      refine (Finset.sum_eq_zero fun s hs => Set.indicator_of_notMem (fun h => hg ?_) _).symm
      exact (hU g).2 ⟨s, hs, Set.mem_smul_set_iff_inv_smul_mem.1 h⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_finset_sum]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_indicator_const _ (hmeas s), Measure.real, Measure.real, measure_smul,
      Complex.real_smul, smul_eq_mul]
  · intro s _
    exact (integrable_indicator_iff (hmeas s)).2
      (integrableOn_const ((hKc.smul s).measure_lt_top.ne))

end Abstract

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {k : ℤ}

theorem archLift_smul_left (f : ℍ → ℂ) {M β h : GL (Fin 2) ℝ} {c : ℝ} (hc : 0 < c)
    (hM : ∀ i j, M i j = c * β i j) (hβ : 0 < β.det.val) (hh : 0 < h.det.val) :
    archLift k f (M * h) = archLift k f (β * h) := by
  have hdetM : M.det.val = c ^ 2 * β.det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two, Matrix.det_fin_two, hM, hM, hM, hM]
    ring
  have hMpos : 0 < M.det.val := by rw [hdetM]; positivity
  have hsm : ∀ z : ℍ, M • z = β • z := by
    intro z
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos hMpos, coe_smul_of_det_pos hβ]
    simp only [num, denom, hM]
    have hd : ((β 1 0 : ℂ) * z + β 1 1) ≠ 0 := by
      have := denom_ne_zero β z
      simpa [denom] using this
    push_cast
    rw [show ((c : ℂ) * β 0 0 * z + c * β 0 1) = c * (β 0 0 * z + β 0 1) by ring,
      show ((c : ℂ) * β 1 0 * z + c * β 1 1) = c * (β 1 0 * z + β 1 1) by ring,
      mul_div_mul_left _ _ (by exact_mod_cast hc.ne')]
  have hden : ∀ z : ℂ, denom M z = c * denom β z := by
    intro z; simp only [denom, hM]; push_cast; ring
  have hdet : ∀ g : GL (Fin 2) ℝ, (g * h).det.val = g.det.val * h.det.val := fun g => by
    rw [map_mul, Units.val_mul]
  rw [archLift, archLift, hdet, hdet, hdetM, mul_smul, mul_smul, hsm, denom_mul_of_det_pos _ hh,
    denom_mul_of_det_pos _ hh, hden, mul_assoc (c ^ 2), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e : (c : ℂ) ^ k * (c : ℂ) ^ (-k) = 1 := by rw [← zpow_add₀ hc0]; simp
  push_cast
  simp only [mul_zpow]
  linear_combination ((Real.sqrt (β.det.val * h.det.val) : ℂ) ^ k * f (β • h • UpperHalfPlane.I) *
    denom β ((h • UpperHalfPlane.I : ℍ) : ℂ) ^ (-k) * denom h Complex.I ^ (-k)) * e

theorem archLift_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (h : GL (Fin 2) ℝ) :
    archLift k (∑ i ∈ s, F i) h = ∑ i ∈ s, archLift k (F i) h := by
  simp only [archLift, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]

variable (N : ℕ) [NeZero N] (p : ℕ) [NeZero p]

def classicalUpper (j : ℤ) : GL (Fin 2) ℚ where
  val := !![1, (j : ℚ); 0, p]
  inv := !![1, -j / p; 0, (p : ℚ)⁻¹]
  val_inv := by
    have := natCast_ne_zero_rat p
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  inv_val := by
    have := natCast_ne_zero_rat p
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem coe_classicalUpper (j : ℤ) :
    ((classicalUpper p j : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (j : ℚ); 0, p] := rfl

def heckeOp (N p : ℕ) [NeZero p] (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  (∑ j : Fin p, f ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ))) +
    if p ∣ N then 0 else f ∣[k] toReal (heckeAlpha p)

def heckeConst (p : ℕ) (k : ℤ) : ℂ := (p : ℂ) ^ (1 - k) * (Real.sqrt p : ℂ) ^ k

theorem heckeConst_ne_zero : heckeConst p k ≠ 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  unfold heckeConst
  refine mul_ne_zero (zpow_ne_zero _ (by exact_mod_cast hp.ne')) (zpow_ne_zero _ ?_)
  exact_mod_cast (Real.sqrt_pos.2 hp).ne'

theorem det_toReal_classicalUpper (j : ℤ) : (toReal (classicalUpper p j)).det.val = p := by
  rw [det_toReal, Matrix.GeneralLinearGroup.val_det_apply, coe_classicalUpper, Matrix.det_fin_two_of]
  simp

theorem det_toReal_heckeAlpha : (toReal (heckeAlpha p)).det.val = p := by
  rw [det_toReal, Matrix.GeneralLinearGroup.val_det_apply, coe_upperHecke, Matrix.det_fin_two_of]
  simp

theorem natCast_pos_real : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)

theorem heckeOp_add (f g : ℍ → ℂ) : heckeOp N p k (f + g) = heckeOp N p k f + heckeOp N p k g := by
  unfold heckeOp
  simp only [SlashAction.add_slash, Finset.sum_add_distrib]
  split_ifs <;> abel

theorem heckeOp_smul (c : ℂ) (f : ℍ → ℂ) : heckeOp N p k (c • f) = c • heckeOp N p k f := by
  unfold heckeOp
  have h1 : ∀ j : ℤ, 0 < (toReal (classicalUpper p j)).det.val := fun j => by
    rw [det_toReal_classicalUpper]; exact natCast_pos_real p
  have h2 : 0 < (toReal (heckeAlpha p)).det.val := by
    rw [det_toReal_heckeAlpha]; exact natCast_pos_real p
  simp only [ModularForm.smul_slash, σ_of_det_pos (h1 _), σ_of_det_pos h2]
  split_ifs <;> simp [smul_add, Finset.smul_sum]

variable [Fact p.Prime]

theorem upperHecke_injective : Function.Injective (upperHecke p) := by
  intro a b h
  have := congrArg (fun γ : GL (Fin 2) ℚ => (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) h
  simpa [coe_upperHecke] using this

theorem lowerHecke_ne_upperHecke (j : ℤ) : lowerHecke p ≠ upperHecke p j := by
  intro h
  have := congrArg (fun γ : GL (Fin 2) ℚ => (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) h
  simp only [coe_lowerHecke, coe_upperHecke] at this
  have h2 := (Fact.out : p.Prime).two_le
  have : (1 : ℚ) = p := by simpa using this
  have : (p : ℕ) = 1 := by exact_mod_cast this.symm
  omega

theorem sum_heckeReps {M : Type*} [AddCommMonoid M] (F : GL (Fin 2) ℚ → M) :
    ∑ ξ ∈ heckeReps N p, F ξ =
      (∑ j : Fin p, F (upperHecke p (-((j : ℕ) : ℤ)))) + if p ∣ N then 0 else F (lowerHecke p) := by
  classical
  have hinj : Function.Injective fun j : Fin p => upperHecke p (-((j : ℕ) : ℤ)) := by
    intro a b h
    have := upperHecke_injective p h
    exact Fin.ext (by omega)
  unfold heckeReps
  split_ifs with h
  · rw [Finset.union_empty, Finset.sum_image (fun a _ b _ hab => hinj hab), add_zero]
  · rw [Finset.sum_union, Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_singleton]
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨j, _, hj⟩
    exact lowerHecke_ne_upperHecke p _ hj.symm

theorem toReal_upperHecke_inv_apply (j : ℤ) (a b : Fin 2) :
    (toReal (upperHecke p (-j)))⁻¹ a b = (p : ℝ)⁻¹ * toReal (classicalUpper p j) a b := by
  have hp := natCast_ne_zero_rat p
  rw [← map_inv, toReal_apply, toReal_apply, coe_upperHecke_inv, coe_classicalUpper]
  fin_cases a <;> fin_cases b <;> simp <;> field_simp

theorem toReal_lowerHecke_inv_apply (a b : Fin 2) :
    (toReal (lowerHecke p))⁻¹ a b = (p : ℝ)⁻¹ * toReal (heckeAlpha p) a b := by
  have hp := natCast_ne_zero_rat p
  rw [← map_inv, toReal_apply, toReal_apply, coe_lowerHecke_inv, coe_upperHecke]
  fin_cases a <;> fin_cases b <;> simp

theorem archLift_inv_smul_mul (f : ℍ → ℂ) {M β h : GL (Fin 2) ℝ} (hM : ∀ a b, M a b = (p : ℝ)⁻¹ * β a b)
    (hβ : β.det.val = p) (hh : 0 < h.det.val) :
    archLift k f (M * h) = heckeConst p k * archLift k (f ∣[k] β) h := by
  have hp := natCast_pos_real p
  have hβpos : 0 < β.det.val := by rw [hβ]; exact hp
  rw [archLift_smul_left f (inv_pos.2 hp) hM hβpos hh]
  have key := archLift_mul_left (k := k) f hβpos hh
  rw [hβ] at key
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : (p : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 1) = 1 := by rw [← zpow_add₀ hp0]; simp
  unfold heckeConst
  push_cast at key ⊢
  linear_combination (p : ℂ) ^ (1 - k) * key - archLift k f (β * h) * e

theorem realEmb_mul_finEmb_finiteDiagonal (ξ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) :
    realEmb h * finEmb ℚ 2 (finiteDiagonal ℚ 2 ξ) =
      diagonal ℚ 2 ξ * realEmb ((toReal ξ)⁻¹ * h) * finEmb ℚ 2 1 := by
  have := diagonal_mul_realEmb_mul_finEmb 1 ξ h (finiteDiagonal ℚ 2 ξ)
  rwa [map_one, one_mul, one_mul, inv_mul_cancel] at this

theorem det_toReal_inv_mul_pos (ξ : GL (Fin 2) ℚ) (hξ : 0 < (ξ.det.val : ℚ)) {h : GL (Fin 2) ℝ}
    (hh : 0 < h.det.val) : 0 < ((toReal ξ)⁻¹ * h).det.val := by
  rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal]
  have : (0 : ℝ) < ((ξ.det.val : ℚ) : ℝ) := by exact_mod_cast hξ
  positivity

theorem det_upperHecke (j : ℤ) : ((upperHecke p j).det.val : ℚ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_upperHecke, Matrix.det_fin_two_of]; simp

theorem det_lowerHecke : ((lowerHecke p).det.val : ℚ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_lowerHecke, Matrix.det_fin_two_of]; simp

def heckeSum (φ : AdelicGL ℚ 2 → ℂ) (g : AdelicGL ℚ 2) : ℂ :=
  ∑ ξ ∈ heckeReps N p, φ (g * finEmb ℚ 2 (finiteDiagonal ℚ 2 ξ))

theorem heckeSum_adelicLift_realEmb {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) {h : GL (Fin 2) ℝ}
    (hh : 0 < h.det.val) :
    heckeSum N p (adelicLift N k f) (realEmb h) = heckeConst p k * archLift k (heckeOp N p k f) h := by
  have hterm : ∀ ξ : GL (Fin 2) ℚ, 0 < (ξ.det.val : ℚ) →
      adelicLift N k f (realEmb h * finEmb ℚ 2 (finiteDiagonal ℚ 2 ξ)) =
        archLift k f ((toReal ξ)⁻¹ * h) := fun ξ hξ => by
    rw [realEmb_mul_finEmb_finiteDiagonal]
    exact adelicLift_apply hf ξ (det_toReal_inv_mul_pos ξ hξ hh) (one_mem _)
  have hp : (0 : ℚ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  unfold heckeSum
  rw [sum_heckeReps]
  unfold heckeOp
  rw [archLift_add, archLift_sum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hterm (upperHecke p (-((j : ℕ) : ℤ))) (by rw [det_upperHecke]; exact hp)]
    exact archLift_inv_smul_mul p f (toReal_upperHecke_inv_apply p ((j : ℕ) : ℤ))
      (det_toReal_classicalUpper p ((j : ℕ) : ℤ)) hh
  · split_ifs
    · simp [archLift]
    · rw [hterm (lowerHecke p) (by rw [det_lowerHecke]; exact hp)]
      exact archLift_inv_smul_mul p f (toReal_lowerHecke_inv_apply p) (det_toReal_heckeAlpha p) hh

def finRightRep : Representation ℂ (FiniteAdelicGL ℚ 2) (AdelicGL ℚ 2 → ℂ) where
  toFun h :=
    { toFun := fun φ g => φ (g * finEmb ℚ 2 h)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ g
    simp
  map_mul' h₁ h₂ := by
    ext φ g
    simp [mul_assoc]

@[simp] theorem finRightRep_apply (h : FiniteAdelicGL ℚ 2) (φ : AdelicGL ℚ 2 → ℂ) (g : AdelicGL ℚ 2) :
    finRightRep h φ g = φ (g * finEmb ℚ 2 h) := rfl

theorem IsWeightLevel.mem_fixedVectors {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) :
    φ ∈ fixedVectors finRightRep (Gamma0Level N) := fun u hu => funext fun g => hφ.right_level g u hu

theorem heckeAct_heckeSet [MeasurableSpace (FiniteAdelicGL ℚ 2)] [BorelSpace (FiniteAdelicGL ℚ 2)]
    (μ : Measure (FiniteAdelicGL ℚ 2)) [μ.IsHaarMeasure] {φ : AdelicGL ℚ 2 → ℂ}
    (hφ : φ ∈ fixedVectors finRightRep (Gamma0Level N)) :
    heckeAct μ finRightRep ((heckeSet N p).indicator fun _ => (1 : ℂ)) φ =
      ((μ.real (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) : ℝ) : ℂ) • heckeSum N p φ := by
  classical
  rw [heckeAct_indicator_eq_sum μ (isCompact_Gamma0Level N) (isOpen_Gamma0Level N)
    ((heckeReps N p).image (finiteDiagonal ℚ 2))]
  · congr 1
    ext g
    rw [Finset.sum_image (fun a ha b hb hab => eq_of_inv_mul_mem_Gamma0Level N p ha hb
      (by rw [hab, inv_mul_cancel]; exact one_mem _))]
    simp [heckeSum, Finset.sum_apply]
  · intro g
    rw [mem_heckeSet_iff]
    simp
  · intro s hs t ht hst
    simp only [Finset.mem_image] at hs ht
    obtain ⟨ξ, hξ, rfl⟩ := hs
    obtain ⟨ξ', hξ', rfl⟩ := ht
    rw [eq_of_inv_mul_mem_Gamma0Level N p hξ hξ' hst]
  · exact hφ

theorem IsWeightLevel.heckeSum {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) :
    IsWeightLevel N k (heckeSum N p φ) where
  isLeftInvariant γ g := by
    unfold GL2Classical.heckeSum
    simp only [mul_assoc]
    exact Finset.sum_congr rfl fun ξ _ => hφ.isLeftInvariant γ _
  right_level g u hu := by
    letI : MeasurableSpace (FiniteAdelicGL ℚ 2) := borel _
    haveI : BorelSpace (FiniteAdelicGL ℚ 2) := ⟨rfl⟩
    set μ : Measure (FiniteAdelicGL ℚ 2) := Measure.haar
    have hf := indicator_mem_locallyConstantCompactSupport (R := ℂ) (isCompact_heckeSet N p)
      (isOpen_heckeSet N p) (1 : ℂ)
    have hfix := heckeAct_mem_fixedVectors (μ := μ) (ρ := finRightRep) hf
      (fun k hk x => by
        by_cases hx : x ∈ heckeSet N p
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mul_mem_heckeSet_left N p hk).2 hx)]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (fun h => hx ((mul_mem_heckeSet_left N p hk).1 h))])
      (smooth_of_mem_fixedVectors (isOpen_Gamma0Level N) hφ.mem_fixedVectors)
    rw [heckeAct_heckeSet N p μ hφ.mem_fixedVectors] at hfix
    have hpos := HeckeAlgebra.measureReal_compactOpen_pos μ (isCompact_Gamma0Level N)
      (isOpen_Gamma0Level N)
    have hne : ((μ.real (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    have := congrFun (hfix u hu) g
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, finRightRep_apply, smul_eq_mul, smul_eq_mul] at this
    exact mul_left_cancel₀ hne this
  right_kGL g w hw := by
    unfold GL2Classical.heckeSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [mul_assoc, realEmb_mul_finEmb_comm, ← mul_assoc]
    exact hφ.right_kGL _ w hw

theorem descend_heckeSum_adelicLift {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    descend k (heckeSum N p (adelicLift N k f)) = heckeConst p k • heckeOp N p k f := by
  funext z
  rw [descend, heckeSum_adelicLift_realEmb N p hf (det_borelGL_pos z), archLift_borelGL, Pi.smul_apply,
    smul_eq_mul]
  have hy : (Real.sqrt z.im : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 z.im_pos).ne'
  have e : (Real.sqrt z.im : ℂ) ^ (-k) * (Real.sqrt z.im : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hy]; simp
  linear_combination (heckeConst p k * heckeOp N p k f z) * e

theorem heckeOp_slash {f : ℍ → ℂ} (hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), heckeOp N p k f ∣[k] γ = heckeOp N p k f := by
  intro γ hγ
  have hW := (isWeightLevel_adelicLift hf).heckeSum N p
  have hd := descend_slash_eq hW γ hγ
  rw [descend_heckeSum_adelicLift N p hf] at hd
  have hc := heckeConst_ne_zero (k := k) p
  obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.1 hγ
  have hpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ s).det.val := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]; exact one_pos
  rw [ModularForm.smul_slash, σ_of_det_pos hpos] at hd
  exact smul_right_injective _ hc hd

def heckeSlash (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (k : ℤ) :
    SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k where
  toFun f :=
    { toFun := heckeOp N p k f
      slash_action_eq' := heckeOp_slash N p fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ }
  map_add' f g := SlashInvariantForm.ext fun z => by
    simp [FunLike.coe_add, heckeOp_add]
  map_smul' c f := SlashInvariantForm.ext fun z => by
    simp [FunLike.coe_smul, heckeOp_smul]

@[simp] theorem coe_heckeSlash (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (heckeSlash N p k f : ℍ → ℂ) = heckeOp N p k f := rfl

theorem heckeSum_liftEquiv (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    heckeSum N p (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) =
      heckeConst p k • (liftEquiv N k (heckeSlash N p k f) : AdelicGL ℚ 2 → ℂ) := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ
  have hW := (isWeightLevel_adelicLift hf).heckeSum N p
  rw [liftEquiv_apply, liftEquiv_apply, ← adelicLift_descend hW, descend_heckeSum_adelicLift N p hf]
  funext g
  simp only [adelicLift, Pi.smul_apply, smul_eq_mul, coe_heckeSlash]
  exact archLift_smul k _ _ _

theorem heckeAct_liftEquiv [MeasurableSpace (FiniteAdelicGL ℚ 2)] [BorelSpace (FiniteAdelicGL ℚ 2)]
    (μ : Measure (FiniteAdelicGL ℚ 2)) [μ.IsHaarMeasure]
    (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    heckeAct μ finRightRep ((heckeSet N p).indicator fun _ => (1 : ℂ)) (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) =
      (((μ.real (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) : ℝ) : ℂ) * heckeConst p k) •
        (liftEquiv N k (heckeSlash N p k f) : AdelicGL ℚ 2 → ℂ) := by
  rw [heckeAct_heckeSet N p μ (liftEquiv N k f).2.mem_fixedVectors, heckeSum_liftEquiv, smul_smul]

section Forms

open scoped Manifold

theorem mdifferentiable_sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (h : ∀ i ∈ s, MDiff (F i)) :
    MDiff (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (mdifferentiable_const : MDiff (fun _ : ℍ => (0 : ℂ)))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isBoundedAtImInfty_sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, IsBoundedAtImInfty (F i)) : IsBoundedAtImInfty (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_form_isBoundedAtImInfty : IsBoundedAtImInfty (0 : ℍ → ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isZeroAtImInfty_sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, IsZeroAtImInfty (F i)) : IsZeroAtImInfty (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem heckeOp_slash_eq (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    heckeOp N p k f ∣[k] g = (∑ j : Fin p, f ∣[k] (toReal (classicalUpper p ((j : ℕ) : ℤ)) * g)) +
      if p ∣ N then 0 else f ∣[k] (toReal (heckeAlpha p) * g) := by
  unfold heckeOp
  rw [SlashAction.add_slash, SlashAction.sum_slash]
  simp only [SlashAction.slash_mul]
  split_ifs <;> simp

theorem mdifferentiable_heckeOp {f : ℍ → ℂ} (hf : MDiff f) : MDiff (heckeOp N p k f) := by
  unfold heckeOp
  refine (mdifferentiable_sum _ fun j _ => hf.slash k _).add ?_
  split_ifs
  · exact mdifferentiable_const
  · exact hf.slash k _

theorem heckeOp_slash_mapGL (f : ℍ → ℂ) (σ : SL(2, ℤ)) :
    heckeOp N p k f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ =
      (∑ j : Fin p, f ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ) * Matrix.SpecialLinearGroup.mapGL ℚ σ)) +
        if p ∣ N then 0 else f ∣[k] toReal (heckeAlpha p * Matrix.SpecialLinearGroup.mapGL ℚ σ) := by
  rw [heckeOp_slash_eq]
  simp only [map_mul, toReal_mapGL]

variable (k)

def heckeModular (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (k : ℤ) :
    ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k where
  toFun f :=
    { toSlashInvariantForm := heckeSlash N p k f.toSlashInvariantForm
      holo' := mdifferentiable_heckeOp N p f.holo'
      bdd_at_cusps' := fun {c} hc => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
        obtain ⟨σ, rfl⟩ := hc
        rw [OnePoint.isBoundedAt_iff rfl]
        change IsBoundedAtImInfty (heckeOp N p k f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ)
        rw [heckeOp_slash_mapGL]
        refine (isBoundedAtImInfty_sum _ fun j _ => isBoundedAtImInfty_slash_toReal f _).add ?_
        split_ifs
        · exact zero_form_isBoundedAtImInfty
        · exact isBoundedAtImInfty_slash_toReal f _ }
  map_add' f g := ModularForm.ext fun z => by
    change heckeOp N p k (⇑f + ⇑g) z = heckeOp N p k f z + heckeOp N p k g z
    rw [heckeOp_add]; rfl
  map_smul' c f := ModularForm.ext fun z => by
    change heckeOp N p k (c • ⇑f) z = c • heckeOp N p k f z
    rw [heckeOp_smul]; rfl

def heckeCusp (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (k : ℤ) :
    CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k where
  toFun f :=
    { toSlashInvariantForm := heckeSlash N p k f.toSlashInvariantForm
      holo' := mdifferentiable_heckeOp N p f.holo'
      zero_at_cusps' := fun {c} hc => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
        obtain ⟨σ, rfl⟩ := hc
        rw [OnePoint.isZeroAt_iff rfl]
        change IsZeroAtImInfty (heckeOp N p k f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ)
        rw [heckeOp_slash_mapGL]
        refine (isZeroAtImInfty_sum _ fun j _ => isZeroAtImInfty_slash f _).add ?_
        split_ifs
        · exact Filter.zero_zeroAtFilter _
        · exact isZeroAtImInfty_slash f _ }
  map_add' f g := CuspForm.ext fun z => by
    change heckeOp N p k (⇑f + ⇑g) z = heckeOp N p k f z + heckeOp N p k g z
    rw [heckeOp_add]; rfl
  map_smul' c f := CuspForm.ext fun z => by
    change heckeOp N p k (c • ⇑f) z = c • heckeOp N p k f z
    rw [heckeOp_smul]; rfl

variable {k}

@[simp] theorem coe_heckeModular (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (heckeModular N p k f : ℍ → ℂ) = heckeOp N p k f := rfl

@[simp] theorem coe_heckeCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (heckeCusp N p k f : ℍ → ℂ) = heckeOp N p k f := rfl

theorem heckeModular_toSlashInvariantForm (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (heckeModular N p k f).toSlashInvariantForm = heckeSlash N p k f.toSlashInvariantForm := rfl

theorem heckeCusp_toSlashInvariantForm (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (heckeCusp N p k f).toSlashInvariantForm = heckeSlash N p k f.toSlashInvariantForm := rfl

theorem heckeAct_liftEquiv_modularForm [MeasurableSpace (FiniteAdelicGL ℚ 2)]
    [BorelSpace (FiniteAdelicGL ℚ 2)] (μ : Measure (FiniteAdelicGL ℚ 2)) [μ.IsHaarMeasure]
    (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    heckeAct μ finRightRep ((heckeSet N p).indicator fun _ => (1 : ℂ))
        (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) =
      (((μ.real (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) : ℝ) : ℂ) * heckeConst p k) •
        (liftEquiv N k (heckeModular N p k f).toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) :=
  heckeAct_liftEquiv N p μ f.toSlashInvariantForm

end Forms

end GL2Classical

end

end GroundTheory.Automorphic
