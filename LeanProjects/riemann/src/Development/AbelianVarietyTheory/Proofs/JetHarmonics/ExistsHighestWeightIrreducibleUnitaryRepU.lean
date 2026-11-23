import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpanStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitaryHighestWeight

section OneParam

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem deriv_right (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (U t (A v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) v) (A v) t := by
    have h := hd v
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  have h2 := ((U t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  have h3 : HasDerivAt (fun s => U t (U (s - t) v)) (U t (A v)) t := h2
  convert h3 using 1
  funext s
  simp [← hadd]

theorem deriv_left (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (A (U t v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) (U t v)) (A (U t v)) t := by
    have h := hd (U t v)
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  convert h1 using 1
  funext s
  simp [← hadd]

theorem eigen (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (c : ℂ) (hv : A v = c • v) :
    U 1 v = Complex.exp c • v := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • U t v) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    have h2 := h1.fun_smul (deriv_right U A hadd hd v t)
    convert h2 using 1
    rw [hv, map_smul, smul_smul, ← add_smul]
    simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    one_smul, h0] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem stable [FiniteDimensional ℂ W] (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (S : Submodule ℂ W) (hS : ∀ v ∈ S, A v ∈ S)
    (v : W) (hv : v ∈ S) (t : ℝ) : U t v ∈ S := by
  set Q : W →L[ℂ] W := ContinuousLinearMap.id ℂ W - S.starProjection with hQ
  have hQ0 : ∀ y ∈ S, Q y = 0 := fun y hy => by
    simp [hQ, (Submodule.starProjection_eq_self_iff (K := S)).2 hy]
  set B : W →L[ℂ] W := Q.comp (LinearMap.toContinuousLinearMap A) with hB
  have hq : ∀ t, HasDerivAt (fun s => Q (U s v)) (B (Q (U t v))) t := by
    intro t
    have h2 : HasDerivAt (fun s => Q (U s v)) (Q (A (U t v))) t :=
      (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (deriv_left U A hadd hd v t)
    convert h2 using 1
    have h3 : Q (A (S.starProjection (U t v))) = 0 :=
      hQ0 _ (hS _ (Submodule.starProjection_apply_mem S _))
    have h4 : Q (U t v) = U t v - S.starProjection (U t v) := by simp [hQ]
    simp only [hB, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    rw [h4, map_sub, map_sub, h3, sub_zero]
  have hz : (fun s => Q (U s v)) = fun _ => (0 : W) := by
    refine ODE_solution_unique_univ (v := fun _ y => B y) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
      (fun _ => B.lipschitz.lipschitzOnWith) (fun t => ⟨hq t, trivial⟩)
      (fun t => ⟨by simpa using hasDerivAt_const t (0 : W), trivial⟩) ?_
    simp only [h0]
    exact hQ0 v hv
  have h5 : U t v - S.starProjection (U t v) = 0 := by simpa [hQ] using congrFun hz t
  rw [sub_eq_zero.1 h5]
  exact Submodule.starProjection_apply_mem S _

end OneParam

open PI.UpqRep

theorem Jm_allPos (k : ℕ) : Jm (allPos k) = 1 := by
  simp [Jm, allPos]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Jm (allPos k) = Jm (allPos k) * g) ↔
    gᴴ * Jm (allPos k) * g = Jm (allPos k)
  rw [Jm_allPos, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem exp_mem {k : ℕ} {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Z) ∈ UJset (allPos k) := by
  refine Formalism.REAL.exp_indefinite_unitary_holds k (allPos k) Z ?_ t
  show Zᴴ * Jm (allPos k) + Jm (allPos k) * Z = 0
  rw [Jm_allPos, hZ]
  simp

variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)}

theorem group_zero (hπ : IsURepOn (UJset (allPos k)) π) (Z : Matrix (Fin k) (Fin k) ℂ) (v : W) :
    π (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) v = v := by
  simp [hπ.1.1]

theorem group_add (hπ : IsURepOn (UJset (allPos k)) π) {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z)
    (s t : ℝ) (v : W) :
    π (NormedSpace.exp (((s + t : ℝ) : ℂ) • Z)) v =
      π (NormedSpace.exp ((s : ℂ) • Z)) (π (NormedSpace.exp ((t : ℂ) • Z)) v) := by
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl Z).smul_left _).smul_right _), hπ.1.2 _ (exp_mem hZ s) _ (exp_mem hZ t)]
  rfl

theorem diag_skew (θ : Fin k → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)ᴴ = -Matrix.diagonal fun a => (θ a : ℂ) * Complex.I := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext a
  simp

theorem exp_diag (θ : Fin k → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      Matrix.diagonal fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  simp [mul_assoc]

theorem sum_diag (E : Fin k → Fin k → Module.End ℂ W) (d : Fin k → ℂ) (v : W) :
    ∑ a, ∑ b, Matrix.diagonal d a b • E a b v = ∑ a, d a • E a a v := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diagonal_apply, ite_smul]

theorem isWtOn_of_isWeight (hπ : IsURepOn (UJset (allPos k)) π) (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : Formalism.REAL.IsWeight E μ v) : IsWtOn (Kset (allPos k)) π μ v := by
  intro θ _
  have h := eigen (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)))
    (∑ a, ((θ a : ℂ) * Complex.I) • E a a) (group_zero hπ _) (group_add hπ (diag_skew θ))
    (fun w => by
      have := hE _ (diag_skew θ) w
      rw [sum_diag] at this
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using this)
    v (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) (by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hv _, smul_smul, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring)
  simp only [exp_diag, one_mul] at h
  exact h

theorem isWeight_of_isWtOn (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : IsWtOn (Kset (allPos k)) π μ v) : Formalism.REAL.IsWeight E μ v := by
  intro a
  set θ : Fin k → ℝ := Pi.single a 1 with hθ
  have h1 := hE _ (diag_skew θ) v
  rw [sum_diag] at h1
  have h2 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) v) =
      fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v := by
    funext t
    have hm := exp_mem (diag_skew θ) t
    rw [exp_diag] at hm ⊢
    rw [hv (fun b => t * θ b) ((mem_K_iff _).2 hm)]
    congr 2
    simp [hθ, Pi.single_apply]
    ring
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v) ((μ a * Complex.I) • v) 0 := by
    have h4 : HasDerivAt (fun t : ℝ => (μ a * Complex.I) * (t : ℂ)) (μ a * Complex.I) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (μ a * Complex.I)
    simpa using h4.cexp.smul_const v
  rw [h2] at h1
  have h5 := h1.unique h3
  have h6 : ∑ b, ((θ b : ℂ) * Complex.I) • E b b v = Complex.I • E a a v := by
    rw [Finset.sum_eq_single a]
    · simp [hθ]
    · intro b _ hb
      simp [hθ, Pi.single_eq_of_ne hb]
    · simp
  rw [h6, mul_comm, ← smul_smul] at h5
  exact smul_right_injective W Complex.I_ne_zero h5

theorem stable_of_derived [FiniteDimensional ℂ W] (hπ : IsURepOn (UJset (allPos k)) π)
    (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (S : Submodule ℂ W) (hS : Formalism.REAL.KStable (allPos k) E S) :
    ∀ g ∈ UJset (allPos k), ∀ v ∈ S, π g v ∈ S := by
  intro g hg v hv
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (allPos k) g ((mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * Jm (allPos k) + Jm (allPos k) * Y = 0 := hY.1
    rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := stable (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E a b)
    (group_zero hπ _) (group_add hπ hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hE _ hZ w) S
    (fun w hw => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b rfl w hw)) v hv 1
  simpa [hg'] using h

theorem exists_isHCTypeU : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π → (∀ S : Submodule ℂ W, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∃ u, PI.UpqRep.IsHCTypeU k u π := by
  intro k W _ _ _ _ π hπ hirr
  obtain ⟨E, hgl, hun, hE⟩ := GlobalTheory.T.exists_derivedAction_finiteDimUnitaryRep k W π hπ
  obtain ⟨x, -, hx, Λ, hΛ⟩ := Formalism.REAL.highestWeightExists_holds W k (allPos k) E ⊤ inferInstance
    (Formalism.REAL.glRel_kRel _ E hgl) (Formalism.REAL.isUnitary_kUnit _ E hun) (fun _ _ _ _ _ => trivial) top_ne_bot
  have hxm : x ∈ Formalism.REAL.kSpan (allPos k) E x := Submodule.mem_sInf.2 fun S hS => hS.1
  have hst : Formalism.REAL.KStable (allPos k) E (Formalism.REAL.kSpan (allPos k) E x) := fun a b hab y hy =>
    Submodule.mem_sInf.2 fun S hS => hS.2 a b hab y (Submodule.mem_sInf.1 hy S hS)
  have htop : Formalism.REAL.kSpan (allPos k) E x = ⊤ := by
    rcases hirr _ (stable_of_derived hπ E hE _ hst) with h | h
    · rw [h] at hxm
      exact absurd hxm hx
    · exact h
  refine ⟨Λ - rhoN (allPos k) + rhoC (allPos k), inferInstance, inferInstance, hπ, ?_⟩
  have hl : lowK (allPos k) (Λ - rhoN (allPos k) + rhoC (allPos k)) = Λ := by
    unfold lowK
    abel
  rw [hl]
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => hirr S fun g hg => hS g ((mem_K_iff g).2 hg),
    ⟨x, trivial, hx, isWtOn_of_isWeight hπ E hE Λ x hΛ.1⟩, fun μ v _ hv hw => ?_⟩
  exact GlobalTheory.T.weight_compactDominance_of_mem_highestWeightSpan k W E Λ μ x v hgl hun hΛ (htop ▸ trivial) hv (isWeight_of_isWtOn E hE μ v hw)

end GlobalTheory.UnitaryHighestWeight
