import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Unitarize
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompA

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem dc_tensF_single_false {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF false E a b (Pi.single c v) = Pi.single c (E a b v) + (if b = c then Pi.single a v else 0) := by
  funext c'
  simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.single_apply]
  by_cases h1 : c' = c <;> by_cases h2 : c' = a <;> by_cases h3 : b = c <;> subst_vars <;> simp_all

theorem dc_tensF_single_true {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF true E a b (Pi.single c v) = Pi.single c (E a b v) - (if a = c then Pi.single b v else 0) := by
  funext c'
  simp only [tensF, cond_true, tensVd_coord, Pi.sub_apply, Pi.single_apply]
  by_cases h1 : c' = c <;> by_cases h2 : c' = b <;> by_cases h3 : a = c <;> subst_vars <;> simp_all

theorem dc_mem_tensSub {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ tensSub S ↔ ∀ c, f c ∈ S := by
  simp [tensSub, Submodule.mem_pi]

theorem dc_tens_gen_le {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) {T : Submodule ℂ (Fin n → M)} (hVT : tensSub V ≤ T)
    (hT : ∀ a b, ∀ f ∈ T, tensF dual E a b f ∈ T) : tensSub (genSub E V) ≤ T := by
  classical
  let S : Submodule ℂ M := ⨅ c, T.comap (LinearMap.single ℂ (fun _ : Fin n => M) c)
  have hS : ∀ x, x ∈ S ↔ ∀ c, Pi.single c x ∈ T := by
    intro x; simp [S, Submodule.mem_iInf]
  have hVS : V ≤ S := by
    intro x hx
    rw [hS]
    intro c
    refine hVT (dc_mem_tensSub.mpr fun i => ?_)
    rw [Pi.single_apply]
    split_ifs
    · exact hx
    · exact V.zero_mem
  have hSt : ∀ a b, ∀ v ∈ S, E a b v ∈ S := by
    intro a b v hv
    rw [hS] at hv ⊢
    intro c
    cases dual
    · have : Pi.single c (E a b v) = tensF false E a b (Pi.single c v) - (if b = c then Pi.single a v else 0) := by
        rw [dc_tensF_single_false]; abel
      rw [this]
      refine T.sub_mem (hT a b _ (hv c)) ?_
      split_ifs
      · exact hv a
      · exact T.zero_mem
    · have : Pi.single c (E a b v) = tensF true E a b (Pi.single c v) + (if a = c then Pi.single b v else 0) := by
        rw [dc_tensF_single_true]; abel
      rw [this]
      refine T.add_mem (hT a b _ (hv c)) ?_
      split_ifs
      · exact hv b
      · exact T.zero_mem
  have hgen : genSub E V ≤ S := sInf_le ⟨hVS, hSt⟩
  intro f hf
  rw [← Finset.univ_sum_single f]
  exact T.sum_mem fun c _ => (hS _).1 (hgen (dc_mem_tensSub.mp hf c)) c

section Ambient
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
  {S : Submodule ℂ D} {dual : Bool}

theorem dc_kDiag_add (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → H) :
    kDiag dual σ k (fun c => x c + y c) = fun c => kDiag dual σ k x c + kDiag dual σ k y c := by
  funext c
  simp only [kDiag, map_add, smul_add, Finset.sum_add_distrib]

theorem dc_kDiag_smul (k : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (x : Fin n → H) :
    kDiag dual σ k (fun c => a • x c) = fun c => a • kDiag dual σ k x c := by
  funext c
  simp only [kDiag, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun d _ => smul_comm _ _ _

theorem dc_isGKEndo_add' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A + B) := by
  refine ⟨fun f hf => (tensSub S).add_mem (hA.1 f hf) (hB.1 f hf), fun a b f hf => ?_,
    fun k hk f hf f' hf' h => ?_⟩
  · simp only [LinearMap.add_apply, map_add, hA.2.1 a b f hf, hB.2.1 a b f hf]
  · have e1 := hA.2.2 k hk f hf f' hf' h
    have e2 := hB.2.2 k hk f hf f' hf' h
    simp only [LinearMap.add_apply, Pi.add_apply, Submodule.coe_add]
    rw [dc_kDiag_add, ← e1, ← e2]

theorem dc_isGKEndo_smul' {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (a : ℂ) :
    IsGKEndo dual ε σ E S (a • A) := by
  refine ⟨fun f hf => (tensSub S).smul_mem a (hA.1 f hf), fun x y f hf => ?_,
    fun k hk f hf f' hf' h => ?_⟩
  · simp only [LinearMap.smul_apply, map_smul, hA.2.1 x y f hf]
  · have e1 := hA.2.2 k hk f hf f' hf' h
    simp only [LinearMap.smul_apply, Pi.smul_apply, Submodule.coe_smul]
    rw [dc_kDiag_smul, ← e1]

theorem dc_isGKEndo_mul' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A * B) := by
  refine ⟨fun f hf => hA.1 _ (hB.1 f hf), fun a b f hf => ?_, fun k hk f hf f' hf' h => ?_⟩
  · simp only [Module.End.mul_apply, hB.2.1 a b f hf, hA.2.1 a b _ (hB.1 f hf)]
  · exact hA.2.2 k hk _ (hB.1 f hf) _ (hB.1 f' hf') (hB.2.2 k hk f hf f' hf' h)

theorem dc_isGKEndo_one' : IsGKEndo dual ε σ E S 1 :=
  ⟨fun f hf => hf, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ h => h⟩

theorem dc_isGKEndo_zero' : IsGKEndo dual ε σ E S 0 := by
  refine ⟨fun _ _ => (tensSub S).zero_mem, fun _ _ _ _ => by simp, fun k _ _ _ _ _ _ => ?_⟩
  funext c
  simp [kDiag]

theorem dc_isGKEndo_aeval {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (p : ℂ[X]) :
    IsGKEndo dual ε σ E S (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact dc_isGKEndo_add' hp hq
  | monomial k a =>
    rw [aeval_monomial, Module.algebraMap_end_eq_smul_id]
    refine dc_isGKEndo_mul' (dc_isGKEndo_smul' dc_isGKEndo_one' a) ?_
    induction k with
    | zero => rw [pow_zero]; exact dc_isGKEndo_one'
    | succ k ih => rw [pow_succ]; exact dc_isGKEndo_mul' ih hA

end Ambient

end ReciprocityTheory.ChartRestriction.DS

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

def dc_wsh (dual : Bool) (μ : Fin n → ℝ) (c : Fin n) : Fin n → ℝ :=
  if dual then μ + Pi.single c 1 else μ - Pi.single c 1

section
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem dc_top_coord_false {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF false E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh false μ c) (f c) := by
  classical
  have hne : (univ.filter fun c => f c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.mp h0
    exact ⟨c, by simpa using hc⟩
  set c := (univ.filter fun c => f c ≠ 0).max' hne with hcdef
  have hc : f c ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa using this
  have hmax : ∀ b, c < b → f b = 0 := by
    intro b hb
    by_contra h
    have := Finset.le_max' (univ.filter fun c => f c ≠ 0) b (by simpa using h)
    exact absurd hb (not_lt.mpr this)
  refine ⟨c, hc, fun a => ?_, fun a b hab he => ?_⟩
  · have h := congrFun (hf.1 a) c
    simp only [tensF, cond_false, tensV_coord, Pi.smul_apply] at h
    simp only [dc_wsh, Bool.false_eq_true, if_false, Pi.sub_apply, Pi.single_apply]
    by_cases hca : c = a
    · subst hca
      simp only [if_true] at h ⊢
      rw [eq_sub_of_add_eq h]
      push_cast
      rw [sub_smul, one_smul]
    · have hac : a ≠ c := Ne.symm hca
      simp only [hca, hac, if_false, add_zero] at h ⊢
      rw [h]
      push_cast
      simp
  · have h := congrFun (hf.2 a b hab he) c
    simp only [tensF, cond_false, tensV_coord, Pi.zero_apply] at h
    by_cases hca : c = a
    · subst hca
      simpa [hmax b hab] using h
    · simpa [hca] using h

theorem dc_top_coord_true {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF true E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh true μ c) (f c) := by
  classical
  have hne : (univ.filter fun c => f c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.mp h0
    exact ⟨c, by simpa using hc⟩
  set c := (univ.filter fun c => f c ≠ 0).min' hne with hcdef
  have hc : f c ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  have hmin : ∀ a, a < c → f a = 0 := by
    intro a ha
    by_contra h
    have := Finset.min'_le (univ.filter fun c => f c ≠ 0) a (by simpa using h)
    exact absurd ha (not_lt.mpr this)
  refine ⟨c, hc, fun a => ?_, fun a b hab he => ?_⟩
  · have h := congrFun (hf.1 a) c
    simp only [tensF, cond_true, tensVd_coord, Pi.smul_apply] at h
    simp only [dc_wsh, if_true, Pi.add_apply, Pi.single_apply]
    by_cases hca : c = a
    · subst hca
      simp only [if_true] at h ⊢
      rw [eq_add_of_sub_eq h]
      push_cast
      rw [add_smul, one_smul]
    · have hac : a ≠ c := Ne.symm hca
      simp only [hca, hac, if_false, sub_zero] at h ⊢
      rw [h]
      push_cast
      simp
  · have h := congrFun (hf.2 a b hab he) c
    simp only [tensF, cond_true, tensVd_coord, Pi.zero_apply] at h
    by_cases hcb : c = b
    · subst hcb
      simpa [hmin a hab] using h
    · simpa [hcb] using h

theorem dc_top_coord {dual : Bool} {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF dual E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh dual μ c) (f c) := by
  cases dual
  · exact dc_top_coord_false hf h0
  · exact dc_top_coord_true hf h0

end

section Pi
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

abbrev dc_TX (n : ℕ) (D : Type*) [NormedAddCommGroup D] [InnerProductSpace ℂ D] := PiLp 2 (fun _ : Fin n => D)

def dc_eqv : dc_TX n D ≃ₗ[ℂ] (Fin n → D) := WithLp.linearEquiv 2 ℂ (Fin n → D)

theorem dc_eqv_apply (x : dc_TX n D) : dc_eqv x = x.ofLp := rfl

theorem dc_eqv_symm_apply (f : Fin n → D) : (dc_eqv (n := n)).symm f = WithLp.toLp 2 f := rfl

def dc_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (dc_TX n D) :=
  dc_eqv.symm.conj (tensF dual E a b)

theorem dc_tensX_apply (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_tensX dual E a b x = dc_eqv.symm (tensF dual E a b (dc_eqv x)) := by
  simp [dc_tensX, LinearEquiv.conj_apply]

theorem dc_eqv_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_eqv (dc_tensX dual E a b x) = tensF dual E a b (dc_eqv x) := by
  rw [dc_tensX_apply, LinearEquiv.apply_symm_apply]

theorem dc_tensX_isGlRep {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hE : IsGlRep E) :
    IsGlRep (dc_tensX dual E) := by
  have hT : IsGlRep (tensF dual E) := by
    cases dual
    · exact tensV_isGlRep hE
    · exact tensVd_isGlRep hE
  intro a b c d
  refine LinearMap.ext fun x => dc_eqv.injective ?_
  have h := LinearMap.congr_fun (hT a b c d) (dc_eqv x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dc_eqv_tensX, map_sub] at h ⊢
  rw [h]
  split_ifs <;> simp [dc_eqv_tensX]

theorem dc_sum_inner_ite_left (a : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (if i = a then u else 0) (g i) = inner ℂ u (g a) := by
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_sum_inner_ite_right (b : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (g i) (if i = b then u else 0) = inner ℂ (g b) u := by
  rw [Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_tensX_isKUnitary {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hU : IsKUnitary ε E) :
    IsKUnitary ε (dc_tensX dual E) := by
  intro a b hab x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [← dc_eqv_apply, dc_eqv_tensX]
  cases dual
  · simp only [tensF, cond_false, tensV_coord, inner_add_left, inner_add_right, Finset.sum_add_distrib,
      hU a b hab]
    congr 1
    simp only [dc_sum_inner_ite_left, dc_sum_inner_ite_right]
  · simp only [tensF, cond_true, tensVd_coord, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib,
      hU a b hab]
    congr 1
    simp only [dc_sum_inner_ite_left, dc_sum_inner_ite_right]

end Pi

end ReciprocityTheory.ChartRestriction.DS

end
