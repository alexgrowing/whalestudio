import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobEdges

section Kill

variable {R : Type} [CommRing R]

theorem cc_kill {σ τ : Type} (e : σ ↪ τ) (f : MvPowerSeries τ R) :
    constantCoeff (killCompl e f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
    coeff_zero_eq_constantCoeff_apply]

theorem kill_subst {σ τ υ : Type} [Finite υ] (e : σ ↪ τ) {a : υ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (H : MvPowerSeries υ R) :
    killCompl e (subst a H) = subst (fun k => killCompl e (a k)) H := by
  ext x
  rw [coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero fun k => (cc_kill e _).trans (ha k))]
  refine finsum_congr fun d => ?_
  rw [← coeff_killCompl, map_finsuppProd]
  simp only [map_pow]

theorem kill_eq_subst {σ τ : Type} [Finite τ] (e : σ ↪ τ) (F : MvPowerSeries τ R) :
    killCompl e F = subst (fun t => (killCompl e (X t) : MvPowerSeries σ R)) F := by
  have h := kill_subst e (a := fun t => (X t : MvPowerSeries τ R)) (fun t => constantCoeff_X t) F
  rw [subst_self] at h
  exact h

variable {d : ℕ} {τ : Type}

theorem elim_const {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (j : Fin d ⊕ Fin d) :
    constantCoeff (Sum.elim u v j) = 0 := by
  cases j with
  | inl i => exact hu i
  | inr i => exact hv i

theorem killCompl_powerSeriesEvalTwoGroups {σ : Type} [Finite τ] (e : σ ↪ τ) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    killCompl e (at2 c u v) = at2 c (fun i => killCompl e (u i)) (fun i => killCompl e (v i)) := by
  unfold at2
  rw [kill_subst e (elim_const hu hv)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_zero_zero (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 c (fun _ => (0 : MvPowerSeries τ R)) (fun _ => 0) = C (constantCoeff c) := by
  unfold at2
  have : (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries τ R)) fun _ : Fin d => 0) =
      (0 : Fin d ⊕ Fin d → MvPowerSeries τ R) := by
    funext s; cases s <;> rfl
  rw [this, subst_zero_eq_C_constantCoeff]
  ext n
  simp [coeff_C]

theorem powerSeriesEvalTwoGroups_X_zero (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 c (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) =
      killCompl Function.Embedding.inl c := by
  rw [kill_eq_subst]
  unfold at2
  congr 1
  funext s
  cases s with
  | inl i => exact (killCompl_X (e := (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)) i).symm
  | inr i =>
    refine (killCompl_X_eq_zero ?_).symm
    rintro ⟨j, hj⟩
    exact Sum.inl_ne_inr hj

theorem powerSeriesEvalTwoGroups_zero_X (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    at2 c (fun _ => 0) (fun i => (X i : MvPowerSeries (Fin d) R)) =
      killCompl Function.Embedding.inr c := by
  rw [kill_eq_subst]
  unfold at2
  congr 1
  funext s
  cases s with
  | inl i =>
    refine (killCompl_X_eq_zero ?_).symm
    rintro ⟨j, hj⟩
    exact Sum.inr_ne_inl hj
  | inr i => exact (killCompl_X (e := (Function.Embedding.inr : Fin d ↪ Fin d ⊕ Fin d)) i).symm

theorem mvPowerSeriesMap_evalTwoGroups {S : Type} [CommRing S] (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (elim_const hu hv))]
  congr 1
  funext s
  cases s <;> rfl

end Kill

section Main

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

theorem powerSeriesEvalTwoGroups_swapVariableGroups (c : MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (swap c) u v = at2 c v u := by
  have hs := hasSubst_of_constantCoeff_zero (elim_const hu hv)
  have hW : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp
  unfold swap at2
  rw [subst_comp_subst_apply hW hs]
  congr 1
  funext s
  cases s <;> simp [subst_X hs]

theorem op_const {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (elim_const hu hv))
    (elim_const hu hv) (h i)

theorem sumElim_zero_right (a : Fin d →₀ ℕ) :
    Finsupp.sumElim a (0 : Fin d →₀ ℕ) =
      Finsupp.embDomain (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) a := by
  ext s
  cases s with
  | inl i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inl]
    exact (Finsupp.embDomain_apply_self (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) a i).symm
  | inr i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inr, Finsupp.embDomain_of_notMem_range]
    · rfl
    · rintro ⟨j, hj⟩
      exact Sum.inl_ne_inr hj

theorem sumElim_zero_left (a : Fin d →₀ ℕ) :
    Finsupp.sumElim (0 : Fin d →₀ ℕ) a =
      Finsupp.embDomain (Function.Embedding.inr : Fin d ↪ Fin d ⊕ Fin d) a := by
  ext s
  cases s with
  | inl i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.embDomain_of_notMem_range]
    · rfl
    · rintro ⟨j, hj⟩
      exact Sum.inr_ne_inl hj
  | inr i =>
    rw [Finsupp.sumElim_apply, Sum.elim_inr]
    exact (Finsupp.embDomain_apply_self (Function.Embedding.inr : Fin d ↪ Fin d ⊕ Fin d) a i).symm

end Main

section Lift

variable {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] {θ : B →+* O} {d : ℕ}
  {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}

theorem up_const (hL : IsLift θ μ) (i : Fin d) : constantCoeff (up Q μ i) = 0 := by
  simp [up, hL.const i]

theorem up_unit (hL : IsLift θ μ) :
    op (up Q μ) (fun i => (X i : MvPowerSeries (Fin d) Q)) (fun _ => 0) = fun i => X i := by
  funext i
  have h := congrArg (map (algebraMap B Q)) (congrFun hL.unit i)
  unfold op at h ⊢
  rw [mvPowerSeriesMap_evalTwoGroups _ _ (fun _ => constantCoeff_X _) (fun _ => map_zero _)] at h
  simpa [up] using h

theorem up_comm (hL : IsLift θ μ) (i : Fin d) : swap (up Q μ i) = up Q μ i := by
  have h := congrArg (map (algebraMap B Q)) (hL.comm i)
  unfold swap at h ⊢
  rw [mvPowerSeriesMap_evalTwoGroups _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)] at h
  simpa [up] using h

theorem up_unit_left (hL : IsLift θ μ) :
    op (up Q μ) (fun _ => 0) (fun i => (X i : MvPowerSeries (Fin d) Q)) = fun i => X i := by
  funext i
  unfold op
  rw [← up_comm hL i, powerSeriesEvalTwoGroups_swapVariableGroups _ (fun _ => map_zero _) (fun _ => constantCoeff_X _)]
  exact congrFun (up_unit hL) i

end Lift

section Edges

variable {Q : Type} [CommRing Q] {d : ℕ}

def e3 (d : ℕ) : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d) :=
  ⟨fun i => Sum.inr (Sum.inr i), fun _ _ h => by simpa using h⟩

theorem killCompl_inl_threeGroupsFirstVariables : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
    (x1 (R := Q) (d := d) i)) = fun i => X i :=
  funext fun i => killCompl_X (e := (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))) i

theorem killCompl_inl_threeGroupsSecondVariables : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
    (x2 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj)

theorem killCompl_inl_threeGroupsThirdVariables : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
    (x3 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj)

theorem killCompl_thirdBlock_threeGroupsFirstVariables : (fun i => killCompl (e3 d) (x1 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by rintro ⟨j, hj⟩; exact Sum.inr_ne_inl hj)

theorem killCompl_thirdBlock_threeGroupsSecondVariables : (fun i => killCompl (e3 d) (x2 (R := Q) (d := d) i)) = fun _ => 0 :=
  funext fun _ => killCompl_X_eq_zero (by
    rintro ⟨j, hj⟩
    exact Sum.inr_ne_inl (Sum.inr.inj hj))

theorem killCompl_thirdBlock_threeGroupsThirdVariables : (fun i => killCompl (e3 d) (x3 (R := Q) (d := d) i)) = fun i => X i :=
  funext fun i => killCompl_X (e := e3 d) i

theorem killCompl_formalGroupLawCoboundaryTwo {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q} (h0 : ∀ i, constantCoeff (μ i) = 0)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) Q)) (fun _ => 0) = fun i => X i)
    (hu' : op μ (fun _ => 0) (fun i => (X i : MvPowerSeries (Fin d) Q)) = fun i => X i)
    (c : MvPowerSeries (Fin d ⊕ Fin d) Q) (hc : constantCoeff c = 0) :
    killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d)) (cob2 μ c) =
        -killCompl Function.Embedding.inl c ∧
      killCompl (e3 d) (cob2 μ c) = killCompl Function.Embedding.inr c := by
  have x1c : ∀ i, constantCoeff (x1 (R := Q) (d := d) i) = 0 := fun _ => constantCoeff_X _
  have x2c : ∀ i, constantCoeff (x2 (R := Q) (d := d) i) = 0 := fun _ => constantCoeff_X _
  have x3c : ∀ i, constantCoeff (x3 (R := Q) (d := d) i) = 0 := fun _ => constantCoeff_X _
  have h12 := op_const h0 x1c x2c
  have h23 := op_const h0 x2c x3c
  have opz : op μ (fun _ => (0 : MvPowerSeries (Fin d) Q)) (fun _ => 0) = fun _ => 0 := by
    funext i
    unfold op
    rw [powerSeriesEvalTwoGroups_zero_zero, h0, map_zero]
  refine ⟨?_, ?_⟩
  · have k12 : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
        (op μ x1 x2 i)) = fun i => X i := by
      rw [← hu]
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x1c x2c, killCompl_inl_threeGroupsFirstVariables, killCompl_inl_threeGroupsSecondVariables]
    have k23 : (fun i => killCompl (Function.Embedding.inl : Fin d ↪ Fin d ⊕ (Fin d ⊕ Fin d))
        (op μ x2 x3 i)) = fun _ => 0 := by
      rw [← opz]
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x2c x3c, killCompl_inl_threeGroupsSecondVariables, killCompl_inl_threeGroupsThirdVariables]
    unfold cob2
    rw [map_sub, map_add, map_sub, killCompl_powerSeriesEvalTwoGroups _ c x2c x3c, killCompl_powerSeriesEvalTwoGroups _ c h12 x3c,
      killCompl_powerSeriesEvalTwoGroups _ c x1c h23, killCompl_powerSeriesEvalTwoGroups _ c x1c x2c, killCompl_inl_threeGroupsFirstVariables, killCompl_inl_threeGroupsSecondVariables, killCompl_inl_threeGroupsThirdVariables, k12, k23,
      powerSeriesEvalTwoGroups_zero_zero, hc, map_zero, powerSeriesEvalTwoGroups_X_zero]
    abel
  · have k12 : (fun i => killCompl (e3 d) (op μ x1 x2 i)) = fun _ => 0 := by
      rw [← opz]
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x1c x2c, killCompl_thirdBlock_threeGroupsFirstVariables, killCompl_thirdBlock_threeGroupsSecondVariables]
    have k23 : (fun i => killCompl (e3 d) (op μ x2 x3 i)) = fun i => X i := by
      rw [← hu']
      funext i
      unfold op
      rw [killCompl_powerSeriesEvalTwoGroups _ _ x2c x3c, killCompl_thirdBlock_threeGroupsSecondVariables, killCompl_thirdBlock_threeGroupsThirdVariables]
    unfold cob2
    rw [map_sub, map_add, map_sub, killCompl_powerSeriesEvalTwoGroups _ c x2c x3c, killCompl_powerSeriesEvalTwoGroups _ c h12 x3c,
      killCompl_powerSeriesEvalTwoGroups _ c x1c h23, killCompl_powerSeriesEvalTwoGroups _ c x1c x2c, killCompl_thirdBlock_threeGroupsFirstVariables, killCompl_thirdBlock_threeGroupsSecondVariables, killCompl_thirdBlock_threeGroupsThirdVariables, k12, k23,
      powerSeriesEvalTwoGroups_zero_zero, hc, map_zero, powerSeriesEvalTwoGroups_zero_X]
    abel

end Edges

theorem coeff_edges_mem : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), constantCoeff c = 0 → In N (cob2 (up Q μ) c) → ∀ a : Fin d →₀ ℕ, (∃ b ∈ N, coeff (Finsupp.sumElim a 0) c = algebraMap B Q b) ∧ (∃ b ∈ N, coeff (Finsupp.sumElim 0 a) c = algebraMap B Q b) := by
  intro B O Q _ _ _ _ θ d μ hL N c hc hN a
  obtain ⟨k1, k3⟩ := killCompl_formalGroupLawCoboundaryTwo (up_const (Q := Q) hL) (up_unit hL) (up_unit_left hL) c hc
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb, e⟩ := hN (Finsupp.embDomain Function.Embedding.inl a)
    refine ⟨-b, N.neg_mem hb, ?_⟩
    rw [← coeff_killCompl, k1, map_neg, coeff_killCompl, ← sumElim_zero_right] at e
    rw [map_neg, ← e, neg_neg]
  · obtain ⟨b, hb, e⟩ := hN (Finsupp.embDomain (e3 d) a)
    refine ⟨b, hb, ?_⟩
    rw [← coeff_killCompl, k3, coeff_killCompl, ← sumElim_zero_left] at e
    exact e

end GlobalTheory.CobEdges
