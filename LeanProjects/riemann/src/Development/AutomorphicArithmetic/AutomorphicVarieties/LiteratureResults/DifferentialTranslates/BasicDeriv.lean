import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Dr

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

end

private theorem hasDerivAt_apply_comp_of_differentiableAt {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F}
    {c : ℝ → V} {c' : V} {s : ℝ} (m : Fin q → V) (hw : DifferentiableAt ℝ w (c s))
    (hc : HasDerivAt c c' s) :
    HasDerivAt (fun r => w (c r) m) (fderiv ℝ w (c s) c' m) s := by
  have h1 := (ContinuousAlternatingMap.apply ℝ V F m).hasFDerivAt.comp (c s) hw.hasFDerivAt
  exact h1.comp_hasDerivAt s hc

private theorem fderiv_update_add_eq_zero_of_radBasic {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ}
    {w : V → V [⋀^Fin q]→L[ℝ] F} (hR : RadBasic Y w) {x : V} (hx : x ∈ Y)
    (hw : DifferentiableAt ℝ w x) (v : Fin q → V) (j : Fin q) :
    fderiv ℝ w x (v j) (Function.update v j x) + w x v = 0 := by
  have hc : HasDerivAt (fun s : ℝ => x + s • v j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v j)).const_add x
  have hw0 : DifferentiableAt ℝ w (x + (0 : ℝ) • v j) := by simpa using hw
  have d1 := hasDerivAt_apply_comp_of_differentiableAt (Function.update v j x) hw0 hc
  have d2 := hasDerivAt_apply_comp_of_differentiableAt v hw0 hc
  have d3 := (hasDerivAt_id (0 : ℝ)).smul d2
  have dg := d1.add d3
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • v j ∈ Y := by
    have hcont : Continuous fun s : ℝ => x + s • v j := by fun_prop
    exact hcont.continuousAt (x := 0) |>.preimage_mem_nhds (by simpa using hY.mem_nhds hx)
  have heq : (fun s : ℝ => w (x + s • v j) (Function.update v j x) + id s • w (x + s • v j) v)
      =ᶠ[𝓝 0] fun _ => (0 : F) := by
    filter_upwards [hev] with s hs
    have h0 := hR (x + s • v j) hs (Function.update v j (x + s • v j)) j (by simp)
    rw [ContinuousAlternatingMap.map_update_add, ContinuousAlternatingMap.map_update_smul,
      Function.update_eq_self] at h0
    simpa using h0
  have := dg.unique ((hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq heq)
  simpa using this

private theorem fderiv_self_add_smul_eq_zero_of_radBasic_closed {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ}
    {w : V → V [⋀^Fin q]→L[ℝ] F} (hR : RadBasic Y w) {x : V} (hx : x ∈ Y)
    (hw : DifferentiableAt ℝ w x) (hd : extDeriv w x = 0) (v : Fin q → V) :
    fderiv ℝ w x x v + (q : ℝ) • w x v = 0 := by
  have h0 := congrArg (fun f => f (Fin.cons x v)) hd
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ] at h0
  cases q with
  | zero => simpa using h0
  | succ n =>
    have hterm : ∀ j : Fin (n + 1), (-1 : ℤ) ^ ((j.succ : Fin (n + 2)) : ℕ) •
        fderiv ℝ w x ((Fin.cons x v : Fin (n + 2) → V) j.succ)
          (Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → V)) = w x v := by
      intro j
      have hr : Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → V) =
          Matrix.vecCons x (Fin.removeNth j v) := by
        ext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [Fin.removeNth]
        · simp [Fin.removeNth, Fin.succ_succAbove_succ]
      rw [hr, ← ContinuousAlternatingMap.neg_one_pow_smul_map_insertNth, Fin.insertNth_removeNth,
        Fin.cons_succ, smul_smul]
      have := fderiv_update_add_eq_zero_of_radBasic hY hR hx hw v j
      rw [Fin.val_succ, pow_succ, mul_comm, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩,
        one_mul, neg_one_smul, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero]
      exact this
    rw [Finset.sum_congr rfl (fun j _ => hterm j)] at h0
    rw [Nat.cast_smul_eq_nsmul]
    simpa [add_comm] using h0

theorem homog : Homog := by
  intro V F _ _ _ _ Y hY hC q w hw hR hd t ht p hp v
  have hdiff : ∀ x ∈ Y, DifferentiableAt ℝ w x := fun x hx =>
    (hw.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  set k : ℝ → F := fun s => s ^ q • w (s • p) v with hkdef
  have hscale : ∀ s : ℝ, w (s • p) (fun i => s • v i) = k s := by
    intro s
    rw [ContinuousAlternatingMap.map_smul_univ]
    simp [k, Finset.prod_const]
  have hk : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt k 0 s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsp : s • p ∈ Y := hC s hs p hp
    have hc : HasDerivAt (fun r : ℝ => r • p) p s := by
      simpa using (hasDerivAt_id s).smul_const p
    have dg := hasDerivAt_apply_comp_of_differentiableAt v (c := fun r : ℝ => r • p) (hdiff _ hsp) hc
    have dk : HasDerivAt k _ s := (hasDerivAt_pow q s).smul dg
    have key := fderiv_self_add_smul_eq_zero_of_radBasic_closed hY hR hsp (hdiff _ hsp) (hd _ hsp) v
    have hA : s • fderiv ℝ w (s • p) p v = -((q : ℝ) • w (s • p) v) := by
      rw [eq_neg_iff_add_eq_zero, ← key]
      simp [map_smul]
    have hpow : s * ((q : ℝ) * s ^ (q - 1)) = q * s ^ q := by
      cases q with
      | zero => simp
      | succ n => simp [pow_succ]; ring
    convert dk using 1
    apply smul_right_injective F hs0
    simp only [smul_zero, smul_add]
    rw [smul_comm s (s ^ q), hA, smul_smul, hpow, smul_neg, smul_smul, mul_comm, neg_add_cancel]
  have hconst := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun s hs => (hk s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hk s hs).deriv) (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr one_pos)
  rw [hscale, hconst]
  simp [k]

end UpperTheory.V.Lit.Dr
