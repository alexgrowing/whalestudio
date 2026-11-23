import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PhiPerm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Sch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem phi_one_Wm (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) : phi E 1 x = 0 := by
  by_contra hne
  have := finiteDimensional_ncV (ε := ε) hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hWst : IsKStableSub ε (bAct E 1) (Wm ε E V) := Wm_kStable hE hU hV
  set T : Submodule ℂ M := (Wm ε E V).map (phi E 1) with hTdef
  have hfdT : FiniteDimensional ℂ T := inferInstance
  have hTst : IsKStableSub ε E T := by
    intro a b hab v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
    rw [← phi_bAct hE 1 hab y]
    exact Submodule.mem_map_of_mem (hWst a b hab y hy)
  have hTne : T ≠ ⊥ := by
    intro hT
    have : phi E 1 x ∈ T := Submodule.mem_map_of_mem hx
    rw [hT, Submodule.mem_bot] at this
    exact hne this
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  obtain ⟨y, hyT, hy0, μ, hyμ⟩ := exists_khw hE hKU hfdT hTst hTne
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hyT
  obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct E 1) (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab z => phi_bAct hE 1 hab z) hfdW hWst hx₀ hyμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  obtain ⟨a, b, hab, hε, hμ⟩ := Wm_khw hE hU hV hmono hh hbig hx1 hx10 hkhw
  have hlay : phi E 1 x₀ ∈ layer ε E V 1 := phi_mem_layer (Wm_le_ncV hx₀)
  have hcas : casimir E (phi E 1 x₀) = (casVal lam : ℂ) • phi E 1 x₀ :=
    casimir_genSub hE hc _ (layer_le_genSub (ε := ε) 1 hlay)
  rw [hμ] at hyμ
  exact hy0 (khw_lowK_sub_root_eq_zero ε hE hU lam hab hε
    (sch_gap ⟨hmono, h, hh, hbig⟩ hab hε) hyμ hcas)

theorem sch_coord_apply {k : ℕ} (κ : Fin k → Fin n × Fin n) (F : Big n k M) : coord k κ F = F κ := rfl

theorem sch_slice_apply {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (F : Big n k M)
    (ι : Fin 1 → Fin n × Fin n) : slice i κ F ι = F (Function.update κ i (ι 0)) := rfl

theorem sch_permute_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := rfl

theorem sch_word_snoc {k : ℕ} (init : Fin k → Fin n × Fin n) (p : Fin n × Fin n) :
    word E (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) = word E init * E p.1 p.2 := by
  simp only [word, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]

theorem sch_word_one (ι : Fin 1 → Fin n × Fin n) : word E ι = E (ι 0).1 (ι 0).2 := by
  simp only [word, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]

theorem sch_phi_one_apply (G : Big n 1 M) :
    phi E 1 G = ∑ p : Fin n × Fin n, E p.1 p.2 (G (fun _ => p)) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun κ => ?_)
  rw [Equiv.funUnique_apply, sch_word_one, sch_coord_apply]
  obtain ⟨p, rfl⟩ : ∃ p, κ = fun _ => p := ⟨κ 0, funext fun j => by rw [Fin.fin_one_eq_zero j]⟩
  rfl

theorem phi_Wm_last (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by

  let e : (Fin k → Fin n × Fin n) × (Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
    { toFun := fun q => Fin.snoc q.1 q.2
      invFun := fun κ => (Fin.init κ, κ (Fin.last k))
      left_inv := fun q => by simp
      right_inv := fun κ => Fin.snoc_init_self κ }
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply, sch_coord_apply]
  rw [Fintype.sum_equiv e.symm _
    (fun q => word E (Fin.snoc q.1 q.2 : Fin (k + 1) → Fin n × Fin n) (F (Fin.snoc q.1 q.2)))
    (fun κ => by simp only [e, Equiv.coe_fn_symm_mk, Fin.snoc_init_self])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun init _ => ?_
  simp only [sch_word_snoc, Module.End.mul_apply]
  rw [← map_sum]
  rcases isEmpty_or_nonempty (Fin n × Fin n) with hX | ⟨⟨p0⟩⟩
  · simp
  · have h := phi_one_Wm hE hU hV hc hmono hh hbig (hF (Fin.snoc init p0))
    rw [sch_phi_one_apply] at h
    simp only [sch_slice_apply, Fin.update_snoc_last] at h
    rw [h, map_zero]

theorem phi_Wm_position (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M} (hF0 : F ∈ ncV ε V (k + 1))
    (hF : ∀ κ, slice i κ F ∈ Wm ε E V) : phi E (k + 1) F ∈ layer ε E V k := by

  have hperm : ∀ κ, slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) ∈ Wm ε E V := by
    intro κ
    have heq : slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) =
        slice i (κ ∘ Equiv.swap i (Fin.last k)) F := by
      refine PiLp.ext fun ι => ?_
      rw [sch_slice_apply, sch_permute_apply, sch_slice_apply, Function.update_comp_equiv,
        Equiv.symm_swap, Equiv.swap_apply_right]
    rw [heq]
    exact hF _
  have h0 := phi_Wm_last hE hU hV hc hmono hh hbig hperm
  have hsub := phi_permute_sub_mem hE hV.2.1 (Equiv.swap i (Fin.last k)) hF0
  rw [h0, sub_zero] at hsub
  exact hsub

end Sch

end ReciprocityTheory.ChartRestriction.DS
