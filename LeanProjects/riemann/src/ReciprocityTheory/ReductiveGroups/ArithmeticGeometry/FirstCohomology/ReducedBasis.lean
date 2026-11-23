import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SpanFlag

namespace ReciprocityTheory.ChartRestriction.G.H1

open Module

theorem reducedBasis_holds : ReducedBasisStatement := by
  intro E _ _ _ X _ _ M v hv hvX hvM
  classical
  obtain ⟨u, hu⟩ := RB.greedy X v hv hvX
  have huX : ∀ k, u k ∈ X := fun k => (hu k).1
  have huV : ∀ k : Fin (finrank ℝ E), u k ∉ RB.V u k.val := fun k => (hu k).2.1
  have hli : LinearIndependent ℝ u := RB.indep_of_flag rfl u huV
  have hmono : ∀ k j : Fin (finrank ℝ E), j < k → ‖u j‖ ≤ ‖u k‖ := by
    intro k j hjk
    apply (hu j).2.2.2 (u k) (huX k)
    intro hmem
    exact huV k (RB.V_mono u (Fin.lt_iff_val_lt_val.1 hjk).le hmem)
  have hb := fun k => RB.exists_b u hli X huX k (fun j hj => hmono k j hj)
  choose b hbX hbV hb0 hb1 hbmin hbnrm hbd using hb
  have hspan := RB.span_flag u hli X b hbX hbV hb0 hb1 hbmin
  have hVtop : RB.V u (finrank ℝ E) = ⊤ := by
    have h1 : RB.V u (finrank ℝ E) = Submodule.span ℝ (Set.range u) := by
      simp only [RB.V]
      congr 1
      ext x
      simp
    rw [h1]
    first
    | exact hli.span_eq_top_of_card_eq_finrank (by simp)
    | exact hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hbnot : ∀ k : Fin (finrank ℝ E), b k ∉ RB.V b k.val := by
    intro k hmem
    have hsub : RB.V b k.val ≤ RB.V u k.val := by
      rw [RB.V, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact RB.V_mono u (show l.val + 1 ≤ k.val from hl) (hbV l)
    have h0 := RB.phi_V u k (hsub hmem)
    exact (hb0 k).ne' h0
  have hliR : LinearIndependent ℝ b := RB.indep_of_flag rfl b hbnot
  have hliZ : LinearIndependent ℤ b := by
    first
    | exact hliR.restrict_scalars' ℤ
    | exact hliR.restrict_scalars (fun a c h => by simpa using h)
  let bX : Fin (finrank ℝ E) → X := fun k => ⟨b k, hbX k⟩
  have hliX : LinearIndependent ℤ bX := LinearIndependent.of_comp X.subtype hliZ
  have hspX : ⊤ ≤ Submodule.span ℤ (Set.range bX) := by
    rintro x -
    have hx := hspan (finrank ℝ E) le_rfl x.1 x.2 (by rw [hVtop]; exact Submodule.mem_top)
    have hrange : Set.range b = X.subtype '' Set.range bX := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  let B := Basis.mk hliX hspX
  have hBj : ∀ j, (B j : E) = b j := fun j => by
    simp only [B, Basis.mk_apply, bX]
  refine ⟨B, ?_, ?_⟩
  · intro j
    rw [hBj]
    obtain ⟨i, hi⟩ := (hu j).2.2.1
    have h1 := hbd j
    have h2 : ‖u j‖ ^ 2 ≤ ‖v i‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
    have h3 := hvM i
    have hd0 : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 hd0, mul_le_mul_of_nonneg_left h3 hd0]
  · intro j z hz
    rw [hBj]
    by_cases hzV : z ∈ RB.V u j.val
    · have hzV1 : z ∈ RB.V u (j.val + 1) := RB.V_mono u (Nat.le_succ _) hzV
      have hphz : RB.phi u j z = 0 := RB.phi_V u j hzV
      have hp : ‖b j‖ ≤ ‖b j + z‖ := hbnrm j (b j + z) (X.add_mem (hbX j) hz)
        (Submodule.add_mem _ (hbV j) hzV1) (by rw [RB.phi_add, hphz, add_zero])
      have hm : ‖b j‖ ≤ ‖b j - z‖ := hbnrm j (b j - z) (X.sub_mem (hbX j) hz)
        (Submodule.sub_mem _ (hbV j) hzV1) (by rw [RB.phi_sub, hphz, sub_zero])
      have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
      rw [norm_add_sq_real] at hp2
      rw [norm_sub_sq_real] at hm2
      have hz0 : 0 ≤ ‖z‖ ^ 2 := by positivity
      have hd1 : (1 : ℝ) ≤ Real.sqrt (finrank ℝ E) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.succ_le_of_lt (Fin.pos j))
      rw [abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right hd1 hz0]
    · have hle : ‖u j‖ ≤ ‖z‖ := (hu j).2.2.2 z hz hzV
      have hb' : ‖b j‖ ≤ Real.sqrt (finrank ℝ E) * ‖u j‖ := by
        calc ‖b j‖ = Real.sqrt (‖b j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt ((finrank ℝ E : ℝ) * ‖u j‖ ^ 2) := Real.sqrt_le_sqrt (hbd j)
          _ = Real.sqrt (finrank ℝ E) * ‖u j‖ := by
            rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      calc |inner ℝ (b j) z| ≤ ‖b j‖ * ‖z‖ := abs_real_inner_le_norm _ _
        _ ≤ (Real.sqrt (finrank ℝ E) * ‖u j‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
        _ ≤ (Real.sqrt (finrank ℝ E) * ‖z‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _))
            (norm_nonneg _)
        _ = 2 * Real.sqrt (finrank ℝ E) * (‖z‖ ^ 2 / 2) := by ring

end ReciprocityTheory.ChartRestriction.G.H1
