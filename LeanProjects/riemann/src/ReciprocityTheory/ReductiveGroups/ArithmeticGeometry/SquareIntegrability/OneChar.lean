import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PrjMemOfSpan

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

set_option maxHeartbeats 1000000 in
lemma one_char [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    (L I : Submodule ℤ (Vsp dim))
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (k : ℕ) (χ : ℕ → Vsp dim) (hχX : ∀ j < k, χ j ∈ Xg L I) (hχW : ∀ j < k, prj σ (χ j) ∈ W)
    (hWχ : W ≤ Submodule.span ℂ ((fun i => prj σ (χ i)) '' Set.Iio k))
    (hflag : ∀ j < k, ∃ μ, χ j ∈ Zs L I μ ∧ ∀ y ∈ Xg L I, prj σ y ∉ W → μ ≤ ‖y‖)
    (v : Vsp dim) (hvX : v ∈ Xg L I) (hvW : prj σ v ∉ W)
    (hvmin : ∀ y ∈ Xg L I, prj σ y ∉ W → ‖v‖ ≤ ‖y‖) (T : ℝ) (hT : 0 < T) :
    ∃ t χ' : Vsp dim, (∀ w ∈ W, inner ℂ w (prj σ t) = 0) ∧ ‖prj σ t‖ = T ∧
      ‖t‖ ^ 2 = 2 * T ^ 2 ∧ χ' ∈ Xg L I ∧ χ' ∈ Zs L I ‖v‖ ∧
      ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 ∧
      ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
  classical

  have hMc1 : ∀ (c : ℂ) (x : Vsp dim), Mc σ 1 (Mc σ c x) = Mc σ c x := by
    intro c x
    ext i
    simp only [Mc, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> simp
  have hprj1 : ∀ x : Vsp dim, prj σ (Mc σ 1 x) = prj σ x := by
    intro x; rw [prj_Mc, one_smul]
  have hZact : ∀ (α : 𝓞 E) x, x ∈ Zs L I ‖v‖ → act α x ∈ Zs L I ‖v‖ :=
    fun α x hx => Zs_act L I _ α hx
  have hZMc : ∀ (c : ℂ) {x : Vsp dim}, x ∈ Zs L I ‖v‖ → Mc σ c x ∈ Zs L I ‖v‖ :=
    fun c x hx => Mc_mem σ (Zs L I ‖v‖) hZact c hx
  have hvZ : v ∈ Zs L I ‖v‖ := Zs_self L I hvX le_rfl
  have hχZ : ∀ j < k, χ j ∈ Zs L I ‖v‖ := by
    intro j hj
    obtain ⟨μ, hμ, hμle⟩ := hflag j hj
    exact Zs_mono L I (hμle v hvX hvW) hμ
  have hshort : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → prj σ u ∈ W := by
    intro u hu huv
    by_contra h
    exact absurd (hvmin u hu h) (not_le.mpr huv)

  obtain ⟨U, hU⟩ : ∃ U : Submodule ℝ (Vsp dim), U = Submodule.span ℝ
      {x | ∃ c : ℂ, ∃ y ∈ Zs L I ‖v‖, prj σ y ∈ W ∧ x = Mc σ c y} := ⟨_, rfl⟩
  have hUgen : ∀ (c : ℂ) y, y ∈ Zs L I ‖v‖ → prj σ y ∈ W → Mc σ c y ∈ U := by
    intro c y hy hyW
    rw [hU]; exact Submodule.subset_span ⟨c, y, hy, hyW, rfl⟩
  have hUZ : U ≤ Zs L I ‖v‖ := by
    rw [hU]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨c, y, hy, -, rfl⟩
    exact hZMc c hy
  have hUprj : ∀ x ∈ U, prj σ x ∈ W := by
    intro x hx
    rw [hU] at hx
    refine prj_mem_of_span σ W _ ?_ hx
    rintro y ⟨c, y', -, hy', rfl⟩
    rw [prj_Mc]; exact W.smul_mem c hy'
  have hUMc : ∀ x ∈ U, Mc σ 1 x ∈ U := by
    intro x hx
    rw [hU] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, y', hy', hy'W, rfl⟩ := hy
      rw [hMc1]; exact hUgen c y' hy' hy'W
    | zero => rw [map_zero]; exact U.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact U.add_mem ha hb
    | smul r a _ ha => rw [LinearMap.map_smul_of_tower]; exact U.smul_mem r ha

  haveI : CompleteSpace U := FiniteDimensional.complete ℝ U
  obtain ⟨y₀, hy₀U, z, hzU, hxyz⟩ := U.exists_add_mem_mem_orthogonal (Mc σ 1 v)
  have hz : z = Mc σ 1 v - y₀ := by rw [hxyz]; abel
  have hzZ : z ∈ Zs L I ‖v‖ := by
    rw [hz]; exact Submodule.sub_mem _ (hZMc 1 hvZ) (hUZ hy₀U)
  have hzperp : ∀ u ∈ U, inner ℝ (Mc σ 1 z) u = 0 := by
    intro u hu
    rw [real_inner_Mc, map_one]
    exact Submodule.inner_left_of_mem_orthogonal (hUMc u hu) hzU
  have hprjt₀ : prj σ (Mc σ 1 z) = prj σ v - prj σ y₀ := by
    rw [hprj1, hz, map_sub, hprj1]
  have hp0 : prj σ (Mc σ 1 z) ≠ 0 := by
    intro h0
    apply hvW
    have h' : prj σ v = prj σ y₀ := by rw [← sub_eq_zero, ← hprjt₀, h0]
    rw [h']; exact hUprj y₀ hy₀U
  have hWorth : ∀ w ∈ W, inner ℂ w (prj σ (Mc σ 1 z)) = 0 := by
    have hsub : W ≤ (Submodule.span ℂ {prj σ (Mc σ 1 z)})ᗮ := by
      refine hWχ.trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j < k := hj
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      have hH := orth_prj hiso σ (Zs_IR hIs _ (hZMc 1 hzZ))
        (fun c => Zs_IR hIs _ (hZMc c (hχZ j hj')))
        (fun c => hzperp _ (hUgen c _ (hχZ j hj') (hχW j hj')))
      have key : inner ℂ (prj σ (χ j)) (prj σ (Mc σ 1 z)) =
          Hf (prj σ (Mc σ 1 z)) (prj σ (χ j)) := by
        simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]
      rw [key]; exact hH
    intro w hw
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hsub hw)

  have hpn : 0 < ‖prj σ (Mc σ 1 z)‖ := norm_pos_iff.mpr hp0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = T / ‖prj σ (Mc σ 1 z)‖ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos hT hpn
  obtain ⟨t, ht⟩ : ∃ t : Vsp dim, t = r • Mc σ 1 z := ⟨_, rfl⟩
  have htZ : t ∈ Zs L I ‖v‖ := by rw [ht]; exact Submodule.smul_mem _ r (hZMc 1 hzZ)
  have hprjt : prj σ t = r • prj σ (Mc σ 1 z) := by rw [ht, prj_rsmul]
  have hnT : ‖prj σ t‖ = T := by
    rw [hprjt, norm_smul, Real.norm_of_nonneg hr0.le, hr, div_mul_cancel₀ _ hpn.ne']
  have hWt : ∀ w ∈ W, inner ℂ w (prj σ t) = 0 := by
    intro w hw
    rw [hprjt, ← Complex.coe_smul, inner_smul_right, hWorth w hw, mul_zero]
  have hMt : Mc σ 1 t = t := by rw [ht, LinearMap.map_smul_of_tower, hMc1]
  have htn : ‖t‖ ^ 2 = 2 * T ^ 2 := by
    have h := norm_projection_sq hiso σ t (by rw [hMt]; exact Zs_IR hIs _ htZ)
      (Zs_IR hIs _ (hZMc Complex.I htZ))
    rw [hMt, hnT] at h; exact h
  have htorth : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → inner ℝ t u = 0 := by
    intro u hu huv
    rw [ht, real_inner_smul_left, real_inner_Mc, map_one,
      Submodule.inner_left_of_mem_orthogonal
        (hUgen 1 u (Zs_self L I hu huv.le) (hshort u hu huv)) hzU, mul_zero]

  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : AddSubgroup (Vsp dim), Λ = Xg L I ⊓ (Zs L I ‖v‖).toAddSubgroup :=
    ⟨_, rfl⟩
  have hΛ : ∀ g, g ∈ Λ ↔ g ∈ Xg L I ∧ g ∈ Zs L I ‖v‖ := by
    intro g; rw [hΛdef, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
  obtain ⟨χ', hχ'Λ, hclose⟩ :=
    exists_closest Λ (fun g hg hg0 => hsep g ((hΛ g).1 hg).1 hg0) t

  obtain ⟨S', hS'⟩ : ∃ S' : Set (Vsp dim),
      S' = {x | ∃ j, ∃ y ∈ Xg L I, ‖y‖ ≤ ‖v‖ ∧ x = act (ω j) y} := ⟨_, rfl⟩
  have hS'Λ : ∀ x ∈ S', x ∈ Λ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    exact (hΛ _).2 ⟨Xg_act hLs hIs (ω j) hy, Zs_act L I _ (ω j) (Zs_self L I hy hyv)⟩
  have hS'norm : ∀ x ∈ S', ‖x‖ ≤ B * ‖v‖ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    have hB : 0 ≤ B := (norm_nonneg _).trans (hωB j σ)
    exact (norm_act_le (ω j) B (hωB j) y).trans (mul_le_mul_of_nonneg_left hyv hB)
  have hZS' : Zs L I ‖v‖ ≤ Submodule.span ℝ S' := by
    unfold Zs
    refine Submodule.span_le.mpr ?_
    rintro x ⟨α, y, hy, hyv, rfl⟩
    refine Submodule.span_mono ?_ (act_omega_expand ω hω α y)
    rintro _ ⟨j, rfl⟩
    rw [hS']
    exact ⟨j, y, hy, hyv, rfl⟩
  obtain ⟨b, hbS', hbspan, hbli⟩ := exists_linearIndependent ℝ S'
  have hli : LinearIndependent ℝ (fun x : b => (x : Vsp dim)) := hbli
  haveI : Finite b := hli.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin b
  obtain ⟨vv, hvvdef⟩ : ∃ vv : Fin n → Vsp dim, vv = fun i => ((e.symm i : b) : Vsp dim) :=
    ⟨_, rfl⟩
  have hvv : LinearIndependent ℝ vv := by
    rw [hvvdef]; exact hli.comp e.symm e.symm.injective
  have hvvS' : ∀ i, vv i ∈ S' := fun i => by rw [hvvdef]; exact hbS' (e.symm i).2
  have hrange : Set.range vv = b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; rw [hvvdef]; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by rw [hvvdef]; simp⟩
  have htspan : t ∈ Submodule.span ℝ (Set.range vv) := by
    rw [hrange, hbspan]; exact hZS' htZ
  obtain ⟨c, hc⟩ := hNP (Vsp dim) n vv hvv t htspan
  have hnD : (n : ℝ) ≤ D := by
    have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range vv)) = n := by
      rw [finrank_span_eq_card hvv, Fintype.card_fin]
    have h2 : Submodule.span ℝ (Set.range vv) ≤ IR I := by
      rw [hrange, hbspan]
      exact Submodule.span_le.mpr fun x hx => Zs_IR hIs _ ((hΛ x).1 (hS'Λ x hx)).2
    have h3 : n ≤ D := by rw [← h1]; exact (Submodule.finrank_mono h2).trans hD
    exact_mod_cast h3
  have hgΛ : (∑ i, (c i : ℝ) • vv i) ∈ Λ := by
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (hS'Λ _ (hvvS' i)) _
  have hsum : ∑ i, ‖vv i‖ ^ 2 ≤ n * (B * ‖v‖) ^ 2 := by
    calc ∑ i, ‖vv i‖ ^ 2 ≤ ∑ _i : Fin n, (B * ‖v‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => by gcongr; exact hS'norm _ (hvvS' i)
      _ = n * (B * ‖v‖) ^ 2 := by simp
  have hbound : ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 := by
    have h1 : ‖t - χ'‖ ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ := hclose _ hgΛ
    have h2 : ‖t - χ'‖ ^ 2 ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ ^ 2 := by gcongr
    have h3 : (n : ℝ) * (B * ‖v‖) ^ 2 ≤ D * (B * ‖v‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hnD (sq_nonneg _)
    rw [norm_sub_rev]
    linarith

  have hlast : ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
    intro u hu
    by_cases huv : ‖v‖ ≤ ‖u‖
    · exact Or.inr huv
    left
    push_neg at huv
    have huΛ : u ∈ Λ := (hΛ u).2 ⟨hu, Zs_self L I hu huv.le⟩
    have h1 := hclose (χ' + u) (Λ.add_mem hχ'Λ huΛ)
    have h2 := hclose (χ' - u) (Λ.sub_mem hχ'Λ huΛ)
    have e1 : t - (χ' + u) = (t - χ') - u := by abel
    have e2 : t - (χ' - u) = (t - χ') + u := by abel
    rw [e1] at h1
    rw [e2] at h2
    have s1 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') - u‖ ^ 2 := by gcongr
    have s2 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') + u‖ ^ 2 := by gcongr
    rw [norm_sub_sq_real (t - χ') u] at s1
    rw [norm_add_sq_real (t - χ') u] at s2
    have hi : inner ℝ (t - χ') u = - inner ℝ χ' u := by
      rw [inner_sub_left, htorth u hu huv, zero_sub]
    rw [hi] at s1 s2
    rw [abs_le]; constructor <;> linarith
  exact ⟨t, χ', hWt, hnT, htn, ((hΛ χ').1 hχ'Λ).1, ((hΛ χ').1 hχ'Λ).2, hbound, hlast⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
