import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorsLEOfIndex

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

section Dual

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem RS.p_zpow (z : ℤ) : (p : R.Kf) ^ z = algebraMap R.O R.Kf R.w ^ (2 * z) := by
  rw [R.p_eq, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem dual_bases (hD3 : DualHeightBasis) (lamO : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lamO)
    (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∃ (r : Fin (dimV R.Kf lamO) → Vsp R.Kf lamO) (ρ : Fin (dimV R.Kf lamO) → Module.Dual R.Kf (Vsp R.Kf lamO)),
      (∀ a, r a ∈ Re p R.ι R.σ R.w 1 lamO e) ∧ (∀ a, ρ a ∈ Re' p R.ι R.σ R.w 1 lamO e) ∧
      ∀ a b, be p 1 lamO (r a) (ρ b) = if a = b then 1 else 0 := by
  classical
  obtain ⟨x, π, -, -, -, -, hRe, hRe'⟩ := hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 lamO hdom e he
  refine ⟨fun a => (algebraMap R.O R.Kf R.w ^ (-order 1 lamO (π a))) • x a,
    fun b => (algebraMap R.O R.Kf R.w ^ (-order 1 lamO (π b)) * (p : R.Kf) ^ (-π b)) • x.coord b, ?_, ?_, ?_⟩
  · intro a
    rw [← hRe]
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro b
    rw [← hRe']
    exact Submodule.subset_span ⟨b, rfl⟩
  · intro a b
    unfold be
    rw [LinearMap.smul_apply, map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, smul_eq_mul, mul_one]
      rw [R.p_zpow, R.p_zpow, ← zpow_add₀ R.w_ne, ← zpow_add₀ R.w_ne, ← zpow_add₀ R.w_ne]
      have : -order 1 lamO (π a) + 2 * -π a + (2 * Ar 1 lamO + -order 1 lamO (π a)) = 0 := by
        unfold order
        ring
      rw [this, zpow_zero]
    · simp [hab]

end Dual

theorem tensor_bound_of_order_bound (hTen : RestTensor) (hOrd : RestOrdBound) (hD3 : DualHeightBasis) (hIncl : DualHeightInclusion) : ResidueClassCount := by
  classical
  intro p n' R m TT ccl aw bw lam0 hBase hDom t c₃ D κ hc hρ e he
  obtain ⟨μ, ν, hν, hHL, hHLe, hdim⟩ := hTen p n' R m TT lam0 hDom
  have hdomO : IsDominant (othW TT lam0) := othW_dom hDom
  have hsmall : ∀ s i, |othW TT lam0 s i| ≤ (ccl : ℤ) := by
    intro s i
    unfold othW
    split_ifs with hs
    · simp
    · exact (hBase s).2 hs i
  set wK : R.Kf := algebraMap R.O R.Kf R.w with hwK
  have hw : wK ≠ 0 := R.w_ne
  obtain ⟨r, ρ, hr, hρm, hrρ⟩ := dual_bases R hD3 (othW TT lam0) hdomO e he
  have hA := Ar_add TT lam0

  have hsrc : ∀ F ∈ CCL R (topW TT lam0) t c₃ e, ∀ a, μ F (r a) ∈ CCL R lam0 (t + (2 * n' * ccl)) (c₃ - (2 * n' * ccl)) e := by
    intro F hF a
    have hr0 := (hOrd p n' R m (othW TT lam0) ccl hdomO hsmall e he).1 (hr a)
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have h1 := mu_scale μ hF.1.1 hr0
      rw [← hHL e.src he.1, ← zpow_add₀ hw] at h1
      have : -(t : ℤ) + -((2 * n' * ccl : ℕ) : ℤ) = -((t + (2 * n' * ccl) : ℕ) : ℤ) := by push_cast; ring
      rwa [this] at h1
    · have h1 := mu_scale μ hF.1.2 (hr a)
      rw [← hHLe e he, ← zpow_add₀ hw] at h1
      have : -Ar 1 (topW TT lam0) + -Ar 1 (othW TT lam0) = -Ar 1 lam0 := by rw [hA]; ring
      rwa [this] at h1
    · rw [Submodule.mem_iInf]
      intro e'
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have hF' := scale_scale_mem (CCL_other R (topW TT lam0) t c₃ e e' h1 h2 h3 hF)
      have hinc := (hIncl p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 (othW TT lam0) hdomO e' h1).1
      rw [h2] at hinc
      have hr1 := scale_scale_mem (scale_mono _ hinc hr0)
      have h4 := mu_scale μ hF' hr1
      rw [← hHLe e' h1] at h4
      apply mem_scale_scale
      have : wK ^ (c₃ : ℤ) * wK ^ (-Ar 1 (topW TT lam0)) *
          (wK ^ (-((2 * n' * ccl : ℕ) : ℤ)) * wK ^ (-Ar 1 (othW TT lam0))) =
          wK ^ ((c₃ - (2 * n' * ccl) : ℕ) : ℤ) * wK ^ (-Ar 1 lam0) := by
        rw [← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hA, Nat.cast_sub hc]
        congr 1
        ring
      rwa [this] at h4

  have htst : ∀ G ∈ CCL' R (topW TT lam0) t c₃ e, ∀ a, ν G (ρ a) ∈ CCL' R lam0 (t + (2 * n' * ccl)) (c₃ - (2 * n' * ccl)) e := by
    intro G hG a
    have hr0 := (hOrd p n' R m (othW TT lam0) ccl hdomO hsmall e he).2 (hρm a)
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have h1 := nu_scale μ ν hν hG.1.1 hr0
      rw [← hHL e.tgt he.2.1, ← zpow_add₀ hw] at h1
      have : -(t : ℤ) + -((2 * n' * ccl : ℕ) : ℤ) = -((t + (2 * n' * ccl) : ℕ) : ℤ) := by push_cast; ring
      rwa [this] at h1
    · have h1 := nu_scale μ ν hν hG.1.2 (hρm a)
      rw [← hHLe e he, ← zpow_add₀ hw] at h1
      have : -Ar 1 (topW TT lam0) + -Ar 1 (othW TT lam0) = -Ar 1 lam0 := by rw [hA]; ring
      rwa [this] at h1
    · rw [Submodule.mem_iInf]
      intro e'
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have hG' := scale_scale_mem (CCL'_other R (topW TT lam0) t c₃ e e' h1 h2 h3 hG)
      have hinc := (hIncl p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 (othW TT lam0) hdomO e' h1).2
      rw [h2] at hinc
      have hr1 := scale_scale_mem (scale_mono _ hinc hr0)
      have h4 := nu_scale μ ν hν hG' hr1
      rw [← hHLe e' h1] at h4
      apply mem_scale_scale
      have : wK ^ (c₃ : ℤ) * wK ^ (-Ar 1 (topW TT lam0)) *
          (wK ^ (-((2 * n' * ccl : ℕ) : ℤ)) * wK ^ (-Ar 1 (othW TT lam0))) =
          wK ^ ((c₃ - (2 * n' * ccl) : ℕ) : ℤ) * wK ^ (-Ar 1 lam0) := by
        rw [← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hA, Nat.cast_sub hc]
        congr 1
        ring
      rwa [this] at h4

  have hbe : ∀ F G a b, be p 1 lam0 (μ F (r a)) (ν G (ρ b)) =
      be p 1 (topW TT lam0) F G * (if a = b then 1 else 0) := by
    intro F G a b
    rw [← hrρ a b]
    unfold be
    have hp0 : (p : R.Kf) ≠ 0 := by rw [R.p_eq]; exact pow_ne_zero _ hw
    rw [map_smul, hν, map_smul, map_smul, hA, zpow_add₀ hp0]
    simp only [smul_eq_mul]
    ring
  obtain ⟨nT, hnT, hfac⟩ := hρ e he
  refine ⟨nT * (dimV R.Kf (othW TT lam0)), ?_, ?_⟩
  · have h1 : dL R lam0 = dL R (topW TT lam0) * (dimV R.Kf (othW TT lam0)) := by
      unfold dL
      rw [hdim]
      push_cast
      ring
    rw [h1, ← mul_assoc]
    push_cast
    exact mul_le_mul_of_nonneg_right hnT (Nat.cast_nonneg _)
  · rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
    · exact Or.inl (by rw [h0, zero_mul])
    · refine FactorsLE_of_index (I := Fin nT × Fin (dimV R.Kf (othW TT lam0))) (nT * (dimV R.Kf (othW TT lam0))) (by simp)
        (fun i => μ (x i.1) (r i.2)) (fun l => ν (y l.1) (ρ l.2)) (fun i => hsrc _ (hx i.1) i.2)
        (fun l => htst _ (hy l.1) l.2) z (Matrix.of fun l j => if l.2 = j.2 then M l.1 j.1 else 0) hz hv ?_
      rintro ⟨i, a⟩ ⟨j, b⟩
      rw [Fintype.sum_prod_type]
      simp only [hbe, Matrix.of_apply]
      have h2 : ∀ l : Fin nT, ∑ b' : Fin (dimV R.Kf (othW TT lam0)), be p 1 (topW TT lam0) (x i) (y l) * (if a = b' then 1 else 0) *
          algebraMap R.O R.Kf (if b' = b then M l j else 0) =
          if a = b then be p 1 (topW TT lam0) (x i) (y l) * algebraMap R.O R.Kf (M l j) else 0 := by
        intro l
        rw [Finset.sum_eq_single a]
        · by_cases hab : a = b <;> simp [hab]
        · intro b' _ hb'
          simp [Ne.symm hb']
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h2]
      by_cases hab : a = b
      · subst hab
        simp only [if_true]
        rw [hM i j]
        by_cases hij : i = j
        · subst hij; simp
        · have : ((i, a) : Fin nT × Fin (dimV R.Kf (othW TT lam0))) ≠ (j, a) := fun h => hij (Prod.mk.inj h).1
          rw [if_neg hij, if_neg this]
      · have : ((i, a) : Fin nT × Fin (dimV R.Kf (othW TT lam0))) ≠ (j, b) := fun h => hab (Prod.mk.inj h).2
        simp [hab, this]

end Formalism.MainNotions.flipOneThree.Pf

end
