import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SecondFlagXsLeBigBlock

noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'}
variable (hw : LinearIndependent D.host.E (Sum.elim F0.fvec F'.fl.fvec))
include hw

theorem u1 {v : (VS D).V} (hv : v ∈ MMg D F0 F') (hX : v ∈ F0.X) :
    v ∈ Submodule.span (𝓞 D.host.E) (Set.range F0.e) := by
  obtain ⟨o1, o2, h⟩ := mmg_coord D F0 F' hv
  obtain ⟨c, rfl⟩ := (mem_X_iff F0).1 hX
  rw [show ∑ i, c i • F0.e i = ∑ i, (Fin.snoc (α := fun _ => D.host.E) c 0 : _ → _) i • F0.fvec i +
      ∑ j, (0 : Fin (D.R.rS + 1) → D.host.E) j • F'.fl.fvec j by
    rw [sum_fvec]; simp only [zero_smul, add_zero, Pi.zero_apply, Finset.sum_const_zero]] at h
  obtain ⟨hα, hβ⟩ := coord_eq hw h
  have hc : ∀ a, c a = algebraMap (𝓞 D.host.E) D.host.E (o1 (Fin.castSucc a)) := by
    intro a
    have h1 := congrFun hα (Fin.castSucc a)
    have h2 := congrFun hβ (Fin.castSucc a)
    simp only [Fin.snoc_castSucc, Pi.zero_apply] at h1 h2
    rw [h1, ← h2, sub_zero]
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun a => o1 (Fin.castSucc a), by simp only [hc, smulO]⟩

theorem u2 {c : D.host.E} {x : (VS D).V} (hv : c • F0.z - x ∈ MMg D F0 F') (hx : x ∈ F0.X) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c := by
  obtain ⟨o1, o2, h⟩ := mmg_coord D F0 F' hv
  obtain ⟨d, rfl⟩ := (mem_X_iff F0).1 hx
  rw [show c • F0.z - ∑ i, d i • F0.e i =
      ∑ i, (Fin.snoc (α := fun _ => D.host.E) (-d) c : _ → _) i • F0.fvec i +
      ∑ j, (0 : Fin (D.R.rS + 1) → D.host.E) j • F'.fl.fvec j by
    rw [sum_fvec]
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    abel] at h
  obtain ⟨hα, hβ⟩ := coord_eq hw h
  have h1 := congrFun hα (Fin.last _)
  have h2 := congrFun hβ (Fin.last _)
  simp only [Fin.snoc_last, Pi.zero_apply] at h1 h2
  exact ⟨o1 (Fin.last _), by rw [h1, ← h2, sub_zero]⟩

theorem u3 {v : (VS D).V} (hv : v ∈ MMg D F0 F') (hX : v ∈ F'.fl.X) :
    v ∈ Submodule.span (𝓞 D.host.E) (Set.range F'.fl.e) := by
  obtain ⟨o1, o2, h⟩ := mmg_coord D F0 F' hv
  obtain ⟨c, rfl⟩ := (mem_X_iff F'.fl).1 hX
  rw [show ∑ i, c i • F'.fl.e i = ∑ i, (0 : Fin (D.R.rS + 1) → D.host.E) i • F0.fvec i +
      ∑ j, (Fin.snoc (α := fun _ => D.host.E) c 0 : _ → _) j • F'.fl.fvec j by
    rw [sum_fvec]; simp only [zero_smul, add_zero, zero_add, Pi.zero_apply, Finset.sum_const_zero]] at h
  obtain ⟨hα, hβ⟩ := coord_eq hw h
  have hc : ∀ a, c a = algebraMap (𝓞 D.host.E) D.host.E (o1 (Fin.castSucc a)) := by
    intro a
    have h1 := congrFun hα (Fin.castSucc a)
    have h2 := congrFun hβ (Fin.castSucc a)
    simp only [Fin.snoc_castSucc, Pi.zero_apply] at h1 h2
    rw [h2]
    linear_combination h1
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun a => o1 (Fin.castSucc a), by simp only [hc, smulO]⟩

theorem u4 {c : D.host.E} {x : (VS D).V} (hv : c • F'.fl.z - x ∈ MMg D F0 F') (hx : x ∈ F'.fl.X) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c := by
  obtain ⟨o1, o2, h⟩ := mmg_coord D F0 F' hv
  obtain ⟨d, rfl⟩ := (mem_X_iff F'.fl).1 hx
  rw [show c • F'.fl.z - ∑ i, d i • F'.fl.e i =
      ∑ i, (0 : Fin (D.R.rS + 1) → D.host.E) i • F0.fvec i +
      ∑ j, (Fin.snoc (α := fun _ => D.host.E) (-d) c : _ → _) j • F'.fl.fvec j by
    rw [sum_fvec]
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add]
    abel] at h
  obtain ⟨hα, hβ⟩ := coord_eq hw h
  have h1 := congrFun hα (Fin.last _)
  have h2 := congrFun hβ (Fin.last _)
  simp only [Fin.snoc_last, Pi.zero_apply] at h1 h2
  exact ⟨o1 (Fin.last _), by rw [h2]; linear_combination -h1⟩

theorem v1 {v : (VS D).V} (hX : v ∈ F0.X) (hv : v ∈ UUS D F0 F') : v ∈ XS D F0 := by
  obtain ⟨x1, hx1, o, x2, hx2, o', h⟩ := uus_coord D F0 F' hv
  have h0 : (x1 - v) + algebraMap (𝓞 D.host.E) D.host.E o • F0.z +
      (x2 + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z) = 0 := by
    rw [h]; abel
  have := (indep4 hw (F0.X.sub_mem (XS_le_X D F0 hx1) hX) (XS_le_X D F'.fl hx2) h0).1
  rw [sub_eq_zero] at this
  rw [← this]; exact hx1

theorem v2 {c : D.host.E} {x : (VS D).V} (hv : c • F0.z - x ∈ UUS D F0 F') (hx : x ∈ F0.X) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c := by
  obtain ⟨x1, hx1, o, x2, hx2, o', h⟩ := uus_coord D F0 F' hv
  have h0 : (x1 + x) + (algebraMap (𝓞 D.host.E) D.host.E o - c) • F0.z +
      (x2 + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z) = 0 := by
    have e : (x1 + x) + (algebraMap (𝓞 D.host.E) D.host.E o - c) • F0.z +
        (x2 + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z) =
        (x1 + algebraMap (𝓞 D.host.E) D.host.E o • F0.z +
          (x2 + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z)) - (c • F0.z - x) := by
      rw [sub_smul]; abel
    rw [e, ← h, sub_self]
  have := (indep4 hw (F0.X.add_mem (XS_le_X D F0 hx1) hx) (XS_le_X D F'.fl hx2) h0).2.1
  exact ⟨o, sub_eq_zero.1 this⟩

theorem v3 {v : (VS D).V} (hX : v ∈ F'.fl.X) (hv : v ∈ UUS D F0 F') : v ∈ XS D F'.fl := by
  obtain ⟨x1, hx1, o, x2, hx2, o', h⟩ := uus_coord D F0 F' hv
  have h0 : x1 + algebraMap (𝓞 D.host.E) D.host.E o • F0.z +
      ((x2 - v) + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z) = 0 := by
    rw [h]; abel
  have := (indep4 hw (XS_le_X D F0 hx1) (F'.fl.X.sub_mem (XS_le_X D F'.fl hx2) hX) h0).2.2.1
  rw [sub_eq_zero] at this
  rw [← this]; exact hx2

theorem v4 {c : D.host.E} {x : (VS D).V} (hv : c • F'.fl.z - x ∈ UUS D F0 F') (hx : x ∈ F'.fl.X) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c := by
  obtain ⟨x1, hx1, o, x2, hx2, o', h⟩ := uus_coord D F0 F' hv
  have h0 : x1 + algebraMap (𝓞 D.host.E) D.host.E o • F0.z +
      ((x2 + x) + (algebraMap (𝓞 D.host.E) D.host.E o' - c) • F'.fl.z) = 0 := by
    have e : x1 + algebraMap (𝓞 D.host.E) D.host.E o • F0.z +
        ((x2 + x) + (algebraMap (𝓞 D.host.E) D.host.E o' - c) • F'.fl.z) =
        (x1 + algebraMap (𝓞 D.host.E) D.host.E o • F0.z +
          (x2 + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z)) - (c • F'.fl.z - x) := by
      rw [sub_smul]; abel
    rw [e, ← h, sub_self]
  have := (indep4 hw (XS_le_X D F0 hx1) (F'.fl.X.add_mem (XS_le_X D F'.fl hx2) hx) h0).2.2.2
  exact ⟨o', sub_eq_zero.1 this⟩

variable {Λ : Submodule (𝓞 D.host.E) (VS D).V}
  (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F')
include hB

theorem mem_BB_of {v : (VS D).V} (hvΛ : v ∈ Λ) (hvU : v ∈ UPair D F0 F') : v ∈ BB D F0 F' := by
  rw [← hB]; exact ⟨hvΛ, hvU⟩

theorem BB_le_Lam : BB D F0 F' ≤ Λ := by
  rw [← hB]; exact inf_le_left

theorem loc_cases {v : (VS D).V} (hv : v ∈ BB D F0 F') (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ((((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • v ∈ MMg D F0 F') ∧
    ((((gS D : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • v ∈ UUS D F0 F') := by
  have := P.isPrime
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · have h1 : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F') := by
      rw [← loc_BB_g D F0 F' P.asIdeal hg]; exact Formalism.L2.SG.Pf.le_locP' _ _ hv
    obtain ⟨s, hs, hsv⟩ := h1
    exact ⟨s, hs, hsv⟩
  · have h1 : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F') := by
      rw [← loc_BB_ng D F0 F' P.asIdeal hg]; exact Formalism.L2.SG.Pf.le_locP' _ _ hv
    obtain ⟨s, hs, hsv⟩ := h1
    exact ⟨s, hs, hsv⟩

theorem xlam0 : XLam Λ (lf D F0) = XS D F0 := by
  apply le_antisymm
  · rintro v ⟨hvΛ, hvX⟩
    have hvX' : v ∈ F0.X := hvX
    have hvB := mem_BB_of hw hB hvΛ (flag_x_le_pair_span D F0 F' hvX')
    apply Formalism.L2.SG.Pf.mem_of_forall_prime
    intro P
    by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hvB P).1 hg
      refine ⟨s, hs, ?_⟩
      have h2 := u1 hw hsv (F0.X.smul_of_tower_mem s hvX')
      exact (Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact e_mem_XS D F0 a)) h2
    · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hvB P).2 hg
      exact ⟨s, hs, v1 hw (F0.X.smul_of_tower_mem s hvX') hsv⟩
  · intro v hv
    exact ⟨BB_le_Lam hw hB (flag_xs_le_big_block D F0 F' hv), XS_le_X D F0 hv⟩

theorem xlam1 : XLam Λ F' = XS D F'.fl := by
  apply le_antisymm
  · rintro v ⟨hvΛ, hvX⟩
    have hvX' : v ∈ F'.fl.X := hvX
    have hvB := mem_BB_of hw hB hvΛ (second_flag_x_le_pair_span D F0 F' hvX')
    apply Formalism.L2.SG.Pf.mem_of_forall_prime
    intro P
    by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hvB P).1 hg
      refine ⟨s, hs, ?_⟩
      have h2 := u3 hw hsv (F'.fl.X.smul_of_tower_mem s hvX')
      exact (Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact e_mem_XS D F'.fl a)) h2
    · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hvB P).2 hg
      exact ⟨s, hs, v3 hw (F'.fl.X.smul_of_tower_mem s hvX') hsv⟩
  · intro v hv
    exact ⟨BB_le_Lam hw hB (second_flag_xs_le_big_block D F0 F' hv), XS_le_X D F'.fl hv⟩

omit hB in
theorem z_ne : F0.z ≠ 0 := by
  have := hw.ne_zero (Sum.inl (Fin.last _))
  simpa [fvec_last] using this

omit hB in
theorem z'_ne : F'.fl.z ≠ 0 := by
  have := hw.ne_zero (Sum.inr (Fin.last _))
  simpa [fvec_last] using this

omit hB in
theorem coeff_of_span {z : (VS D).V} (hz : z ≠ 0) {c : D.host.E}
    (h : c • z ∈ Submodule.span (𝓞 D.host.E) {z}) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 h
  rw [smulO] at ho
  exact ⟨o, smul_left_injective D.host.E hz ho⟩

theorem prim0 (c : D.host.E) (hc : c • F0.z ∈ Lsub Λ (lf D F0)) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hc.1
  have hx' : x ∈ F0.X := hx
  have hl' : c • F0.z - x = l := by rw [← hlx]; abel
  have hzU : F0.z ∈ UPair D F0 F' := by rw [← fvec_last]; exact f_mem_U D F0 F' _
  have hlB : c • F0.z - x ∈ BB D F0 F' := by
    refine mem_BB_of hw hB (hl' ▸ hl.1) ?_
    exact (UPair D F0 F').sub_mem ((UPair D F0 F').smul_mem c hzU) (flag_x_le_pair_span D F0 F' hx')
  refine coeff_of_span hw (z_ne hw) ?_
  apply Formalism.L2.SG.Pf.mem_of_forall_prime
  intro P
  have e1 : ∀ s : 𝓞 D.host.E, s • (c • F0.z - x) =
      (algebraMap (𝓞 D.host.E) D.host.E s * c) • F0.z - s • x := by
    intro s; rw [smul_sub, smulO D s (c • _), smul_smul]
  have fin : ∀ s : 𝓞 D.host.E, (∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o =
      algebraMap (𝓞 D.host.E) D.host.E s * c) → s • c • F0.z ∈ Submodule.span (𝓞 D.host.E) {F0.z} := by
    rintro s ⟨o, ho⟩
    rw [smulO, smul_smul, ← ho, ← smulO]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hlB P).1 hg
    rw [e1] at hsv
    exact ⟨s, hs, fin s (u2 hw hsv (F0.X.smul_of_tower_mem s hx'))⟩
  · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hlB P).2 hg
    rw [e1] at hsv
    exact ⟨s, hs, fin s (v2 hw hsv (F0.X.smul_of_tower_mem s hx'))⟩

theorem prim1 (c : D.host.E) (hc : c • F'.fl.z ∈ Lsub Λ F') : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hc.1
  have hx' : x ∈ F'.fl.X := hx
  have hl' : c • F'.fl.z - x = l := by rw [← hlx]; abel
  have hzU : F'.fl.z ∈ UPair D F0 F' := by rw [← fvec_last]; exact f'_mem_U D F0 F' _
  have hlB : c • F'.fl.z - x ∈ BB D F0 F' := by
    refine mem_BB_of hw hB (hl' ▸ hl.1) ?_
    exact (UPair D F0 F').sub_mem ((UPair D F0 F').smul_mem c hzU) (second_flag_x_le_pair_span D F0 F' hx')
  refine coeff_of_span hw (z'_ne hw) ?_
  apply Formalism.L2.SG.Pf.mem_of_forall_prime
  intro P
  have e1 : ∀ s : 𝓞 D.host.E, s • (c • F'.fl.z - x) =
      (algebraMap (𝓞 D.host.E) D.host.E s * c) • F'.fl.z - s • x := by
    intro s; rw [smul_sub, smulO D s (c • _), smul_smul]
  have fin : ∀ s : 𝓞 D.host.E, (∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o =
      algebraMap (𝓞 D.host.E) D.host.E s * c) → s • c • F'.fl.z ∈ Submodule.span (𝓞 D.host.E) {F'.fl.z} := by
    rintro s ⟨o, ho⟩
    rw [smulO, smul_smul, ← ho, ← smulO]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hlB P).1 hg
    rw [e1] at hsv
    exact ⟨s, hs, fin s (u4 hw hsv (F'.fl.X.smul_of_tower_mem s hx'))⟩
  · obtain ⟨s, hs, hsv⟩ := (loc_cases hw hB hlB P).2 hg
    rw [e1] at hsv
    exact ⟨s, hs, fin s (v4 hw hsv (F'.fl.X.smul_of_tower_mem s hx'))⟩

end Formalism.L2.SG.Pf.Cnt.R3
