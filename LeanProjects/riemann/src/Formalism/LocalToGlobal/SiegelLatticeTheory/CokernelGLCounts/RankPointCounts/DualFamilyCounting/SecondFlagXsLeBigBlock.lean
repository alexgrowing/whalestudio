import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal

noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')

def BB : Submodule (𝓞 D.host.E) (VS D).V := MMg D F0 F' ⊔ XS D F0 ⊔ XS D F'.fl

theorem natsmul_mem (n : ℕ) {N : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ N) :
    ((n : ℕ) : D.host.E) • x ∈ N := by
  have := N.smul_mem ((n : ℕ) : 𝓞 D.host.E) hx
  rwa [smulO, map_natCast] at this

theorem f'_eq (b : Fin (D.R.rS + 1)) : F'.fl.fvec b = F0.fvec b +
    ((gS D : ℕ) : D.host.E) • ((((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
  rw [smul_smul, mul_inv_cancel₀ (g_ne D), one_smul, add_sub_cancel]

theorem f_mem_MMg (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ MMg D F0 F' :=
  Submodule.subset_span (Or.inl ⟨i, rfl⟩)

theorem m_mem_MMg (b : Fin (D.R.rS + 1)) :
    (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b) ∈ MMg D F0 F' :=
  Submodule.subset_span (Or.inr ⟨b, rfl⟩)

theorem f'_mem_MMg (b : Fin (D.R.rS + 1)) : F'.fl.fvec b ∈ MMg D F0 F' := by
  rw [f'_eq D F0 F' b]
  exact Submodule.add_mem _ (f_mem_MMg D F0 F' b) (natsmul_mem D _ (m_mem_MMg D F0 F' b))

theorem e_mem_MMg (a : Fin D.R.rS) : F0.e a ∈ MMg D F0 F' := by
  rw [← fvec_cast]; exact f_mem_MMg D F0 F' _

theorem z_mem_MMg : F0.z ∈ MMg D F0 F' := by
  rw [← fvec_last]; exact f_mem_MMg D F0 F' _

theorem e'_mem_MMg (a : Fin D.R.rS) : F'.fl.e a ∈ MMg D F0 F' := by
  rw [← fvec_cast]; exact f'_mem_MMg D F0 F' _

theorem z'_mem_MMg : F'.fl.z ∈ MMg D F0 F' := by
  rw [← fvec_last]; exact f'_mem_MMg D F0 F' _

theorem MMg_le_BB : MMg D F0 F' ≤ BB D F0 F' := le_sup_left.trans le_sup_left

theorem flag_xs_le_big_block : XS D F0 ≤ BB D F0 F' := le_sup_right.trans le_sup_left

theorem second_flag_xs_le_big_block : XS D F'.fl ≤ BB D F0 F' := le_sup_right

theorem UUS_le_BB : UUS D F0 F' ≤ BB D F0 F' := by
  refine sup_le (sup_le (sup_le (flag_xs_le_big_block D F0 F') ?_) (second_flag_xs_le_big_block D F0 F')) ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact MMg_le_BB D F0 F' (z_mem_MMg D F0 F')
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact MMg_le_BB D F0 F' (z'_mem_MMg D F0 F')

theorem f_mem_U (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ UPair D F0 F' :=
  Submodule.subset_span (Or.inl ⟨i, rfl⟩)

theorem f'_mem_U (i : Fin (D.R.rS + 1)) : F'.fl.fvec i ∈ UPair D F0 F' :=
  Submodule.subset_span (Or.inr ⟨i, rfl⟩)

theorem flag_x_le_pair_span : F0.X ≤ UPair D F0 F' := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [← fvec_cast]; exact f_mem_U D F0 F' _

theorem second_flag_x_le_pair_span : F'.fl.X ≤ UPair D F0 F' := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [← fvec_cast]; exact f'_mem_U D F0 F' _

theorem BB_le_U : BB D F0 F' ≤ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
  refine sup_le (sup_le ?_ ((XS_le_X D F0).trans ?_)) ((XS_le_X D F'.fl).trans ?_)
  · rw [MMg, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · exact f_mem_U D F0 F' i
    · exact (UPair D F0 F').smul_mem _ ((UPair D F0 F').sub_mem (f'_mem_U D F0 F' b) (f_mem_U D F0 F' b))
  · exact flag_x_le_pair_span D F0 F'
  · exact second_flag_x_le_pair_span D F0 F'

theorem loc_BB_g (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') = Formalism.HermitianLatticesTheory.localization₂ P (MMg D F0 F') := by
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (sup_le (sup_le (Formalism.L2.SG.Pf.le_locP' _ _) ?_) ?_))
    (Formalism.L2.SG.Pf.localization_mono' (MMg_le_BB D F0 F'))
  · refine (XS_le_locP_e D F0 P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
    rintro _ ⟨a, rfl⟩; exact e_mem_MMg D F0 F' a
  · refine (XS_le_locP_e D F'.fl P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
    rintro _ ⟨a, rfl⟩; exact e'_mem_MMg D F0 F' a

theorem loc_BB_ng (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∉ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') = Formalism.HermitianLatticesTheory.localization₂ P (UUS D F0 F') := by
  have hX0 : XS D F0 ≤ UUS D F0 F' := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hX1 : XS D F'.fl ≤ UUS D F0 F' := le_sup_right.trans le_sup_left
  have hz0 : F0.z ∈ UUS D F0 F' :=
    (show Submodule.span (𝓞 D.host.E) {F0.z} ≤ UUS D F0 F' from
      le_sup_right.trans (le_sup_left.trans le_sup_left)) (Submodule.mem_span_singleton_self _)
  have hz1 : F'.fl.z ∈ UUS D F0 F' :=
    (show Submodule.span (𝓞 D.host.E) {F'.fl.z} ≤ UUS D F0 F' from le_sup_right)
      (Submodule.mem_span_singleton_self _)
  have hf0 : ∀ i, F0.fvec i ∈ UUS D F0 F' := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [fvec_last]; exact hz0
    | cast a => rw [fvec_cast]; exact hX0 (e_mem_XS D F0 a)
  have hf1 : ∀ i, F'.fl.fvec i ∈ UUS D F0 F' := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [fvec_last]; exact hz1
    | cast a => rw [fvec_cast]; exact hX1 (e_mem_XS D F'.fl a)
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (sup_le (sup_le ?_ ?_) ?_))
    (Formalism.L2.SG.Pf.localization_mono' (UUS_le_BB D F0 F'))
  · rw [MMg, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · exact Formalism.L2.SG.Pf.le_locP' _ _ (hf0 i)
    · refine ⟨((gS D : ℕ) : 𝓞 D.host.E), hg, ?_⟩
      rw [smulO, map_natCast, smul_smul, mul_inv_cancel₀ (g_ne D), one_smul]
      exact Submodule.sub_mem _ (hf1 b) (hf0 b)
  · exact hX0.trans (Formalism.L2.SG.Pf.le_locP' _ _)
  · exact hX1.trans (Formalism.L2.SG.Pf.le_locP' _ _)

theorem MMof_eq : MMof D F0 F' = BB D F0 F' := by
  have key : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (haveI := P.isPrime; if ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal then Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F')
        else Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F')) =
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BB D F0 F')) := by
    intro P
    have := P.isPrime
    split_ifs with hg
    · exact (loc_BB_g D F0 F' P.asIdeal hg).symm
    · exact (loc_BB_ng D F0 F' P.asIdeal hg).symm
  refine le_antisymm ?_ ?_
  · intro x hx
    apply Formalism.L2.SG.Pf.mem_of_forall_prime
    intro P
    have := P.isPrime
    have h1 := (Submodule.mem_iInf _).1 hx P
    rw [key P] at h1
    exact h1
  · refine le_iInf fun P => ?_
    have := P.isPrime
    rw [key P]
    exact Formalism.L2.SG.Pf.le_locP' _ _

theorem BB_latIn : IsLatIn (UPair D F0 F') (BB D F0 F') := by
  refine ⟨?_, le_antisymm (Submodule.span_le.2 (BB_le_U D F0 F')) ?_⟩
  · refine Submodule.FG.sup (Submodule.FG.sup ?_ (XS_fg D F0)) (XS_fg D F'.fl)
    exact Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))
  · rw [UPair, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Submodule.subset_span (MMg_le_BB D F0 F' (f_mem_MMg D F0 F' i))
    · exact Submodule.subset_span (MMg_le_BB D F0 F' (f'_mem_MMg D F0 F' i))

section Coord

variable {D F0 F'}
variable (hw : LinearIndependent D.host.E (Sum.elim F0.fvec F'.fl.fvec))
include hw

theorem coord_eq {α β α' β' : Fin (D.R.rS + 1) → D.host.E}
    (h : ∑ i, α i • F0.fvec i + ∑ j, β j • F'.fl.fvec j = ∑ i, α' i • F0.fvec i + ∑ j, β' j • F'.fl.fvec j) :
    α = α' ∧ β = β' := by
  have h0 := Fintype.linearIndependent_iff.1 hw (Sum.elim (α - α') (β - β')) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, h, sub_self])
  exact ⟨funext fun i => sub_eq_zero.1 (h0 (Sum.inl i)), funext fun j => sub_eq_zero.1 (h0 (Sum.inr j))⟩

theorem indep4 {x1 x2 : (VS D).V} (h1 : x1 ∈ F0.X) (h2 : x2 ∈ F'.fl.X) {a a' : D.host.E}
    (h : x1 + a • F0.z + (x2 + a' • F'.fl.z) = 0) : x1 = 0 ∧ a = 0 ∧ x2 = 0 ∧ a' = 0 := by
  obtain ⟨c1, rfl⟩ := (mem_X_iff F0).1 h1
  obtain ⟨c2, rfl⟩ := (mem_X_iff F'.fl).1 h2
  rw [← sum_fvec, ← sum_fvec] at h
  obtain ⟨hα, hβ⟩ := coord_eq hw (α' := 0) (β' := 0) (by simpa using h)
  have hc1 : ∀ i, c1 i = 0 := fun i => by simpa using congrFun hα (Fin.castSucc i)
  have hc2 : ∀ i, c2 i = 0 := fun i => by simpa using congrFun hβ (Fin.castSucc i)
  refine ⟨by simp [hc1], by simpa using congrFun hα (Fin.last _), by simp [hc2],
    by simpa using congrFun hβ (Fin.last _)⟩

end Coord

theorem mmg_coord {v : (VS D).V} (hv : v ∈ MMg D F0 F') : ∃ o1 o2 : Fin (D.R.rS + 1) → 𝓞 D.host.E,
    v = ∑ i, (algebraMap (𝓞 D.host.E) D.host.E (o1 i) -
        algebraMap (𝓞 D.host.E) D.host.E (o2 i) * (((gS D : ℕ) : D.host.E))⁻¹) • F0.fvec i +
      ∑ j, (algebraMap (𝓞 D.host.E) D.host.E (o2 j) * (((gS D : ℕ) : D.host.E))⁻¹) • F'.fl.fvec j := by
  have hs : MMg D F0 F' = Submodule.span (𝓞 D.host.E) (Set.range (Sum.elim F0.fvec
      (fun b => (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)))) := by
    rw [Set.Sum.elim_range]; rfl
  rw [hs, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  refine ⟨fun i => c (Sum.inl i), fun j => c (Sum.inr j), ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, smulO, smul_sub, sub_smul, smul_smul, Finset.sum_sub_distrib]
  abel

theorem uus_coord {v : (VS D).V} (hv : v ∈ UUS D F0 F') : ∃ x1 ∈ XS D F0, ∃ o : 𝓞 D.host.E,
    ∃ x2 ∈ XS D F'.fl, ∃ o' : 𝓞 D.host.E,
      v = x1 + algebraMap (𝓞 D.host.E) D.host.E o • F0.z + (x2 + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z) := by
  obtain ⟨y, hy, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨y', hy', x2, hx2, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨x1, hx1, w1, hw1, rfl⟩ := Submodule.mem_sup.1 hy'
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw1
  obtain ⟨o', rfl⟩ := Submodule.mem_span_singleton.1 hw2
  refine ⟨x1, hx1, o, x2, hx2, o', ?_⟩
  rw [smulO, smulO]
  abel

end Formalism.L2.SG.Pf.Cnt.R3
