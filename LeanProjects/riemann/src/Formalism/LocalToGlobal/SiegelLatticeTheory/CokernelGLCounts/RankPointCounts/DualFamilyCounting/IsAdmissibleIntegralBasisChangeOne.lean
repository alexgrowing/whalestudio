import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CoeffOfSpan

noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem frameAct_one (f : Fin (r + 1) → S.V) (b : Fin (r + 1)) : frameAct f 1 b = f b := by
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Matrix.one_apply_ne hab]
  · simp

end General

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'}
  {Λ : Submodule (𝓞 D.host.E) (VS D).V}

theorem f_mem_UUS (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F0.fvec (Fin.last _) = F0.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · have e : F0.fvec (Fin.castSucc a) = F0.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem f'_mem_UUS (i : Fin (D.R.rS + 1)) : F'.fl.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F'.fl.fvec (Fin.last _) = F'.fl.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · have e : F'.fl.fvec (Fin.castSucc a) = F'.fl.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem spanE_UUS : spanE (VS D) (UUS D F0 F') = UPair D F0 F' := by
  apply le_antisymm
  · unfold spanE
    rw [Submodule.span_le]
    intro y hy
    have hle : UUS D F0 F' ≤ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
      unfold UUS
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inl ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inr ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inr ⟨Fin.last _, by simp [FlagG.fvec]⟩)
    exact hle hy
  · unfold UPair
    rw [Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Submodule.subset_span (f_mem_UUS i)
    · exact Submodule.subset_span (f'_mem_UUS i)

theorem UU_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    UU Λ (lf D F0) F' = UUS D F0 F' := by
  unfold UU
  rw [hX0, hX1, hz]
  rfl

theorem blat_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    BLat Λ (lf D F0) F' = Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
  unfold BLat UUE
  rw [UU_eq hX0 hX1 hz, spanE_UUS]

theorem mplus1_loc (hX0 : XLam Λ (lf D F0) = XS D F0) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (Mplus Λ (gS D) (lf D F0) F' 1) = Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') := by
  rw [loc_BB_g D F0 F' P hg]
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (Submodule.span_le.2 ?_))
    (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
  · rintro v ((hv | hv) | ⟨b, rfl⟩)
    · have hv' : v ∈ XS D F0 := by rw [← hX0]; exact hv
      refine ((XS_le_locP_e D F0 P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))) hv'
      rintro _ ⟨a, rfl⟩; exact e_mem_MMg D F0 F' a
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact Formalism.L2.SG.Pf.le_locP' _ _ (z_mem_MMg D F0 F')
    · refine Formalism.L2.SG.Pf.le_locP' _ _ ?_
      simp only [frame, frameAct_one]
      exact m_mem_MMg D F0 F' b
  · rintro v (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · induction i using Fin.lastCases with
      | last => rw [fvec_last]; exact Submodule.subset_span (Or.inl (Or.inr rfl))
      | cast a =>
        rw [fvec_cast]
        refine Submodule.subset_span (Or.inl (Or.inl ?_))
        rw [hX0]; exact e_mem_XS D F0 a
    · refine Submodule.subset_span (Or.inr ⟨b, ?_⟩)
      simp only [frame, frameAct_one]

theorem isAdmissibleIntegralBasisChange_one (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    AdmWit Λ (gS D) (lf D F0) F' 1 := by
  refine ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a, fun b P _ => ?_⟩
  have := P.isPrime
  have hm : (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b) ∈ Λ := by
    have := MMg_le_BB D F0 F' (m_mem_MMg D F0 F' b)
    rw [← hB] at this
    exact this.1
  refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
  rw [one_smul]
  have e : frame F' b - frameAct (frame (lf D F0)) 1 b =
      ((gS D : ℕ) : 𝓞 D.host.E) • ((((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
    rw [frameAct_one, smulO, map_natCast, smul_smul, mul_inv_cancel₀ (g_ne D), one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm

theorem forward {Z : MatZ D} (hz : F'.zt = F'.fl.z) (hR : IsRowLat D F0 Λ) (hE : F' ∈ EZ T' F0 Λ Z) :
    Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F' := by
  obtain ⟨-, ⟨-, -, hL, hF⟩, hX0⟩ := hR
  obtain ⟨⟨hL', -, -⟩, h1, ⟨ξ, hξ, hgen⟩, ⟨hF', hX1⟩, -⟩ := hE
  rw [← blat_eq hX0 hX1 hz]
  apply Formalism.L2.SG.Pf.eq_of_locP
  intro P
  have := P.isPrime
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · rw [(hgen P).1 hg, Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg ξ hξ,
      ← Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg 1 h1, mplus1_loc hX0 P.asIdeal hg]
  · rw [(hgen P).2 hg, UU_eq hX0 hX1 hz, ← loc_BB_ng D F0 F' P.asIdeal hg]

theorem backward (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) {Z : MatZ D} (hz : F'.zt = F'.fl.z)
    (hZ : ZhatL (lf D F0) F' = Z) (hG : GZ T T' (Zhat F0 F'.fl) ≠ 0)
    (hlat : Submodule.IsLattice D.host.E Λ) (huni : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    IsRowLat D F0 Λ ∧ F' ∈ EZ T' F0 Λ Z := by
  have hw := indep D F0 F'.fl hG
  have hX0 := xlam0 hw hB
  have hX1 := xlam1 hw hB
  have hzΛ : F0.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z_mem_MMg D F0 F'))
  have hz'Λ : F'.fl.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z'_mem_MMg D F0 F'))
  have hFC0 : IsFixedConv Λ (gS D) (lf D F0) := by
    refine ⟨fun P => ?_, prim0 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F0 P
    exact ⟨c, hc0, hc1, by rw [hX0]; exact hc2⟩
  have hFC1 : IsFixedConv Λ (gS D) F' := by
    refine ⟨fun P => ?_, prim1 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F'.fl P
    exact ⟨c, hc0, hc1, by rw [hX1]; exact hc2⟩
  have h1 := isAdmissibleIntegralBasisChange_one hB
  refine ⟨⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus hU D.sp.cm (VS D) Λ hlat huni,
    ⟨hlat, huni, ⟨hzΛ, rfl⟩, hFC0⟩, hX0⟩, ⟨⟨hz'Λ, hz⟩, ⟨1, h1⟩, hG⟩, h1, ⟨1, h1, fun P => ?_⟩,
    ⟨hFC1, hX1⟩, hZ⟩
  have := P.isPrime
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [blat_eq hX0 hX1 hz, hB, mplus1_loc hX0 P.asIdeal hg]
  · rw [blat_eq hX0 hX1 hz, hB, UU_eq hX0 hX1 hz, loc_BB_ng D F0 F' P.asIdeal hg]

end Formalism.L2.SG.Pf.Cnt.R3

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmChar_of (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) : MMChar := by
  intro D u u' _ F0 what₂ _ Z F' hz hZ hP
  have hG : GZ (Tn u) (Tn u') (Zhat F0 F'.fl) ≠ 0 := by
    subst hZ
    exact totPos_ne D hP
  rw [MMof_eq]
  refine ⟨BB_latIn D F0 F', fun Λ => ⟨fun ⟨hR, hE⟩ => ?_, fun ⟨hlat, huni, hB⟩ => ?_⟩⟩
  · exact ⟨hR.2.1.1, hR.2.1.2.1, forward hz hR hE⟩
  · exact backward hU hz hZ hG hlat huni hB

end Formalism.L2.SG.Pf.Cnt
