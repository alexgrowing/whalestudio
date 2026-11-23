import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameStandardLatticeHermitianIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFamilyUnitriangularChangeOfMemFrameUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingLeadingMinorEqOfUnitriangularChangesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramDetJoinedFamilyEqPmNormDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedSpanOfGramDetIsUnitIntegralLatticeStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocNoDef
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem N_unitary (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : ∀ n ∈ Fr.N, IsUnitary H n := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => intro a b; rfl
  | mul x y _ _ hx hy => intro a b; rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, hy]
  | inv x _ hx =>
    intro a b
    have hxx : ∀ v, x (x⁻¹ v) = v := fun v => by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [← hx (x⁻¹ a) (x⁻¹ b), hxx, hxx]

theorem frame_mem_lamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : Fr.IsInner L) (b : Fin (r + 1)) : Fr.f b ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  induction b using Fin.lastCases with
  | last =>
    have h1 : ∀ a, H.h (Fr.f (Fin.last r)) (Fr.es a) = 0 := fun a => by
      rw [H.h_herm (Fr.es a), Fr.h_sz, map_zero]
    have h2 : ∀ a : Fin r, H.h (Fr.f (Fin.last r)) (Fr.e a) = 0 := fun a =>
      Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne)
    refine ⟨fun a => by rw [h1]; exact M.L.O.zero_mem, fun a => by rw [h2]; exact M.L.O.zero_mem, xz, ?_, hxzL⟩
    simp [FrameD.prF, h1, h2, hxz, FrameD.z]
  | cast a =>
    have h1 : ∀ c, H.h (Fr.f a.castSucc) (Fr.es c) = if a = c then 1 else 0 := fun c => Fr.h_es a c
    have h2 : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.e c) = 0 := fun c =>
      Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
    refine ⟨fun c => ?_, fun c => by rw [h2]; exact M.L.O.zero_mem, 0, ?_, by simp⟩
    · rw [h1]; split_ifs
      · exact M.L.O.one_mem
      · exact M.L.O.zero_mem
    · have h2' : ∀ c : Fin r, H.h (Fr.f a.castSucc) (Fr.f c.castSucc) = 0 := h2
      simp [FrameD.prF, h1, h2', FrameD.e]

theorem noDefect_gen (H : HermSp M V) {r : ℕ} (P : FPair H r) (hR : P.RelG (theta M)) (hP : P.PrimeTo)
    (d : Datum P) (t : Term V M r) (ht : IsTermOver P d t) : ¬ BBne (H := H) t := by
  rintro ⟨v, hvΛ, hvE, hvO⟩
  have hs : M.split = none := hP.1
  have hMM : H.MMfam t = Sum.elim t.f t.f' := by
    unfold HermSp.MMfam; rw [hs]
  rw [hMM] at hvE hvO
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩ := ht
  have hu := N_unitary H P.A n hn
  have hu' := N_unitary H P.B n' hn'

  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    rw [hΛ] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [hu]
    exact GlobalTheory.T.frameStandardLattice_hermitian_integral H P.A d.L d.hL x0 hx0 y0 hy0
  have hmem : ∀ i, Sum.elim t.f t.f' i ∈ t.abelian₂ := by
    rintro (b | b)
    · simp only [Sum.elim_inl, hf]
      rw [hΛ]
      exact Submodule.mem_map_of_mem (f := ((n : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.A d.L d.hL b)
    · simp only [Sum.elim_inr, hf']
      rw [hΛ']
      exact Submodule.mem_map_of_mem (f := ((n' : V →ₗ[E] V).restrictScalars M.L.O))
        (frame_mem_lamStd H P.B d.L' d.hL' b)
  have hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l := by
    intro l
    rw [hf, hf']
    exact GlobalTheory.T.pairingLeadingMinor_eq_of_unitriangular_changes H _ _ _ _ (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.A n hn) (GlobalTheory.T.isFamilyUnitriangularChange_of_mem_frameUnipotent H P.B n' hn') l
  have hG : H.Gdet t.f t.f' t.T t.T' = P.Gv := by
    simp only [HermSp.Gdet, hDl, hT, hT', FPair.Gv]
  have hfr : ∀ (Fr : FrameD H r) (g : V ≃ₗ[E] V), IsUnitary H g → ∀ a b,
      H.h (g (Fr.f a)) (g (Fr.f b)) =
        if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E Fr.T) else 0 := by
    intro Fr g hg a b
    rw [hg]
    split_ifs with hab
    · rw [hab.1, hab.2]; exact Fr.h_zz
    · apply Fr.h_iso
      tauto
  have hdet := GlobalTheory.T.gramDet_joinedFamily_eq_pm_norm_difference H t.f t.f' t.T t.T'
    (by intro a b; rw [hf, hT]; exact hfr P.A n hu a b)
    (by intro a b; rw [hf', hT']; exact hfr P.B n' hu' a b)
    (by rw [hDl]; exact hR.2.1)
  rw [hG] at hdet
  have hU : IsUnitO M (H.gram (Sum.elim t.f t.f')).det := by
    obtain ⟨h1, y, hy, hxy⟩ := hP.2.1
    rcases hdet with h | h
    · rw [h]; exact ⟨h1, y, hy, hxy⟩
    · rw [h]
      refine ⟨M.L.O.neg_mem h1, -y, M.L.O.neg_mem hy, ?_⟩
      rw [neg_mul_neg]; exact hxy
  exact hvO (GlobalTheory.T.saturated_span_of_gramDet_isUnit_integralLattice H t.abelian₂ hint (Sum.elim t.f t.f') hmem hU v hvΛ hvE)

end Gen

theorem noDefect : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t :=
  fun _ _ FP p hR hP d t ht => noDefect_gen _ (FP p) hR hP d t ht

end GlobalTheory.LocNoDef

end
