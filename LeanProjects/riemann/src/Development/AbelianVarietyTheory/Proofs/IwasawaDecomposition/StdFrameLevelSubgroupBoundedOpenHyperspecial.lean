import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.OpenLev
open Classical
variable {D : D7} {n : ℕ}

theorem cong_entry {N : ℕ} {κ : Formalism.AUTREP.GAf D.host.E n} (hκ : NG.Cong D.host.E n N κ) (i j : Fin n) :
    ∃ w ∈ GlobalTheory.StdFrameExist.SI D, (km D n κ).val i j - (1 : Matrix (Fin n) (Fin n) (EAf D)) i j = (N : EAf D) * w := by
  obtain ⟨w, hw, e⟩ := hκ.2 i j
  refine ⟨w, (GlobalTheory.StdFrameExist.mem_ALint_iff w).1 hw, ?_⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) (EAf D)) i j = (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h2 : (N : EAf D) = (N : ReciprocityTheory.Aut.AL D.host.E) := by
    induction N with
    | zero => simp
    | succ k ih => simp
  rw [h1, h2]
  exact e

set_option maxHeartbeats 2000000 in
theorem redFn_eq_one_of_cong {N : ℕ} {PP : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    {κ : Formalism.AUTREP.GAf D.host.E n} (hκ : NG.Cong D.host.E n N κ) :
    redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
  obtain ⟨y, hy⟩ := ((GlobalTheory.T.stdMaximalCompact_reduction_properties D n).2.1 κ).2 hκ.1
  rw [← hy, redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : ((y.val i j : Herm.intAf D.host.F D.host.E) : EAf D) = (km D n κ).val i j := by
    rw [← hy]
    simp [frGL, intGL, Formalism.UG.bc]
  obtain ⟨w, hw', e⟩ := cong_entry hκ i j
  have h1 : (((1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j : Herm.intAf D.host.F D.host.E) : EAf D) =
      (1 : Matrix (Fin n) (Fin n) (EAf D)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have key : y.val i j - (1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j =
      (N : Herm.intAf D.host.F D.host.E) * ⟨w, hw'⟩ := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [hyij, h1]
    exact e
  have hN' : (N : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hN
    simpa using this
  have k2 := congrArg (resS D.host.F PP) key
  rw [map_sub, map_mul, map_natCast, hN', zero_mul, sub_eq_zero] at k2
  have h3 : resS D.host.F PP ((1 : Matrix (Fin n) (Fin n) (Herm.intAf D.host.F D.host.E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (kP PP)) i j := by
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  simp only [Formalism.UG.bc]
  show resS D.host.F PP (y.val i j) = _
  rw [k2, h3]
  rfl

theorem mem_stdJ_of {Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n} {κ : Formalism.AUTREP.GAf D.host.E n}
    (hU : km D n κ ∈ UA D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E))
    (hS : km D n κ ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (EAf D)))
    (hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) : κ ∈ stdJ Ld := by
  show km D n κ ∈ Formalism.L2.DIV.lev D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld
  refine Kg_le_lev (T := Ld.Pg ∪ Ld.Q) Finset.subset_union_left Finset.subset_union_right ?_
  exact ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hS, hr PP hP⟩⟩

theorem stdX_eq_one_of {Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n} {κ : Formalism.AUTREP.GAf D.host.E n} (h : κ ∈ stdJ Ld)
    (hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1) : stdX Ld ⟨κ, h⟩ = 1 := by
  show levFn (1 : GL (Fin n) (EAf D)) Ld (km D n κ) = 1
  have hT : rTup (1 : GL (Fin n) (EAf D)) Ld (km D n κ) = 1 := by
    funext PP
    show upperLeftBlock Ld.hr (redFn (1 : GL (Fin n) (EAf D)) PP.1 (km D n κ)) = 1
    rw [hr PP.1 (Finset.mem_union_left _ PP.2)]
    exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [hT, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [hr PP (Finset.mem_union_right _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hr PP (Finset.mem_union_left _ hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_nat_mem (T : Finset (Pl D.host.E)) :
    ∃ N : ℕ, 0 < N ∧ ∀ PP ∈ T, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  refine ⟨∏ PP ∈ T, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero fun h0 =>
    PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0), fun PP hP => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem PP.asIdeal)

theorem stdJ_open : ∀ (D : D7) (n : ℕ) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n), stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n ∧
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E n N κ → ∃ h : κ ∈ stdJ Ld, stdX Ld ⟨κ, h⟩ = 1) ∧
    ∀ B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))),
      (∀ PP, PP ∈ Ld.Pg ∨ PP ∈ Ld.Q → ∀ v, NG.OverPl PP v → v ∈ B) → NG.HypOutside (stdJ Ld) (stdX Ld) B := by
  intro D n Ld
  have R := GlobalTheory.T.stdMaximalCompact_reduction_properties D n
  have hle : stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
    (R.2.1 κ).1 (parLev_St (lev_le_parLev (show km D n κ ∈ Formalism.L2.DIV.lev D.sp.cm
      (1 : Matrix (Fin n) (Fin n) D.host.E) 1 Ld from hκ)))
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨N, hN, hmem⟩ := exists_nat_mem (D := D) (Ld.Pg ∪ Ld.Q)
    refine ⟨N, hN, fun κ hκ => ?_⟩
    have hr : ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 :=
      fun PP hP => redFn_eq_one_of_cong (hmem PP hP) hκ
    have h := mem_stdJ_of (R.1 κ) ((R.2.1 κ).2 hκ.1) hr
    exact ⟨h, stdX_eq_one_of h hr⟩
  · intro B hB κ hκ
    have hr : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n →
        ∀ PP ∈ Ld.Pg ∪ Ld.Q, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) = 1 := by
      intro hU PP hP
      have hov : NG.OverPl PP (PP.under (𝓞 (maximalRealSubfield D.host.E))) := by
        simp [NG.OverPl, HeightOneSpectrum.under_asIdeal, Ideal.under_def]
      refine R.2.2.1 κ hU Bᶜ _ PP hκ hov ?_
      exact fun hc => hc <| hB PP (Finset.mem_union.1 hP) _ hov
    exact ⟨⟨fun h => hle h, fun hU => mem_stdJ_of (R.1 κ) ((R.2.1 κ).2 hU) (hr hU)⟩,
      fun h => stdX_eq_one_of h (hr (hle h))⟩

end GlobalTheory.MtIn.OpenLev

end
