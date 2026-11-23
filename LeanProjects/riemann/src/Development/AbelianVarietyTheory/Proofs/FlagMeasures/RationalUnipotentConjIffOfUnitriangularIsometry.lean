import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagMove

variable {D : D7}

theorem Xsp_eq_Xflag {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Xsp F = Xflag F D.R.rS := by
  unfold Xsp Xflag
  simp only [Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]
  congr 1
  ext v
  simp

private lemma finrank_Xflag {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Fintype.card {i : Fin D.R.rS // i.1 < j} := by
  have h : Xflag F j = Submodule.span D.host.E
      (Set.range (fun i : {i : Fin D.R.rS // i.1 < j} => F.fl.e i.1)) := by
    unfold Xflag
    simp only [Formalism.MainNotions.S.FlagG.Xa]
    congr 1
    ext v
    simp
  rw [h, finrank_span_eq_card]
  exact F.fl.e_indep.comp _ Subtype.val_injective

theorem finrank_Xflag_eq {T T0 : D.host.E} (F : LFlag (VS D) D.R.rS T) (F0 : LFlag (VS D) D.R.rS T0) (j : ℕ) :
    Module.finrank D.host.E (Xflag F j) = Module.finrank D.host.E (Xflag F0 j) := by
  rw [finrank_Xflag, finrank_Xflag]

theorem orth_iff {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {U U' : Submodule D.host.E (VS D).V} (hU : ∀ x, β x ∈ U' ↔ x ∈ U) (y : (VS D).V) :
    β y ∈ orth (VS D) U' ↔ y ∈ orth (VS D) U := by
  have hiso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y := hi
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h x hx
    rw [← hiso]
    exact h (β x) ((hU x).2 hx)
  · intro h x hx
    have hx' : β.symm x ∈ U := (hU _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hx)
    have h' := h _ hx'
    rw [← hiso, LinearEquiv.apply_symm_apply] at h'
    exact h'

private lemma frame_mem_Xflag {T0 : D.host.E} (F0 : LFlag (VS D) D.R.rS T0) (j : ℕ)
    (a : Fin (D.R.rS + 1)) (ha : a.1 < j) (hr : a.1 < D.R.rS) : frame F0 a ∈ Xflag F0 j := by
  have e : a = Fin.castSucc ⟨a.1, hr⟩ := Fin.ext rfl
  rw [e]
  unfold frame Xflag
  simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.MainNotions.S.FlagG.Xa]
  exact Submodule.subset_span ⟨⟨a.1, hr⟩, ha, rfl⟩

theorem map_Xflag_le {T T0 : D.host.E} (F : LFlag (VS D) D.R.rS T) (F0 : LFlag (VS D) D.R.rS T0)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : IsUpUni U) (hf : ∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) (j : ℕ) :
    ∀ x ∈ Xflag F j, σ x ∈ Xflag F0 j := by
  intro x hx
  have key : Submodule.span D.host.E (F.fl.e '' {i | i.1 < j}) ≤
      (Xflag F0 j).comap (σ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i.1 < j := hi
    show σ (F.fl.e i) ∈ Xflag F0 j
    have he : F.fl.e i = frame F (Fin.castSucc i) := by
      unfold frame
      simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [he, hf]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    by_cases hab : Fin.castSucc i < a
    · rw [(hU a (Fin.castSucc i)).1 hab, zero_smul]
      exact Submodule.zero_mem _
    · have h1 : a.1 ≤ i.1 := by
        simpa [Fin.lt_def] using hab
      have h2 := i.2
      exact Submodule.smul_mem _ _ (frame_mem_Xflag F0 j a (by omega) (by omega))
  exact key hx

theorem mem_Xflag_iff {T T0 : D.host.E} (F : LFlag (VS D) D.R.rS T) (F0 : LFlag (VS D) D.R.rS T0)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : IsUpUni U) (hf : ∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) (j : ℕ) (x : (VS D).V) :
    σ x ∈ Xflag F0 j ↔ x ∈ Xflag F j := by
  have hle : (Xflag F j).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag F0 j := by
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    exact map_Xflag_le F F0 σ U hU hf j y hy
  have hfin : FiniteDimensional D.host.E (Xflag F0 j) := by
    show FiniteDimensional D.host.E (Submodule.span D.host.E (F0.fl.e '' {i | i.1 < j}))
    exact FiniteDimensional.span_of_finite D.host.E ((Set.toFinite _).image _)
  have heq : (Xflag F j).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F0 j := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    exact le_of_eq ((finrank_Xflag_eq F0 F j).trans (LinearEquiv.finrank_map_eq σ (Xflag F j)).symm)
  constructor
  · intro h
    rw [← heq, Submodule.mem_map] at h
    obtain ⟨y, hy, hyx⟩ := h
    have hyx' : y = x := σ.injective hyx
    rw [hyx'] at hy
    exact hy
  · exact map_Xflag_le F F0 σ U hU hf j x

theorem nrat_conj_iff : ∀ (D : D7) {T : D.host.E} (F F0 : LFlag (VS D) D.R.rS T)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E),
    σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → IsUpUni U → (∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) →
    ∀ n, n ∈ NRat F ↔ σ * n * σ⁻¹ ∈ NRat F0 := by
  intro D T F F0 σ U hσ hU hf n
  have hX : ∀ j x, σ x ∈ Xflag F0 j ↔ x ∈ Xflag F j := fun j x => mem_Xflag_iff F F0 σ U hU hf j x
  have hS : ∀ x, σ x ∈ Xsp F0 ↔ x ∈ Xsp F := by
    intro x
    rw [Xsp_eq_Xflag, Xsp_eq_Xflag]
    exact hX _ x
  have hO : ∀ x, σ x ∈ orth (VS D) (Xsp F0) ↔ x ∈ orth (VS D) (Xsp F) := orth_iff hσ hS
  have hc : ∀ x, (σ * n * σ⁻¹) (σ x) = σ (n x) := by
    intro x
    show σ (n (σ.symm (σ x))) = σ (n x)
    rw [LinearEquiv.symm_apply_apply]
  have hsub : ∀ x, σ (n x) - σ x = σ (n x - x) := fun x => (map_sub σ _ _).symm
  unfold NRat
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mul_mem (mul_mem hσ h1) (inv_mem hσ), ?_, ?_⟩
    · intro j x hx
      obtain ⟨y, rfl⟩ := σ.surjective x
      rw [hc, hsub, hX]
      exact h2 j y ((hX _ y).1 hx)
    · intro x hx
      obtain ⟨y, rfl⟩ := σ.surjective x
      rw [hc, hsub, hS]
      exact h3 y ((hO y).1 hx)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · have e : n = σ⁻¹ * (σ * n * σ⁻¹) * σ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hσ) h1) hσ
    · intro j x hx
      have h' := h2 j (σ x) ((hX _ x).2 hx)
      rw [hc, hsub, hX] at h'
      exact h'
    · intro x hx
      have h' := h3 (σ x) ((hO x).2 hx)
      rw [hc, hsub, hS] at h'
      exact h'

end GlobalTheory.FlagMove
