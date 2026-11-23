import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroCmElementLocalUnitAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFactorsLocalUnitsAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalModelsUnsplitAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesLeadingMinorEqStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimeAlmostAll

open Formalism.MainNotions.S.LocNG

theorem isUnitO_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} {x y : E} (hx : IsUnitO M x) (hy : IsUnitO M y) : IsUnitO M (x * y) := by
  obtain ⟨hx1, x', hx', hxx⟩ := hx
  obtain ⟨hy1, y', hy', hyy⟩ := hy
  refine ⟨mul_mem hx1 hy1, x' * y', mul_mem hx' hy', ?_⟩
  linear_combination (y * y') * hxx + hyy

theorem isUnitO_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} : IsUnitO M 1 :=
  ⟨one_mem _, 1, one_mem _, mul_one 1⟩

theorem isUnitO_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Formalism.MainNotions.S.Loc.Model F E} {ι : Type} (s : Finset ι) (g : ι → E) (h : ∀ i ∈ s, IsUnitO M (g i)) :
    IsUnitO M (∏ i ∈ s, g i) :=
  Finset.prod_induction g (IsUnitO M) (fun _ _ => isUnitO_mul) isUnitO_one h

theorem isUnitO_cj {D : D7} (Z : LocDat D) (p : PlF D) {x : (D.s.atP p).Ep} (hx : IsUnitO (Z.M p) x) :
    IsUnitO (Z.M p) ((Z.M p).L.cj x) := by
  obtain ⟨hx1, x', hx', hxx⟩ := hx
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z p
  have hc : ∀ y ∈ (Z.M p).L.O, (Z.M p).L.cj y ∈ (Z.M p).L.O := by
    intro y hy
    rw [Z.hcj p, hO] at *
    exact Formalism.L2.SG.Pf.LocFacts.lf_cj_mem p y hy
  refine ⟨hc x hx1, (Z.M p).L.cj x', hc x' hx', ?_⟩
  rw [← map_mul, hxx, map_one]

end GlobalTheory.PrimeAlmostAll

open GlobalTheory.PrimeAlmostAll in

theorem GlobalTheory.PrimeAlmostAll.primeTo_finite : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), Gval F00 F'0 ≠ 0 → ∀ FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS, (∀ p, AtBase Z p F00 F'0 (Tu D u) (Tu D u') (FP p)) → {p : PlF D | ¬ (FP p).PrimeTo}.Finite := by
  intro D Z u u' F00 F'0 hG FP hFP
  let xs : Fin (D.R.rS + 2) → D.host.E := fun l => Formalism.MainNotions.S.Dl F00.fl F'0.fl (l : ℕ)
  have hfin : ({p : PlF D | (Z.M p).split ≠ none} ∪
      (⋃ a : Fin (D.R.rS + 1), {p : PlF D | ¬ LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}) ∪
      {p : PlF D | ¬ LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE (Gval F00 F'0))} ∪
      ⋃ l : Fin (D.R.rS + 2), {p : PlF D | xs l ≠ 0 ∧ ¬ LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE (xs l))}).Finite := by
    refine (((GlobalTheory.T.local_models_unsplit_almost_all D Z).union (Set.finite_iUnion fun a => GlobalTheory.T.frame_factors_local_units_almost_all D Z a)).union (GlobalTheory.T.nonzero_cm_element_local_unit_almost_all D Z _ hG)).union
      (Set.finite_iUnion fun l => ?_)
    by_cases h : xs l = 0
    · simp [h]
    · exact (GlobalTheory.T.nonzero_cm_element_local_unit_almost_all D Z _ h).subset (fun p hp => hp.2)
  refine hfin.subset ?_
  intro p hp
  by_contra hgood
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_not] at hgood
  obtain ⟨⟨⟨hsp, hfr⟩, hGv⟩, hD⟩ := hgood
  apply hp
  have hL4 := GlobalTheory.T.localised_base_frames_leading_minor_eq D Z p F00 F'0 (Tu D u) (Tu D u') (FP p) (hFP p)
  have hκ : ∀ l : ℕ, LocNG.IsUnitO (Z.M p)
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) := by
    intro l
    refine isUnitO_prod _ _ fun a _ => ?_
    split_ifs
    · exact isUnitO_mul (isUnitO_cj Z p (hfr a)) (hfr a)
    · exact isUnitO_one
  refine ⟨hsp, ?_, ?_⟩
  ·
    have hlast : ∀ a : Fin (D.R.rS + 1), ¬ a.val < D.R.rS → (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a = 1 := by
      intro a ha
      have h1 : a.val = D.R.rS := by omega
      have : frFac Z.δ p a = 1 := by
        unfold frFac
        rw [h1, Nat.sub_self, pow_zero, Ring.inverse_one]
      rw [this, map_one, one_mul]
    have hK : (∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS + 1 then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) =
        ∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1 := by
      refine Finset.prod_congr rfl fun a _ => ?_
      have ha : a.val < D.R.rS + 1 := a.2
      by_cases h : a.val < D.R.rS
      · rw [if_pos ha, if_pos h]
      · rw [if_pos ha, if_neg h, hlast a h]
    set K := ∏ a : Fin (D.R.rS + 1), if a.val < D.R.rS then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1 with hKdef
    have eG : (FP p).Gv = (FP p).Dm (D.R.rS + 1) * (Z.M p).L.cj ((FP p).Dm (D.R.rS + 1)) -
        algebraMap _ _ ((FP p).A.T * (FP p).B.T) * ((FP p).Dm D.R.rS * (Z.M p).L.cj ((FP p).Dm D.R.rS)) := rfl
    have hT := (hFP p).2.2
    rw [hT.1, hT.2, hL4 (D.R.rS + 1), hL4 D.R.rS, hK] at eG
    have eGv : (D.s.atP p).ιE (Gval F00 F'0) =
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F00.fl F'0.fl (D.R.rS + 1)) * (D.s.atP p).ιE (star (Formalism.MainNotions.S.Dl F00.fl F'0.fl (D.R.rS + 1))) -
        ((Tu D u : (D.s.atP p).Ep) * (Tu D u' : (D.s.atP p).Ep)) *
        ((D.s.atP p).ιE (Formalism.MainNotions.S.Dl F00.fl F'0.fl D.R.rS) * (D.s.atP p).ιE (star (Formalism.MainNotions.S.Dl F00.fl F'0.fl D.R.rS))) := by
      simp only [Gval, Formalism.MainNotions.S.Gflag, map_sub, map_mul, map_natCast]
    have hTT : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Tu D u : (D.s.atP p).Fp) * (Tu D u' : (D.s.atP p).Fp)) =
        (Tu D u : (D.s.atP p).Ep) * (Tu D u' : (D.s.atP p).Ep) := by
      rw [map_mul, map_natCast, map_natCast]
    rw [hTT, map_mul, map_mul, cj_iota (Z.hcj p), cj_iota (Z.hcj p)] at eG
    have : (FP p).Gv = (K * (Z.M p).L.cj K) * (D.s.atP p).ιE (Gval F00 F'0) := by
      rw [eG, eGv]; ring
    rw [this]
    exact isUnitO_mul (isUnitO_mul (hκ D.R.rS) (isUnitO_cj Z p (hκ D.R.rS))) hGv
  ·
    intro l hl
    simp only [LocNG.FPair.ends, Finset.mem_filter, Finset.mem_range] at hl
    obtain ⟨hlr, -, hu⟩ := hl
    rw [hL4 l] at hu ⊢
    by_cases h0 : xs ⟨l, hlr⟩ = 0
    · exfalso
      have h0' : Formalism.MainNotions.S.Dl F00.fl F'0.fl l = 0 := h0
      rw [h0', map_zero, mul_zero] at hu
      exact not_isUnit_zero hu
    · exact isUnitO_mul (hκ l) (hD ⟨l, hlr⟩ h0)
