import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

noncomputable def atW (w : Pl D.host.E) : AE D →+* Kw w := (cpt w).comp (toEAf D)

theorem atW_apply (w : Pl D.host.E) (a : AE D) : atW w a = cpt w (toEAf D a) := rfl

theorem atW_atPl_self (w : Pl D.host.E) (x : Kw w) : atW w (atPl w x) = x := by
  classical
  rw [atW_apply, (atPl_spec w x).2 w, Pi.single_eq_same]

theorem atW_atPl_ne {w w' : Pl D.host.E} (h : w ≠ w') (x : Kw w') : atW w (atPl w' x) = 0 := by
  classical
  rw [atW_apply, (atPl_spec w' x).2 w, Pi.single_eq_of_ne h]

theorem atPl_one_mul (w : Pl D.host.E) (z : Kw w) : atPl w 1 * atPl w z = atPl w z := by
  classical
  refine ae_ext (by rw [map_mul, (atPl_spec w 1).1, zero_mul, (atPl_spec w z).1]) fun Q => ?_
  rw [map_mul, map_mul, (atPl_spec w 1).2 Q, (atPl_spec w z).2 Q]
  by_cases h : Q = w
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_mul]

namespace CoordinateMaps

variable (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
  (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)

theorem coord_add (y y' : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (y + y') = B.coord t w hX hY y + B.coord t w hX hY y' := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem coord_zero : B.coord t w hX hY 0 = 0 := by
  unfold Frames.coord
  rw [Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem coord_surj (z : Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w)) :
    ∃ y, B.coord t w hX hY y = z := by
  refine ⟨(loc w (B.β X.1 X.2)).val * (zᵀ.submatrix (Fin.cast (rank_vertex G t w hX).symm)
    (Fin.cast (rank_vertex G t w hY).symm)) * ((loc w (B.β Y.1 Y.2))⁻¹).val, ?_⟩
  unfold Frames.coord
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  ext a b
  simp only [transpose_apply, submatrix_apply, Fin.cast_cast, Fin.cast_eq_self]

end CoordinateMaps

end GlobalTheory.BigDat

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem map_atW_smul (w : Pl D.host.E) {m n : Type} (M : Matrix m n (AE D)) :
    (atPl w 1 • M).map (atW w) = M.map (atW w) := by
  refine Matrix.ext fun a b => ?_
  rw [map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, atW_atPl_self, one_mul]

theorem mixCo_eq (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) (u : Pt G i j) :
    mixCo B t e w u = fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mapV e u).map (atW w)))
      (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((mapW e u).map (atW w)))ᵀ := rfl

theorem mixCo_spec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E),
    (∀ u x : Pt G i j, mixCo B t e w (u + x) = mixCo B t e w u + mixCo B t e w x) ∧
    (∀ z, ∃ x ∈ mixHalf e (atPl w 1), mixCo B t e w x = z) ∧
    (∀ u : Pt G i j, mixCo B t e w (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = mixCo B t e w u) ∧
    ∀ w' : Pl D.host.E, w' ≠ w → ∀ x ∈ mixHalf e (atPl w' 1), mixCo B t e w x = 0 := by
  intro D T L sc G B t i j e w
  refine ⟨fun u x => ?_, fun z => ?_, fun u => ?_, fun w' hw x hx => ?_⟩
  · rw [mixCo_eq, mixCo_eq, mixCo_eq, mapV_add, mapW_add, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
      CoordinateMaps.coord_add, CoordinateMaps.coord_add, transpose_add]
    exact Matrix.ext fun a b => by rcases b with b | b <;> rfl
  · obtain ⟨y₁, hy₁⟩ := CoordinateMaps.coord_surj B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      z.toCols₁
    obtain ⟨y₂, hy₂⟩ := CoordinateMaps.coord_surj B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      z.toCols₂ᵀ
    let x₁ : HomV G i j := y₁.map (atPl w)
    let x₂ : HomW G i j := y₂.map (atPl w)
    have k₁ : mapV e (ofMaps e (x₁, x₂)) = x₁ := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (x₁, x₂)) = x₂ := mapW_ofMaps e _
    have m₁ : x₁.map (atW w) = y₁ := Matrix.ext fun a b => atW_atPl_self w _
    have m₂ : x₂.map (atW w) = y₂ := Matrix.ext fun a b => atW_atPl_self w _
    refine ⟨ofMaps e (x₁, x₂), ⟨?_, ?_⟩, ?_⟩
    · show IsHalf _ (mapV e _)
      rw [k₁]
      intro a b
      exact atPl_one_mul w _
    · show IsHalf _ (mapW e _)
      rw [k₂]
      intro a b
      exact atPl_one_mul w _
    · rw [mixCo_eq, k₁, k₂, m₁, m₂, hy₁, hy₂, transpose_transpose, fromCols_toCols]
  · have k₁ : mapV e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapV e u := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapW e u := mapW_ofMaps e _
    rw [mixCo_eq, mixCo_eq, k₁, k₂, map_atW_smul, map_atW_smul]
  · have h₁ : (mapV e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapV e x a b) = atW w (atPl w' 1 * mapV e x a b) := congrArg _ (hx.1 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    have h₂ : (mapW e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapW e x a b) = atW w (atPl w' 1 * mapW e x a b) := congrArg _ (hx.2 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    rw [mixCo_eq, h₁, h₂, CoordinateMaps.coord_zero, CoordinateMaps.coord_zero, transpose_zero, fromCols_zero]

end GlobalTheory.BigDat

end
