import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDataLevelFormsTransportFieldMap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_data_level_forms_transport_field_map : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ), B.Ok s →
    GlobalTheory.Mem.R3.DefLatBC.BlockBaseChange φ e B B' ℓ ℓ' Z Z' →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x y : Fin (B.dZ ℓ Z) → K, Formalism.DivisionValues.hform (B'.HZ ℓ' Z') (Matrix.mulVec Gm (fun k => φ (x k))) (Matrix.mulVec Gm (fun k => φ (y k))) = φ (Formalism.DivisionValues.hform (B.HZ ℓ Z) x y) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.defLat_of_blockBC | exact GlobalTheory.Mem.R3.DefLatBC.defLat_of_blockBC | (intros; apply GlobalTheory.Mem.R3.DefLatBC.defLat_of_blockBC <;> assumption)
