import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtMatInjective
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinScale

open Formalism.L2.SG.RealObj

theorem ptEntry_row_zero {K : Type*} [Zero K] :
    ∀ (bs : List (K × ℕ)) (a b : ℕ), a < b → b < (bs.map Prod.snd).sum →
      blkOf bs a = blkOf bs b → ∃ c, c < b ∧ ∀ j, j ≤ c → Formalism.MainNotions.S.ptEntry bs c j = 0
  | [], a, b, _, hb, _ => by simp at hb
  | (t, s) :: rest, a, b, hab, hb, hbl => by
    by_cases ha : a < s
    · by_cases hbs : b < s
      · refine ⟨0, by omega, fun j hj => ?_⟩
        have hj0 : j = 0 := by omega
        subst hj0
        have hs : 0 < s := by omega
        simp only [Formalism.MainNotions.S.ptEntry]
        rw [if_pos ⟨hs, hs⟩, if_neg (by omega)]
      · exfalso
        simp [blkOf, ha, hbs] at hbl
    · have hbs : ¬ b < s := by omega
      simp only [blkOf, ha, hbs, if_false] at hbl
      have hbl' : blkOf rest (a - s) = blkOf rest (b - s) := by omega
      have hb' : b - s < (rest.map Prod.snd).sum := by simp at hb; omega
      obtain ⟨c, hc, hz⟩ := ptEntry_row_zero rest (a - s) (b - s) (by omega) hb' hbl'
      refine ⟨c + s, by omega, fun j hj => ?_⟩
      simp only [Formalism.MainNotions.S.ptEntry]
      rw [if_neg (by omega)]
      split_ifs with h
      · have hcs : c + s - s = c := by omega
        rw [hcs]
        exact hz _ (by omega)
      · rfl

theorem isEmpty_freeE_of_reg {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hreg : RegX X u u' γ) (hrep : IsPtRep X u u' w γ) :
    IsEmpty (FreeE w) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨⟨a, b⟩, hab, hbl⟩ := p
  have hab' : a.1 < b.1 := hab
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hb := b.2
  obtain ⟨c, hcb, hz⟩ := ptEntry_row_zero w.1 a.1 b.1 hab' (by rw [hsum]; exact b.2) hbl
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hle : c + 1 ≤ D.R.rS + 1 := by omega
  apply (hreg v).1 (c + 1) (by omega) (by omega)
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos hle]
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨c, by omega⟩
  intro j
  simp only [Matrix.submatrix_apply]
  have hrow := congrFun (congrFun (hrep v) (Fin.castLE hle ⟨c, by omega⟩)) (Fin.castLE hle j)
  simp only [ptC, Formalism.MainNotions.S.ptMat, Matrix.map_apply, Formalism.L2.SG.RealObj.ZhatO, Fin.val_castLE] at hrow
  rw [hz j.1 (by omega), map_zero, map_zero] at hrow
  rcases mul_eq_zero.mp hrow with h | h
  · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · exact h

theorem ptRep_unique {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) {w w' : Point D.host.E (D.R.rS + 1)}
    {γ : X.B.I.Ginf} (h : IsPtRep X u u' w γ) (h' : IsPtRep X u u' w' γ) : w = w' := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have e := (h v).symm.trans (h' v)
  apply GlobalTheory.IntTerm.ptMat_injective
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun e i) j
  simp only [ptC, Matrix.map_apply] at hij
  exact X.ιE.symm.injective ((X.B.I.φ v).injective hij)

theorem one_le_g {D : D7} (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem scale_pin : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), ∃ s : X.B.I.Ginf → NNReal, (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧ (∀ γ, s γ ≤ 1) ∧ ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  intro D X u u'
  have hg : (1 : NNReal) ≤ (X.B.g : NNReal) := by exact_mod_cast one_le_g X
  let sc : X.B.I.Ginf → NNReal := fun γ =>
    if h : ∃ w, IsPtRep X u u' w γ then ((X.B.g : NNReal) ^ (D.R.f * Fintype.card (FreeE h.choose)))⁻¹ else 1
  refine ⟨sc, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    simp only [sc]
    split_ifs with h
    · have := isEmpty_freeE_of_reg X u u' _ γ hγ h.choose_spec
      simp [Fintype.card_eq_zero]
    · rfl
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_pos.mpr (pow_pos (lt_of_lt_of_le one_pos hg) _)
    · exact one_pos
  · intro γ
    simp only [sc]
    split_ifs
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ hg)
    · exact le_rfl
  · rintro w ⟨γ0, hγ0⟩
    have hex0 : ∃ γ, IsPtRep X u u' w γ := ⟨γ0, hγ0⟩
    have hw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW
      rw [dif_pos hex0]
      exact hex0.choose_spec
    have hex : ∃ w', IsPtRep X u u' w' (gamW X u u' w) := ⟨w, hw⟩
    simp only [sc, dif_pos hex]
    rw [ptRep_unique X u u' hex.choose_spec hw]
    push_cast
    rfl

end GlobalTheory.PinScale
