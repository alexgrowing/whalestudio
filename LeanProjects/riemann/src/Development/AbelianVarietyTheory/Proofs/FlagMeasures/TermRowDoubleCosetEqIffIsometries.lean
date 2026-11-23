import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.KeyIff

variable {D : D7}

theorem one_mem {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : (1 : GV D) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

theorem dcoset_eq_iff {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (γ₁ γ₂ : GV D) :
    ({δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₁ * n'} : Set (GV D)) =
        {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} ↔
      ∃ n ∈ NRat F, ∃ n' ∈ NRat F', γ₂ = n * γ₁ * n' := by
  constructor
  · intro h
    have hm : γ₂ ∈ {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} :=
      ⟨1, one_mem F, 1, one_mem F', by simp⟩
    rw [← h] at hm
    exact hm
  · rintro ⟨n, hn, n', hn', rfl⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F hn),
        n'⁻¹ * b, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F' hn') hb, ?_⟩
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha hn, n' * b,
        Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' hn' hb, by group⟩

theorem key_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  intro D X Y u u' t t'
  have hkey : key t = key t' ↔
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ nmlOf Y u u' t = nmlOf Y u u' t' := Prod.ext_iff
  have hrow : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := by
    show rowOf Y.TR (Y.cs u) (Y.cs u') t = rowOf Y.TR (Y.cs u) (Y.cs u') t' ↔ _
    simp only [rowOf, Prod.mk.injEq, Subtype.mk.injEq]
  have hnml : nmlOf Y u u' t = nmlOf Y u u' t' ↔
      ∃ n ∈ NRat (lf D (X.Fu u)), ∃ n' ∈ NRat (lf D (X.Fu u')), t'.lin = n * t.lin * n' :=
    dcoset_eq_iff _ _ _ _
  rw [hkey, hrow, hnml]
  unfold KeyEq
  constructor
  · rintro ⟨⟨hl, hl', hi⟩, hc⟩
    exact ⟨hl, hl', hc, (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').1 hi⟩
  · rintro ⟨hl, hl', hc, hi⟩
    exact ⟨⟨hl, hl', (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').2 hi⟩, hc⟩

end GlobalTheory.Unfold.KeyIff
