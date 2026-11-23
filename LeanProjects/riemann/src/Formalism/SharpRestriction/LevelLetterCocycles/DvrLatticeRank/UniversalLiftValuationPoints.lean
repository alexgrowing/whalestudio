import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
import Formalism.SharpRestriction.LevelLetterCocycles.DdRFull
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U1r2Basis

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem universal_lift_basis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
      (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)), ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k) := by
  exact u1r2_basis D HW F Cm hA hl K LL hG π' E hp9 T hT c

theorem universal_lift_valuation (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    (∀ x y, x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) → y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) →
      valAt ((HW l).W K 1 LL hG) T c ζ (x + y) = valAt ((HW l).W K 1 LL hG) T c ζ x + valAt ((HW l).W K 1 LL hG) T c ζ y) ∧
    (∀ (a : ↥(OL LL)) x, x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1) →
      valAt ((HW l).W K 1 LL hG) T c ζ (a • x) = algebraMap ↥(OL LL) ↥LL.1 a • valAt ((HW l).W K 1 LL hG) T c ζ x) := by
  have hP := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ hpt
  exact ⟨fun x y hx hy => (LevelExpansions.V.valL ((Cm l).C K 1 LL hG).tie T hP).map_add ⟨x, hx⟩ ⟨y, hy⟩,
    fun a x hx => (LevelExpansions.V.valL ((Cm l).C K 1 LL hG).tie T hP).map_smul a ⟨x, hx⟩⟩

theorem universal_lift_valuation_points (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ ζ' : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) (hpt' : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ' τ)
    (x : ((HW l).W K 1 LL hG).DD T) (hx : x ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) :
    valAt ((HW l).W K 1 LL hG) T c ζ x = valAt ((HW l).W K 1 LL hG) T c ζ' x := by
  have hP := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ hpt
  have hP' := u1r2_pt D HW F Cm hA K LL hG T hT c τ ζ' hpt'
  have hxN := ((mem_NcS _ T (c - 1) x).1 hx).1
  exact (LevelExpansions.V.valAt_eq ((Cm l).C K 1 LL hG).tie T hP ⟨x, hxN⟩).trans
    (LevelExpansions.V.valAt_eq ((Cm l).C K 1 LL hG).tie T hP' ⟨x, hxN⟩).symm

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
