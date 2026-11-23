import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
import Formalism.SharpRestriction.LevelLetterCocycles.DdRFull
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalFiltrationHolds

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem universal_lift_filtration (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (S η m : ℕ) (upτ : Bool) (bτ : ℕ)
    (hj : JumpsInV ((D.loc l).PD K) T.ρ τ (deep upτ bτ S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bτ)
    (hm : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV ((D.loc l).PD K) T.ρ τ a ≤ m) :
    (upτ = true →
      (∀ i : ℤ, i < -((bτ : ℤ) + S) → ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-i) → d = 0) ∧
      r ≤ finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ bτ).comap (Phi ((HW l).W K 1 LL hG) T c ζ rep)) + m) ∧
    (upτ = false →
      finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(bτ : ℤ) + 1)).comap
        (Phi ((HW l).W K 1 LL hG) T c ζ rep)) ≤ m ∧
      ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-((bτ : ℤ) + S))) := by
  exact UniversalFiltration.universal_filtration_holds D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep
    S η m upτ bτ hj hηb hm

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
