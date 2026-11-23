import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem resΓ_eq_one_of_chi {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) (h1 : P.χQ g = 1) : W.resΓ g = 1 := by
  apply W.χΓ_inj
  rw [map_one W.χΓ]
  apply Units.ext
  apply Subtype.ext
  have h3 := W.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at h3
  exact h3

theorem hinf_fixes_εroot_and_resΓ_eq_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l),
    (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧
    ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K,
      ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  intro l _ P AI K
  have hχ : ∀ g ∈ Hinf K, P.χQ g = 1 := fun g hg =>
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g
      (IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Kinf K from le_sup_left) hg)).2.1 hg
  refine ⟨fun g hg j => ?_, fun s LL hG W g hg => ?_⟩
  · have := GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g 1 (by simp [hχ g hg]) j
    rwa [pow_one] at this
  · have h1 : Ks K s ≤ Kinf K :=
      sup_le_sup_left (IntermediateField.adjoin.mono _ _ _
        fun (x : Om l) (hx : x ^ (l ^ s) = 1) => (⟨s, hx⟩ : ∃ j : ℕ, x ^ (l ^ j) = 1)) _
    have h2 : K.1 ≤ Ks K s := hG.2.2.1
    have hgK : g ∈ GK K := IntermediateField.fixingSubgroup_antitone (h2.trans h1) hg
    exact ⟨hgK, resΓ_eq_one_of_chi P W ⟨g, hgK⟩ (hχ g hg)⟩

end GlobalTheory.Decompl
