import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescentStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.Cyc.CrysDeRham

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_Ks_of_good {K LL : FinExt l} {s : ℕ} (h : Good K s LL) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hle : Ks K s ≤ LL.1 := fun x hx => h.2.2.2 (Ks K s).val ⟨x, hx⟩
  have := LL.2
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

theorem apply_mem_Ks (K : FinExt l) (s : ℕ) :
    ∀ g ∈ GK K, ∀ x ∈ Ks K s, g x ∈ Ks K s := by
  intro g hg
  have key : Ks K s ≤ (Ks K s).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le ?_ ?_
    · intro x hx
      have h1 : g x = x := hg ⟨x, hx.1⟩
      change g x ∈ Ks K s
      rw [h1]
      exact (le_sup_left : K0 K ≤ Ks K s) hx
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change g x ∈ Ks K s
      apply (le_sup_right : _ ≤ Ks K s)
      apply IntermediateField.subset_adjoin
      have hx' : x ^ (l ^ s) = 1 := hx
      change (g x) ^ (l ^ s) = 1
      rw [← map_pow, hx', map_one]
  intro x hx
  exact key hx

noncomputable def restrictRep {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  modO := T.modO
  towO := T.towO
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_inclusion (GK_le hle))

theorem isDR_of_restrict (P : LocPrime l) {K E LL : FinExt l} (hle : K.1 ≤ E.1)
    (hs : ∀ g ∈ GK K, ∀ x ∈ E.1, g x ∈ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (h : IsDR (P.PD E) (restrictRep hle T).ρ) : IsDR (P.PD K) T.ρ :=
  GlobalTheory.T.isDeRham_of_restrict_galois_descent l P K E LL (GK_le hle) hle hs T.V T.ρ h

set_option maxHeartbeats 1600000 in

theorem isDR_of_isCrysOn : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → IsDR S.PD T.ρ := by
  intro D HW hF l _ K s LL h S T hT
  let E : FinExt l := ⟨Ks K s, finiteDimensional_Ks_of_good h⟩
  have hle : K.1 ≤ E.1 := h.2.2.1
  have h1 := isCrys_Ks_of_finrank l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h)
    E rfl hle T hT
  have h2 := (hF l E ↥LL.1 ↥(OL LL) (GlobalTheory.LocalIntegers.goodO_integers l LL)
    (restrictRep hle T)).2.2 h1
  exact isDR_of_restrict (D.loc l) hle (apply_mem_Ks K s) T h2

end GlobalTheory.Cyc.CrysDeRham
