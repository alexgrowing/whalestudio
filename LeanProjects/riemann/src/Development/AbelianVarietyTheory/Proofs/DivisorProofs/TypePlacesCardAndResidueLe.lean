import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem typePlaces_card_and_residue_le : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → R.Pg.card = 2 * D.R.f ∧ ∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h
  obtain ⟨_, plg, iso, -⟩ := h
  refine ⟨?_, fun PP hPP => ?_⟩
  · rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr plg, Nat.card_sigma]
    have hk : ∀ k : Fin 2, Nat.card (D.nd.PlG k) = D.R.f := fun k => by
      rw [← D.nd.card_PlG k]
      exact @Nat.card_eq_fintype_card _ (_)
    simp only [hk, Fin.sum_univ_two, two_mul]
  · obtain ⟨kv, hkv⟩ := plg.surjective ⟨PP, hPP⟩
    have h1 : Nat.card (kP (plg kv).1) = D.host.g kv.1 := by
      rw [← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod]
    rw [hkv] at h1
    change _ ≤ Nat.card (kP (⟨PP, hPP⟩ : R.Pg).1)
    rw [h1]
    generalize kv.1 = k
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _

end GlobalTheory
