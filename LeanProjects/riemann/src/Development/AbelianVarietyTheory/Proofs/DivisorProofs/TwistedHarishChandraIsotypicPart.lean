import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartTwistedInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotypicPartExteriorProductInflatedSurjectionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.HcIso

theorem kills_hcTw : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b →
    ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A →
      Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  intro F _ _ t a b n hn α A β B hA hB hαA hβB
  obtain ⟨H, π, hmem, hsurj, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmem x).symm)
  have hE : ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (z : GL (Fin n) F),
      (if InPar a z then α (tlG a z) * β (brG a b z) else 0) =
        ext0 H (fun p => α (π p).1 * β (π p).2) z := by
    intro α β z
    unfold ext0
    by_cases h : InPar a z
    · have hz : z ∈ H := (hmem z).2 h
      rw [if_pos h, dif_pos hz]
      show _ = α (π ⟨z, hz⟩).1 * β (π ⟨z, hz⟩).2
      rw [hπ]
    · have hz : z ∉ H := fun hz => h ((hmem z).1 hz)
      rw [if_neg h, dif_neg hz]
  have h1 : hcTw t a b α β n = fun x => (Nat.card H : ℂ)⁻¹ *
      ∑ᶠ y : GL (Fin n) F, ext0 H (fun p => α (π p).1 * β (π p).2) (y⁻¹ * x * (fun y => gal t n y) y) := by
    funext x
    unfold hcTw
    rw [hcard]
    congr 1
    congr 1
    funext y
    exact hE α β _
  have hid : ∀ y : GL (Fin n) F, gal (RingHom.id F) n y = y := by
    intro y
    ext i j
    simp [gal]
  have h2 : hc a b A B n = ind H (fun p => A (π p).1 * B (π p).2) := by
    funext x
    unfold hc hcTw ind
    rw [hcard]
    congr 1
    congr 1
    funext y
    rw [hid, hE]
  have hk := GlobalTheory.T.isotypicPart_exteriorProduct_inflated_surjection H (GL (Fin a) F) (GL (Fin b) F) π hsurj α A β B hA hB hαA hβB
  rw [h1, h2]
  exact GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction (GL (Fin n) F) H (fun y => gal t n y) _ _ hk

end GlobalTheory.Shin.HcIso
