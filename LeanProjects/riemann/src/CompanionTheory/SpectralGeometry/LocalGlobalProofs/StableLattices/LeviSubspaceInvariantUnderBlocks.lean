import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub

noncomputable section

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

theorem glRel_bops {n : ℕ} (Q : GMod n) {c : ℕ} (d : Fin c → ℕ) (h : ∑ i, d i = n) (i : Fin c) :
    GlRel (bops Q d h i) := by
  intro p q r s
  have inj : ∀ p q : Fin (d i), stdBlocks d h ⟨i, p⟩ = stdBlocks d h ⟨i, q⟩ ↔ p = q := fun p q => by
    simp
  have e := Q.gl (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩) (stdBlocks d h ⟨i, r⟩) (stdBlocks d h ⟨i, s⟩)
  simp only [inj] at e
  exact e

theorem commute_E_Qd {n : ℕ} (P : GMod n) {c : ℕ} (d : Fin c → ℕ) (h : ∑ i, d i = n) (i : Fin c) (Y : ℂ)
    (a b : Fin n) (hab : blk (stdBlocks d h) a = blk (stdBlocks d h) b) :
    Commute (P.E a b) (Qd P d h i Y) := by
  by_cases hi : blk (stdBlocks d h) a = i
  · obtain ⟨⟨i₁, p⟩, rfl⟩ := (stdBlocks d h).surjective a
    obtain ⟨⟨i₂, q⟩, rfl⟩ := (stdBlocks d h).surjective b
    simp only [blk_apply] at hab hi
    subst hi
    subst hab
    exact (qDetCentral _ _ (bops P d h i₁) (glRel_bops P d h i₁) _ p q).symm
  · refine GlobalTheory.CentreFin.commute_qdet (fun p q => ?_) _
    have h1 : b ≠ stdBlocks d h ⟨i, p⟩ := fun e => hi (by rw [hab, e, blk_apply])
    have h2 : stdBlocks d h ⟨i, q⟩ ≠ a := fun e => hi (by rw [← e, blk_apply])
    have e := P.gl a b (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩)
    rw [if_neg h1, if_neg h2, sub_zero] at e
    exact sub_eq_zero.mp e

theorem leviSub_stable {n : ℕ} (P : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (χ : Fin n → ℂ) (L : Fin n → Fin 3)
    (a b : Fin n) (hab : blk (stdBlocks d h) a = blk (stdBlocks d h) b) :
    ∀ x ∈ leviSub P d h χ L, P.E a b x ∈ leviSub P d h χ L := by
  rintro x ⟨hk, he⟩
  refine ⟨fun c e hce => ?_, fun i Y => ?_⟩
  · rw [comm_apply P c e a b x, hk c e hce, map_zero, zero_add]
    have h1 : (if e = a then P.E c b x else 0) = 0 := by
      split_ifs with h1
      · exact hk c b (by rw [← hab, ← h1]; exact hce)
      · rfl
    have h2 : (if b = c then P.E a e x else 0) = 0 := by
      split_ifs with h2
      · exact hk a e (by rw [hab, h2]; exact hce)
      · rfl
    rw [h1, h2, sub_zero]
  · have e := LinearMap.congr_fun (commute_E_Qd P d h i Y a b hab).eq x
    simp only [Module.End.mul_apply] at e
    rw [← e, he i Y, map_smul]

end GlobalTheory.CompanionTheory.RgTransport
