import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfFpqc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuasiInvPull

open GlobalTheory.CechPic in

theorem lbIso_of_pullback_quasiInverseIsogeny_trivial_axes : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (Q₁ Q₂ : LB (G2 B).left), IsAbelianScheme B → 0 < k →
    IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsAxesTriv B Q₁ → IsAxesTriv B Q₂ →
    LBIso (Q₁.pull (Hecke.sq2 ψ)) (Q₂.pull (Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro Y A B _ _ _ _ k ψ ψ' Q₁ Q₂ hB hk _ hq h₁ h₂ hiso
  obtain ⟨hψ, hψ', -, hc⟩ := hq
  haveI := hψ
  haveI := hψ'
  have o₁ : (1 : B ⟶ B) ≫ (𝟙 B) ^ k = 1 := by
    rw [← hc, ← Category.assoc, GlobalTheory.BirigUniq.one_comp_monHom, GlobalTheory.BirigUniq.one_comp_monHom]
  obtain ⟨hL₁, r₁₁, r₁₂⟩ := h₁
  obtain ⟨hL₂, r₂₁, r₂₂⟩ := h₂
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk
  let d := cls Q₁ hL₁ - cls Q₂ hL₂
  have z₁₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₁
  have z₁₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₂
  have z₂₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₁
  have z₂₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₂
  have d₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left d = 0 := by simp only [d, map_sub, z₁₁, z₂₁, sub_zero]
  have d₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left d = 0 := by simp only [d, map_sub, z₁₂, z₂₂, sub_zero]
  have dψ : pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left d = 0 := by
    have e : pull (Hecke.sq2 ψ) (cls Q₁ hL₁) = pull (Hecke.sq2 ψ) (cls Q₂ hL₂) :=
      (cls_eq_iff (pull_isLB hL₁ _) (pull_isLB hL₂ _)).2 hiso
    simp only [d, map_sub]
    exact sub_eq_zero.2 e

  have dk : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k)).left d = 0 := by
    have : lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) =
        lift (fst B B ≫ ψ') (snd B B ≫ ψ') ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
      rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this, GlobalTheory.BirigUniq.pull_comp_left, dψ, map_zero]

  have hD : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B)).left d = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) = lift (1 : B ⟶ B) (𝟙 B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [o₁]
      rw [this, d₁]
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) =
          lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, dk]

  have hQ : pull (lift (snd B B) (fst B B)).left d = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₂]
    · rw [← GlobalTheory.BirigUniq.pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) =
          lift (snd B B) (fst B B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, GlobalTheory.BirigUniq.pull_comp_left, hD, map_zero]
  have hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hd : d = 0 := by
    have H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d := by
      rw [hsw, Over.id_left, pull_id]
    rw [GlobalTheory.BirigUniq.pull_comp_left, hQ, map_zero] at H
    exact H.symm
  exact (cls_eq_iff hL₁ hL₂).1 (sub_eq_zero.1 hd)

end GlobalTheory.QuasiInvPull
