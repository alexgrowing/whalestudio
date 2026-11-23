import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RepInd

theorem exists_inj (L : ℕ) (Δ : Set M2) {ι κ : Type} (β : ι → M2) (β' : κ → M2)
    (hβ : LRep L Δ β) (hβ' : LRep L Δ β') :
    ∃ σ : κ → ι, Function.Injective σ ∧ ∃ g : κ → Gamma0 L,
      ∀ j, β' j = (((g j : SL(2, ℤ)) : M2)) * β (σ j) := by
  have hmem : ∀ j, ∃ p : Gamma0 L × ι, ((p.1 : SL(2, ℤ)) : M2) * β p.2 = β' j := by
    intro j
    have h1 : β' j ∈ Δ := by
      have := hβ'.mapsTo (Set.mem_univ ((1 : Gamma0 L), j))
      simpa using this
    obtain ⟨p, -, hp⟩ := hβ.surjOn h1
    exact ⟨p, hp⟩
  choose p hp using hmem
  refine ⟨fun j => (p j).2, ?_, fun j => (p j).1, fun j => (hp j).symm⟩
  intro j j' hjj
  have key : (((((p j).1 * ((p j').1)⁻¹ : Gamma0 L) : SL(2, ℤ)) : M2)) * β' j'
      = (((1 : Gamma0 L) : SL(2, ℤ)) : M2) * β' j := by
    rw [← hp j', ← hp j]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
      Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, one_mul]
    simp only at hjj
    rw [hjj, ← mul_assoc, mul_assoc (((p j).1 : SL(2, ℤ)) : M2)]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mul_one]
  have := hβ'.injOn (Set.mem_univ (((p j).1 * ((p j').1)⁻¹), j')) (Set.mem_univ ((1 : Gamma0 L), j)) key
  exact (congrArg Prod.snd this).symm

end GlobalTheory.EisM.RepInd

namespace GlobalTheory.EisM.RepInd

theorem term_eq (k L N : ℕ) (ε : DirichletCharacter ℂ N) (β : M2) (γ : Gamma0 L) (f : ℍ → ℂ)
    (hk : 1 ≤ k) (hNL : N ∣ L) (hdet : 0 < β.det) (hN : (N : ℤ) ∣ β 1 0) (hf : Inv k L (ch ε) f) (τ : ℍ) :
    ch ε (((((γ : SL(2, ℤ)) : M2)) * β) 0 0) * slz k ((((γ : SL(2, ℤ)) : M2)) * β) f τ
      = ch ε (β 0 0) * slz k β f τ := by
  obtain ⟨hc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k f hk
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  have hgL : (L : ℤ) ∣ g 1 0 := by
    have := (Gamma0_mem).1 γ.2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have hgN : (N : ℤ) ∣ g 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hNL) hgL
  have hgdet : 0 < (g : M2).det := by simp
  rw [hc _ _ hgdet hdet, (hinv L (ch ε)).1 hf g hgL]
  have hlin : slz k β (fun τ => ch ε (g 1 1) * f τ) τ = ch ε (g 1 1) * slz k β f τ := by
    simp only [slz]; ring
  rw [hlin]
  have hdetg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have h00 : ((((g : M2)) * β) 0 0 : ZMod N) = (g 0 0 : ZMod N) * (β 0 0 : ZMod N) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have : ((β 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hN
    push_cast
    rw [this]; simp
  have h1 : (g 0 0 : ZMod N) * (g 1 1 : ZMod N) = 1 := by
    have : ((g 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hgN
    have h2 : ((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℤ) : ZMod N) = 1 := by rw [hdetg]; simp
    push_cast at h2
    rw [this, mul_zero, sub_zero] at h2
    exact h2
  simp only [ch]
  rw [h00, map_mul]
  have : ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N) = 1 := by rw [← map_mul, h1, map_one]
  calc ε (g 0 0 : ZMod N) * ε (β 0 0 : ZMod N) * (ε (g 1 1 : ZMod N) * slz k β f τ)
      = (ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N)) * (ε (β 0 0 : ZMod N) * slz k β f τ) := by ring
    _ = ε (β 0 0 : ZMod N) * slz k β f τ := by rw [this, one_mul]

theorem hsum_indep : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (β' : κ → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → LRep L Δ β' → Inv k L (ch ε) f → hsum k (ch ε) β f = hsum k (ch ε) β' f := by
  intro k L N ε Δ ι κ _ _ β β' f hk hNL hΔ hβ hβ' hf
  obtain ⟨σ, hσ, g, hg⟩ := exists_inj L Δ β β' hβ hβ'
  obtain ⟨σ', hσ', -, -⟩ := exists_inj L Δ β' β hβ' hβ
  have hcard : Fintype.card κ = Fintype.card ι :=
    le_antisymm (Fintype.card_le_of_injective σ hσ) (Fintype.card_le_of_injective σ' hσ')
  have hbij : Function.Bijective σ := (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ, hcard⟩
  have hin : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  funext τ
  simp only [hsum]
  symm
  refine Fintype.sum_bijective σ hbij _ _ ?_
  intro j
  rw [hg j]
  exact term_eq k L N ε (β (σ j)) (g j) f hk hNL (hΔ _ (hin _)).1 (hΔ _ (hin _)).2 hf τ

end GlobalTheory.EisM.RepInd
