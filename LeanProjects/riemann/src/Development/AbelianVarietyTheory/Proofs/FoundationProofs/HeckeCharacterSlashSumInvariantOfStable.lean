import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepRepsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem GlobalTheory.EisM.hsum_inv_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  intro k L L' N ε Δ ι _ β f hk hNL hNL' hΔ hΔγ hβ hf
  have hcoc := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).1
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (hsum k (ch ε) β f) hk).2.2.1 L' (ch ε)]
  intro γ hγ
  have hNγ : (N : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hNL').trans hγ
  have hβmem : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  have hγγ : (γ : M2) * ((γ⁻¹ : SL(2,ℤ)) : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγγ' : ((γ⁻¹ : SL(2,ℤ)) : M2) * (γ : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγinv : (L' : ℤ) ∣ (γ⁻¹ : SL(2,ℤ)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hγ.neg_right
  set β' : ι → M2 := fun i => β i * (γ : M2) with hβ'
  have hβ'rep : LRep L Δ β' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨g, i⟩ -
      have := hβ.mapsTo (Set.mem_univ (g, i))
      simp only [β', ← mul_assoc]
      exact hΔγ _ this γ hγ
    · rintro ⟨g, i⟩ - ⟨g', j⟩ - h
      have h' := congrArg (· * ((γ⁻¹ : SL(2,ℤ)) : M2)) h
      simp only [β', mul_assoc, hγγ, mul_one] at h'
      exact hβ.injOn (Set.mem_univ _) (Set.mem_univ _) h'
    · intro δ hδ
      have h1 := hΔγ δ hδ γ⁻¹ hγinv
      obtain ⟨⟨g, i⟩, -, hgi⟩ := hβ.surjOn h1
      refine ⟨(g, i), Set.mem_univ _, ?_⟩
      simp only at hgi ⊢
      rw [← mul_assoc, hgi, mul_assoc, hγγ', mul_one]
  have hsumeq := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k L N ε Δ ι ι β β' f hk hNL hΔ hβ hβ'rep hf
  have hdetγ : (0 : ℤ) < (γ : M2).det := by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num
  have hch : ∀ i, ch ε (β' i 0 0) = ch ε (β i 0 0) * ch ε (γ 0 0) := by
    intro i
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    simp only [ch, β', Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hz, mul_zero, add_zero, map_mul]
  have hγd : ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hd
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    have h2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod N)) hd
      push_cast at this
      rw [hz, mul_zero, sub_zero] at this
      exact this
    simp only [ch]
    rw [← map_mul, h2, map_one]
  funext τ
  have hlin : slz k (γ : M2) (hsum k (ch ε) β f) τ = ∑ i, ch ε (β i 0 0) * slz k (γ : M2) (slz k (β i) f) τ := by
    simp only [slz, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hlin, hsumeq]
  simp only [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcoc (β i) γ (hΔ _ (hβmem i)).1 hdetγ, hch i]
  calc ch ε (β i 0 0) * slz k (β i * ↑γ) f τ
      = ch ε (β i 0 0) * (ch ε (γ 0 0) * ch ε (γ 1 1)) * slz k (β i * ↑γ) f τ := by rw [hγd, mul_one]
    _ = _ := by simp only [β']; ring
