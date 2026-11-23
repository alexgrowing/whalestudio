import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimura
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.GamComm

theorem intCast_eq_of_dvd {K M : ℕ} (hK : K ∣ M) {x y : ℤ} (h : (x : ZMod M) = y) : (x : ZMod K) = y := by
  simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h

theorem gamma_le_of_dvd {K M : ℕ} (hK : K ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h1)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h2)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h3)
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h4)

theorem mul_inv_mem_Gam (N l : ℕ) (g δ : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h00 : (en δ 0 0 : ZMod N) = en g 0 0) (h11 : (en δ 1 1 : ZMod N) = en g 1 1) : g * δ⁻¹ ∈ Gam N l := by
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (Subgroup.mem_inf.1 hg).2 (inv_mem (Subgroup.mem_inf.1 hδ).2)⟩
  have a1 : (en g 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hg).1
  have a2 : (en δ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hδ).1
  have hdet : (en δ 0 0 : ZMod N) * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod N) h
    simpa [en] using this
  have e00 : en (g * δ⁻¹) 0 0 = en g 0 0 * en δ 1 1 - en g 0 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e10 : en (g * δ⁻¹) 1 0 = en g 1 0 * en δ 1 1 - en g 1 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e11 : en (g * δ⁻¹) 1 1 = en g 1 1 * en δ 0 0 - en g 1 0 * en δ 0 1 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩
  · change ((en (g * δ⁻¹) 0 0 : ℤ) : ZMod N) = 1
    rw [e00]; push_cast
    linear_combination hdet - (en δ 1 1 : ZMod N) * h00 + ((en δ 0 1 : ZMod N) - en g 0 1) * a2
  · change ((en (g * δ⁻¹) 1 1 : ℤ) : ZMod N) = 1
    rw [e11]; push_cast
    linear_combination hdet - (en δ 0 0 : ZMod N) * h11 + (en δ 0 1 : ZMod N) * a2 - (en δ 0 1 : ZMod N) * a1
  · change ((en (g * δ⁻¹) 1 0 : ℤ) : ZMod N) = 0
    rw [e10]; push_cast
    rw [a1, a2]; ring

theorem act_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ _ ε X N l w _ hN b hb δ hδ s
  funext u
  refine AdicCompletion.ext fun n => ?_
  have hcls := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hF := hcls.2.2.2.2.2.1
  obtain ⟨f, hf⟩ := hcls.1 (AdicCompletion.eval (idl l) (X.Kl l) n
    (b ![(mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))
  obtain ⟨M₀, hM₀, hlev⟩ := X.level (f : X.K)
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨M, hM, hM0, hMN, hMl, hMn⟩ : ∃ M : ℕ, 0 < M ∧ M₀ ∣ M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M :=
    ⟨M₀ * N * l * l ^ n, by positivity, ⟨N * l * l ^ n, by ring⟩, ⟨M₀ * l * l ^ n, by ring⟩,
      ⟨M₀ * N * l ^ n, by ring⟩, ⟨M₀ * N * l, by ring⟩⟩
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hMn s
  obtain ⟨g, h00, h01, h10, h11⟩ := GlobalTheory.exists_sl2_conj_diag_zmod M i hi δ
  have hc : (en δ 0 0 : ZMod M) = en g 0 0 ∧ (en δ 0 1 : ZMod M) = ((i : ℤ) : ZMod M) * en g 0 1 ∧
      ((i : ℤ) : ZMod M) * en δ 1 0 = en g 1 0 ∧ (en δ 1 1 : ZMod M) = en g 1 1 :=
    ⟨h00, by simpa only [Int.cast_natCast] using h01, by simpa only [Int.cast_natCast] using h10, h11⟩
  have hrec := X.recip M f hM (fun γ hγ => hlev γ (gamma_le_of_dvd hM0 hγ)) ζ hζ s i
    (by rw [zpow_natCast, hs]) g δ hc
  have h10' : (((i : ℤ) * en δ 1 0 : ℤ) : ZMod M) = en g 1 0 := by push_cast; exact h10
  have hg0 : ∀ K : ℕ, K ∣ M → δ ∈ CongruenceSubgroup.Gamma0 K → g ∈ CongruenceSubgroup.Gamma0 K := fun K hK h => by
    have a : (en δ 1 0 : ZMod K) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
    refine CongruenceSubgroup.Gamma0_mem.2 ((intCast_eq_of_dvd hK h10').symm.trans ?_)
    rw [Int.cast_mul, a, mul_zero]
  have hgam : g * δ⁻¹ ∈ Gam N l :=
    mul_inv_mem_Gam N l g δ
      (Subgroup.mem_inf.2 ⟨hg0 N hMN (Subgroup.mem_inf.1 hδ).1, hg0 l hMl (Subgroup.mem_inf.1 hδ).2⟩) hδ
      (intCast_eq_of_dvd hMN h00) (intCast_eq_of_dvd hMN h11)
  have hact : X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b := by
    have e : (g : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [e, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos), hb.2 _ hgam]
  have hpol := StabGal.eval_Pol_congr X l w b hb.1 n _ _
    (StabGal.twist_congr l n M hMn δ g i (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) hc
      (by simpa only [Int.cast_natCast] using hχ) u)
  rw [hact]
  have hL := hF (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hF (X.gal s) _ _ hf.symm)
  have hR := hF (X.gal s) _ _ (hF (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hpol.symm.trans hf.symm))
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 1
  apply Units.ext
  change X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ)) (X.gal s f) = X.gal s (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ)) f)
  rw [StabGal.toGQ_SL, StabGal.toGQ_SL, hrec]

end GlobalTheory.KZ.GamComm
