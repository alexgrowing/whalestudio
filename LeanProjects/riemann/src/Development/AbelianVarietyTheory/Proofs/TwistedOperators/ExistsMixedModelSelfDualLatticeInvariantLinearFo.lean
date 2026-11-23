import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergInvariantLinearFormIsotropicVacuStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem mem_mixLat_iff {x : Matrix (Fin n') (Fin n) L} : x ∈ mixLat L n' n ↔ ∀ r c,
    (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n / 2 → x r c = 0) ∧ (n' / 2 ≤ r.1 → c.1 < n - n / 2 → x r c ∈ intL L) :=
  Iff.rfl

theorem pairing_mixLat (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x) (hδ : Valued.v δ = 1)
    (hψ0 : ∀ a ∈ intL L, σ a = a → ψ a = 1) {a b : Matrix (Fin n') (Fin n) L} (ha : a ∈ mixLat L n' n)
    (hb : b ∈ mixLat L n' n) : pairing σ δ ψ a b = 1 := by
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => mem_intL.2 ((hv x).trans_le hx)
  rw [mem_mixLat_iff] at ha hb
  have hS : ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := by
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hai := ha i j
    have hbi := hb i.rev j.rev
    simp only [Fin.val_rev] at hbi
    have := i.isLt
    have := j.isLt
    by_cases h1 : n' - n' / 2 ≤ i.1 ∨ n' / 2 ≤ i.1 ∧ j.1 < n / 2
    · rw [hai.1 h1, zero_mul]; exact zero_mem _
    by_cases h2 : n' - n' / 2 ≤ n' - (i.1 + 1) ∨ n' / 2 ≤ n' - (i.1 + 1) ∧ n - (j.1 + 1) < n / 2
    · rw [hbi.1 h2, map_zero, mul_zero]; exact zero_mem _
    exact mul_mem (hai.2 (by omega) (by omega)) (hs _ (hbi.2 (by omega) (by omega)))
  have hi : δ * ∑ i, ∑ j, a i j * σ (b i.rev j.rev) ∈ intL L := mul_mem (mem_intL.2 hδ.le) hS
  exact hψ0 _ (add_mem hi (hs _ hi)) (by rw [map_add, hσ, add_comm])

theorem exists_bad_entry (x : Matrix (Fin n') (Fin n) L)
    (hx : ¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) :
    ∃ r c, x r c ∉ intL L ∧ (n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) := by
  by_contra hc
  refine hx ⟨fun r c => if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c, fun r c =>
    ⟨fun e => by dsimp only; rw [if_pos (by omega)], fun e e' => by dsimp only; rw [if_pos (by omega)]; exact zero_mem _⟩,
    fun r c => ?_⟩
  show x r c - (if n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2 then 0 else x r c) ∈ intL L
  split_ifs with hb
  · rw [sub_zero]
    by_contra hi
    exact hc ⟨r, c, hi, hb⟩
  · rw [sub_self]; exact zero_mem _

variable {M : Type} [AddCommGroup M] [Module ℂ M]
variable {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M} {ω : GU σ n × GU σ n' →* Module.End ℂ M} {s : M}

theorem IsStd.form_eq_zero (h : IsStd ϖ σ q δ ψ ρ ω s) (ℓ' : M →ₗ[ℂ] ℂ)
    (hℓ' : ∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) (x : Matrix (Fin n') (Fin n) L) (r : Fin n') (c : Fin n)
    (hx : x r c ∉ intL L) (hrc : n' - n' / 2 ≤ r.1 ∨ n' / 2 ≤ r.1 ∧ c.1 < n - n / 2) : ℓ' (ρ x s) = 0 := by
  obtain ⟨u, hu, hne⟩ := exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hx
  have := r.isLt
  have := c.isLt
  have hyA : Matrix.single r.rev c.rev u ∈ mixLat L n' n := by
    intro r' c'
    rw [Matrix.single_apply]
    split_ifs with he
    · obtain ⟨rfl, rfl⟩ := he
      simp only [Fin.val_rev]
      exact ⟨fun e => by omega, fun _ _ => hu⟩
    · exact ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  have hyL : Matrix.single r.rev c.rev u ∈ intMat L (Fin n') (Fin n) := by
    intro i j
    rw [Matrix.single_apply]
    split_ifs
    exacts [hu, zero_mem _]
  have e1 := h.isHeis.comm x (Matrix.single r.rev c.rev u) s
  rw [h.fixes _ hyL] at e1
  have e2 := congrArg ℓ' e1
  rw [map_smul, hℓ' _ hyA, smul_eq_mul] at e2
  have e3 : (pairing σ δ ψ x (Matrix.single r.rev c.rev u) - 1) * ℓ' (ρ x s) = 0 := by linear_combination -e2
  rcases mul_eq_zero.1 e3 with h' | h'
  · exact absurd (sub_eq_zero.1 h') hne
  · exact h'

end

theorem exists_mixLat_form : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.T.exists_heisenbergInvariant_linearForm_isotropic_vacuum h.isHeis (intMat L (Fin n') (Fin n)) h.selfDual s h.2.1 h.fixes h.2.2.2
    (mixLat L n' n) fun a ha b hb => pairing_mixLat h.1.unr.1 h.1.unr.2.1 h.1.delta.1 h.1.psi_int ha hb
  have hz : ∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ x,
      (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ' (ρ x s) = 0 := fun ℓ' hℓ' x hx => by
    obtain ⟨r, c, hr, hrc⟩ := exists_bad_entry x hx
    exact h.form_eq_zero ℓ' hℓ' x r c hr hrc
  refine ⟨ℓ, h1, h2, hz ℓ h2, fun ℓ' hℓ' => ?_, fun z => ?_⟩
  · have key : ℓ' = ℓ' s • ℓ := LinearMap.ext_on_range h.2.2.2 fun x => ?_
    · exact fun v => LinearMap.congr_fun key v
    show ℓ' (ρ x s) = (ℓ' s • ℓ) (ρ x s)
    by_cases hx : ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)
    · obtain ⟨a, ha, hxa⟩ := hx
      have e := h.isHeis.comp a (x - a) s
      rw [h.fixes _ hxa, show a + (x - a) = x by abel] at e
      have hg := h.isHeis.ne_zero (half h.v_two • a) (x - a)
      have hx' : ρ x s = (pairing σ δ ψ (half h.v_two • a) (x - a))⁻¹ • ρ a s := by
        rw [e, smul_smul, inv_mul_cancel₀ hg, one_smul]
      rw [LinearMap.smul_apply, hx', map_smul, map_smul, hℓ' a ha, h2 a ha, h1, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        mul_one, mul_comm]
    · rw [LinearMap.smul_apply, hz ℓ' hℓ' x hx, hz ℓ h2 x hx, smul_zero]
  · have := (n' / 2).le_refl
    split_ifs with hzi
    · have hm : embLow n' n z ∈ intMat L (Fin n') (Fin n) := fun r c => by
        unfold embLow
        split_ifs
        exacts [hzi _ _, zero_mem _]
      rw [h.fixes _ hm, h1]
    · obtain ⟨i, j, hij⟩ : ∃ i j, z i j ∉ intL L := by
        by_contra hc
        push_neg at hc
        exact hzi hc
      have he : embLow n' n z (hi n' i) (hi n j) = z i j := by
        simp [embLow, hi]
      refine h.form_eq_zero ℓ h2 _ (hi n' i) (hi n j) (by rwa [he]) (Or.inl ?_)
      simp only [hi]
      omega

end GlobalTheory.SphTheta

end
