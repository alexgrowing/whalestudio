import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.ExtLatMatrix

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L}

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in

theorem _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP (h : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1)
    {a : ℕ} (M : Submodule (𝓞 K) (Fin a → K)) (x : Fin a → K) (hx : x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) :
    (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M := by
  obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M x).1 hx
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have hs' : s = 0 := by exact_mod_cast h0
    rw [hs']
    exact w.asIdeal.zero_mem
  have hval : w.valuation K ((s : K)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    have h1 : w.valuation K (s : K) = 1 := by
      rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs
    rw [h1, inv_one]
  have hint : σ ((s : K)⁻¹) ∈ v.integer := (h _).2 hval
  have hmem : (fun i => σ ((s • x) i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M :=
    Submodule.subset_span ⟨s • x, hsx, rfl⟩
  have hsm := Submodule.smul_mem _ (⟨σ ((s : K)⁻¹), hint⟩ : v.integer) hmem
  convert hsm using 1
  funext i
  simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
  rw [Algebra.smul_def, map_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in

theorem _root_.GlobalTheory.ExtLatMatrix.extLat_matrix_integral : ∀ (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (σ : K →+* L), (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    (∀ (a : ℕ) (M : Submodule (𝓞 K) (Fin a → K)), ∀ x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M,
      (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) ∧
    ∀ (a b : ℕ) (M : Submodule (𝓞 K) (Fin a → K)) (MW : Submodule (𝓞 K) (Fin b → K))
      (B : GL (Fin a) K) (BW : GL (Fin b) K), _root_.Formalism.L2.DIV.IsBasisAt w M B → _root_.Formalism.L2.DIV.IsBasisAt w MW BW →
      ∀ ap : Matrix (Fin a) (Fin b) L,
        (∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW, ap *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) →
        ∀ i j, v ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap *
          (BW : Matrix (Fin b) (Fin b) K).map σ) i j) ≤ 1 := by
  intro K _ _ w L Γ _ _ v σ h
  refine ⟨fun a M x hx => _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h M x hx, ?_⟩
  intro a b M MW B BW hB hBW ap hap i j
  have hunit : ∀ t : 𝓞 K, t ∉ w.asIdeal → v (σ ((t : K)⁻¹)) ≤ 1 := by
    intro t ht
    refine (h _).2 ?_
    rw [map_inv₀]
    have h1 : w.valuation K (t : K) = 1 := by
      rw [show (t : K) = algebraMap (𝓞 K) K t from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 ht
    rw [h1, inv_one]
  have hint : ∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M, ∀ k,
      v (((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ y) k) ≤ 1 := by
    intro y hy
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      have hm' : m ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.colLat B) := by
        unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
        rw [← hB]
        exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hm
      obtain ⟨t, ht, htm⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal _ m).1 hm'
      unfold _root_.Formalism.L2.DIV.colLat at htm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 htm
      have ht0 : (t : K) ≠ 0 := by
        intro h0
        apply ht
        have ht' : t = 0 := by exact_mod_cast h0
        rw [ht']
        exact w.asIdeal.zero_mem
      have hBc : (B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K)) = (t : K) • m := by
        funext r
        have hr := congrFun hc r
        simp only [Finset.sum_apply, Pi.smul_apply] at hr
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [← Algebra.smul_def] at *
        convert hr using 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [Algebra.smul_def, mul_comm]
          try rfl
      have hBm : ((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m =
          (t : K)⁻¹ • fun k => (c k : K) := by
        have e : m = (t : K)⁻¹ • ((B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K))) := by
          rw [hBc, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
        simp
      intro k
      have e : ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ (fun i => σ (m i))) k =
          σ ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m) k) := by
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e, hBm, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
      refine mul_le_one' (hunit t ht) ((h _).2 ?_)
      exact HeightOneSpectrum.valuation_le_one w (c k)
    | zero => simp
    | add y z _ _ hy hz =>
      intro k
      rw [Matrix.mulVec_add, Pi.add_apply]
      exact v.map_add_le (hy k) (hz k)
    | smul c y _ hy =>
      intro k
      rw [Matrix.mulVec_smul, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      exact mul_le_one' c.2 (hy k)
  have hcol : (fun k => σ ((BW : Matrix (Fin b) (Fin b) K) k j)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW := by
    refine _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h MW _ ?_
    unfold _root_.Formalism.L2.DIV.IsBasisAt at hBW
    rw [hBW]
    exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have key := hint _ (hap _ hcol) i
  convert key using 2
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.ExtLatMatrix
