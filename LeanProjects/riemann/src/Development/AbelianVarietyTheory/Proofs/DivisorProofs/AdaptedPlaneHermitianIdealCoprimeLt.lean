import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsExactIdeal
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.PlaneIdeal

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem count_nonneg_of_forall {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (w : HeightOneSpectrum (𝓞 E))
    (h : ∀ s ∈ I, w.valuation E s ≤ 1) : 0 ≤ FractionalIdeal.count E w I := by
  obtain ⟨y, hy, hy0, he⟩ := PI.UnitaryGroupMassFormula.CntFormula.R6.exists_exact w hI
  rw [← he, ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton E w hy0]
  have h1 := h y hy
  have h0 : w.valuation E y ≠ 0 := (map_ne_zero _).2 hy0
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_smul_mem {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.IsLattice E) (z : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • z ∈ L := by
  have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨d, hd, ha⟩ := ha
    obtain ⟨e, he, hb⟩ := hb
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    exact add_mem (by rw [mul_comm, mul_smul]; exact L.smul_mem e ha) (by rw [mul_smul]; exact L.smul_mem d hb)
  | smul c a _ ha =>
    obtain ⟨d, hd, ha⟩ := ha
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    refine ⟨q * d, mul_ne_zero hq0 hd, ?_⟩
    have hQ : algebraMap (𝓞 E) E q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hq0
    have e : (q * d) • ((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • a) = p • (d • a) := by
      rw [← algebraMap_smul E (q * d), ← algebraMap_smul E p, ← algebraMap_smul E d, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]
    exact L.smul_mem p ha

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (herm : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J b a = σ (form σ J a b) := by
  have herm' : ∀ i j, σ (J i j) = J j i := fun i j => herm j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, herm', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J (c • a) b = c * form σ J a b := by
  simp [form, smul_dotProduct]

theorem form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a a' b : Fin n → E) :
    form σ J (a + a') b = form σ J a b + form σ J a' b := by
  simp [form, add_dotProduct]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J a (c • b) = σ c * form σ J a b := by
  unfold form
  rw [show (fun i => σ ((c • b) i)) = σ c • fun i => σ (b i) from funext fun i => by simp, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

theorem pair_eq {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z z' : Fin n → E) :
    (fun r => (τ.comp σ) (z r)) ⬝ᵥ (Jᵀ).map τ *ᵥ (fun r => τ (z' r)) = τ (form σ J z' z) := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul,
    AlgHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PlaneIdeal

namespace GlobalTheory.PlaneIdeal

open GlobalTheory.AdelicU

theorem plane_ideal_trivial : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁)
    (i₀ i₁ r s : ℕ), B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < i₁ → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ v ∈ B.P, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      FractionalIdeal.count E w H.𝔟 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hA h01 h1n
  have hcm := hB.cm
  have hσ : ∀ x, σ (σ x) = x := cm_conj_conj hcm

  have hb0 : H.𝔟 ≠ 0 := by
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem hY.lat H.x
    intro h
    have hm : algebraMap (𝓞 E) E d ∈ H.𝔟 := (hA.ideal _).2 (by rw [algebraMap_smul]; exact hd)
    rw [h, FractionalIdeal.mem_zero_iff] at hm
    exact hd0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 hm)
  refine ⟨hb0, fun v hv w hw => ?_⟩
  set τ := B.τ ⟨v, hv⟩ with hτ
  have hbas := hY.bas ⟨v, hv⟩
  have hadb := hA.bas ⟨v, hv⟩

  have hcol : ∀ (i : Fin n) (z : Fin n → E), (∀ r, (Y.bas v).1 r i = τ (z r)) → ∀ c : Fv F v,
      (c • (fun r => τ (z r)) ∈ splitLat τ Y.L ↔ c ∈ v.adicCompletionIntegers F) := by
    intro i z hz c
    have e : (Y.bas v).1 *ᵥ Pi.single i c = c • (fun r => τ (z r)) := by
      funext r
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hz, mul_comm]
    change _ ↔ c ∈ v.adicCompletionIntegers F
    rw [← e, ← hbas]
    refine ⟨fun h => by simpa using h i, fun h j => ?_⟩
    rw [Pi.single_apply]
    split_ifs
    · exact h
    · exact zero_mem _
  have hx := hcol ⟨i₀, h01.trans h1n⟩ H.x ((hadb ⟨i₀, h01.trans h1n⟩).1 rfl)
  have hy := hcol ⟨i₁, h1n⟩ H.y ((hadb ⟨i₁, h1n⟩).2.1 rfl)
  have hx1 : (fun r => τ (H.x r)) ∈ splitLat τ Y.L := by simpa using (hx 1).2 (one_mem _)
  have hy1 : (fun r => τ (H.y r)) ∈ splitLat τ Y.L := by simpa using (hy 1).2 (one_mem _)

  have glob : ∀ (ρ : E →ₐ[F] Fv F v) (z : Fin n → E), z ∈ Y.L → (fun r => ρ (z r)) ∈ splitLat ρ Y.L :=
    fun ρ z hz => ⟨_, tmul_mem_latLoc (one_mem _) hz, funext fun r => by simp [splitVec]⟩

  have hJT : IsHermND σ Y.Jᵀ := ⟨fun i j => by simpa using hY.herm j i, by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hY⟩
  have hsd := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n Y r s hB hY v
  have hdual : ∀ z z' : Fin n → E, (fun r => (τ.comp σ) (z r)) ∈ splitLat (τ.comp σ) Y.L →
      (fun r => τ (z' r)) ∈ splitLat τ Y.L → τ (form σ Y.J z' z) ∈ v.adicCompletionIntegers F := by
    intro z z' hz hz'
    rw [← pair_eq τ σ Y.J z z']
    exact (mem_splitLat_comp_iff hcm hJT hsd).1 hz _ hz'
  have toVal : ∀ (ρ : E →ₐ[F] Fv F v) (t : E), ρ t ∈ v.adicCompletionIntegers F →
      (splitPrime ρ).valuation E t ≤ 1 := fun ρ t h => by
    rw [← valued_apply_eq_valuation]; exact h
  have hyx : form σ Y.J H.y H.x = 1 := by rw [form_swap hσ hY.herm, hA.xy, map_one]
  have hxy' : form σ Y.J H.x H.y = 1 := hA.xy

  have b1 : ∀ t ∈ H.𝔟, (splitPrime τ).valuation E t ≤ 1 := fun t ht => by
    have h1 := glob τ _ ((hA.ideal t).1 ht)
    have e : (fun r => τ ((t • H.x) r)) = τ t • (fun r => τ (H.x r)) := funext fun r => by simp
    rw [e, hx] at h1
    exact toVal τ t h1
  have b2 : ∀ t ∈ H.𝔟, (splitPrime (τ.comp σ)).valuation E t ≤ 1 := fun t ht => by
    have h1 := hdual _ _ (glob (τ.comp σ) _ ((hA.ideal t).1 ht)) hy1
    rw [form_smul_right, hyx, mul_one] at h1
    exact toVal (τ.comp σ) t h1

  have hinv : ∀ t ∈ H.𝔟⁻¹, σ t • H.y ∈ Y.L := by
    intro t ht
    rw [hY.dual]
    intro z hz
    obtain ⟨a, b, u, ha, _, _, rfl⟩ := hA.split z hz
    have hab : t * a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [← inv_mul_cancel₀ hb0]
      exact FractionalIdeal.mul_mem_mul ht ((hA.ideal a).2 ha)
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hab
    have e : form σ Y.J (σ t • H.y) (a • H.x + H.ι *ᵥ u + b • H.y) = σ (t * a) := by
      rw [form_smul_left, form_swap hσ hY.herm, form_add_left, form_add_left, form_smul_left, form_smul_left,
        hxy', (hA.orth u).2, hA.yy, map_mul]
      simp
    rw [e, ← ho]
    exact IsIntegral.map (σ : E →+* E).toIntAlgHom o.isIntegral_coe
  have c2 : ∀ t ∈ H.𝔟⁻¹, (splitPrime (τ.comp σ)).valuation E t ≤ 1 := fun t ht => by
    have h1 := glob τ _ (hinv t ht)
    have e : (fun r => τ ((σ t • H.y) r)) = τ (σ t) • (fun r => τ (H.y r)) := funext fun r => by simp
    rw [e, hy] at h1
    exact toVal (τ.comp σ) t h1
  have c1 : ∀ t ∈ H.𝔟⁻¹, (splitPrime τ).valuation E t ≤ 1 := fun t ht => by
    have h1 := hdual _ _ (glob (τ.comp σ) _ (hinv t ht)) hx1
    rw [form_smul_right, hxy', mul_one, hσ] at h1
    exact toVal τ t h1
  have cnt : ∀ w' : HeightOneSpectrum (𝓞 E), (∀ t ∈ H.𝔟, w'.valuation E t ≤ 1) →
      (∀ t ∈ H.𝔟⁻¹, w'.valuation E t ≤ 1) → FractionalIdeal.count E w' H.𝔟 = 0 := by
    intro w' h1 h2
    have e1 := count_nonneg_of_forall hb0 w' h1
    have e2 := count_nonneg_of_forall (inv_ne_zero hb0) w' h2
    rw [FractionalIdeal.count_inv] at e2
    omega
  haveI := v.isMaximal
  have hm : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨hw ▸ rfl⟩⟩
  rw [primesOver_eq_split hcm τ] at hm
  rcases hm with e | e
  · rw [HeightOneSpectrum.ext e]; exact cnt _ b1 c1
  · rw [HeightOneSpectrum.ext e]; exact cnt _ b2 c2

end GlobalTheory.PlaneIdeal
