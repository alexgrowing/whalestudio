import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentAntidiagonalMemSkewLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.RowLift

theorem Hpk_mulVec_eI (k r : ℕ) (a : Fin r) (y : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ y) (eI k r a) = y (esI k r a) := by
  have ha := a.isLt
  have h : ∀ j, Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
    intro j
    have hj : j = esI k r a ↔ j.val = 2 * r + k - a.val := by
      rw [Fin.ext_iff]; rfl
    simp only [Hpk, eI, hj, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  simp [Matrix.mulVec, dotProduct, h]

theorem Hpk_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r i j = Hpk k r j i := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem herm_bvec_eI (k r : ℕ) (c : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (eI k r c)) v = star (v (esI k r c)) := by
  have h : Hpk k r *ᵥ bvec (eI k r c) = bvec (esI k r c) := by
    funext i
    have h1 : (Hpk k r *ᵥ bvec (eI k r c)) i = Hpk k r i (eI k r c) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    have h2 := Hpk_mulVec_eI k r c (bvec i)
    have h3 : (Hpk k r *ᵥ bvec i) (eI k r c) = Hpk k r (eI k r c) i := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, Hpk_symm, ← h3, h2]
    simp [bvec, Pi.single_apply, eq_comm]
  rw [herm, h]
  simp [bvec, dotProduct, Pi.single_apply]

theorem herm_bvec_esI (k r : ℕ) (c : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (esI k r c)) v = star (v (eI k r c)) := by
  have h : Hpk k r *ᵥ bvec (esI k r c) = bvec (eI k r c) := by
    funext i
    have h1 : (Hpk k r *ᵥ bvec (esI k r c)) i = Hpk k r i (esI k r c) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    have h2 := IntG.Hpk_mulVec_esI k r c (bvec i)
    have h3 : (Hpk k r *ᵥ bvec i) (esI k r c) = Hpk k r (esI k r c) i := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, Hpk_symm, ← h3, h2]
    simp [bvec, Pi.single_apply, eq_comm]
  rw [herm, h]
  simp [bvec, dotProduct, Pi.single_apply]

section Place

variable {E : Type} [Field E]

theorem pair_isom {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x))
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x x' : Fin (2 * r + k + 1) → E) :
    star (B *ᵥ fun i => τ (x' i)) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) = τ (form σ J x x') := by
  have hJg : J.map τ *ᵥ (fun i => τ (x i)) = fun i => τ ((J *ᵥ x) i) := by
    funext i
    exact (RingHom.map_mulVec τ J x i).symm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB, hJg]
  simp only [form, dotProduct, map_sum, map_mul, hτ, Pi.star_apply]

theorem coord_zero {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x))
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x x' : Fin (2 * r + k + 1) → E) (h0 : form σ J x x' = 0) (c : ℝ) (hc : c ≠ 0)
    (j : Fin (2 * r + k + 1)) (hx' : (B *ᵥ fun i => τ (x' i)) = (c : ℂ) • bvec j) :
    (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) j = 0 := by
  have h := pair_isom σ τ hτ J B hB x x'
  rw [h0, map_zero, hx'] at h
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have h1 : star ((c : ℂ) • bvec j) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      (c : ℂ) * (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) j := by
    simp [bvec, dotProduct, Pi.single_apply, apply_ite]
  rw [h1] at h
  exact (mul_eq_zero.1 h).resolve_left hcC

end Place

section Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_add_conj_eq_one (h : IsCMExt F E σ) (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) :
    ∃ θ : 𝓞 E, (θ : E) + σ (θ : E) = 1 := by
  have h1 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [h1, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  let I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  have hI0 : (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    intro hb
    have : Algebra.intTrace (𝓞 F) (𝓞 E) 1 ∈ I := ⟨1, rfl⟩
    rw [hb, Ideal.mem_bot] at this
    have h2 := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) 1
    rw [this, map_zero, map_one, ← map_one (algebraMap F E), Algebra.trace_algebraMap, h.2.2.1] at h2
    norm_num at h2
  have hinv : (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
    intro a ha
    rw [FractionalIdeal.mem_inv_iff hI0] at ha
    have hmem : algebraMap F E a ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
      intro b hb
      rw [FractionalIdeal.mem_one_iff] at hb
      obtain ⟨z, rfl⟩ := hb
      rw [Algebra.traceForm_apply, ← Algebra.smul_def, map_smul, smul_eq_mul,
        ← Algebra.algebraMap_intTrace (A := 𝓞 F)]
      have := ha (algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) z))
        ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, ⟨z, rfl⟩, rfl⟩)
      rw [FractionalIdeal.mem_one_iff] at this
      exact this
    rw [hdual, FractionalIdeal.mem_one_iff] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective F E), ← hz]
      exact z.isIntegral_coe
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨⟨a, hint⟩, rfl⟩
  have hone : (1 : FractionalIdeal (𝓞 F)⁰ F) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 F)⁰ F) = I * (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          (mul_inv_cancel₀ hI0).symm
      _ ≤ I * 1 := mul_le_mul_right hinv _
      _ = I := mul_one _
  have h1I : (1 : F) ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := hone (FractionalIdeal.one_mem_one _)
  rw [FractionalIdeal.mem_coeIdeal] at h1I
  obtain ⟨w, ⟨θ, hθ⟩, hw⟩ := h1I
  refine ⟨θ, ?_⟩
  rw [← GlobalTheory.SelfDualLatticeCompare.trace_field h]
  have h2 := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) θ
  rw [hθ, hw] at h2
  rw [show ((θ : E)) = algebraMap (𝓞 E) E θ from rfl, ← h2, map_one]

end Trace

theorem lift_row : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → Fin (k + 1) → ℂ), l ∈ homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inl a)) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inl a)) → degB r β ≤ degB r (.inr (.inl a)) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD a l hl
  obtain ⟨t₀, ⟨ht₀, htΛ⟩, hlt⟩ := hl
  have hD' := hD
  obtain ⟨hCM, hU, hND, hSD, -, -, -, hMod, hs, hAd⟩ := hD
  have hconj : ∀ (τ : E →+* ℂ) x, τ ((σ : E →+* E) x) = star (τ x) := hCM.2.2.2
  have hσσ : ∀ x, σ (σ x) = x := GlobalTheory.SelfDualLatticeCompare.conj_conj hCM
  let te : E ≃ₐ[ℚ] E := AlgEquiv.ofAlgHom (σ : E →+* E).toRatAlgHom (σ : E →+* E).toRatAlgHom
    (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hte : ∀ x, te x = σ x := fun _ => rfl
  set y : Fin (2 * r + k + 1) → E := -t₀ with hy
  set c : E := form (σ : E →+* E) J y y with hc
  obtain ⟨θ, hθ⟩ := exists_add_conj_eq_one hCM hU

  have hfix : σ c = c := by
    have hJ : ∀ i j, σ (J i j) = J j i := fun i j => hND.1 j i
    simp only [hc, form, dotProduct, Matrix.mulVec, map_sum, map_mul, RingHom.coe_coe, hσσ, hJ]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

  have hyΛ : ∀ x ∈ (dInv E (r - a.val))⁻¹, x • y ∈ Λ := by
    intro x hx
    have := Λ.neg_mem (htΛ x hx)
    rwa [← smul_neg] at this
  have hDm : ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) ^ (r - a.val) = (dInv E (r - a.val))⁻¹ := by
    simp [dInv, inv_pow]
  have hmem : c ∈ dInv E (2 * (r - a.val)) := by
    refine IntG.mem_dInv_two_mul te (fun x => hσσ x) _ c ?_
    intro x hx x' hx'
    rw [hDm] at hx hx'
    have h2 := (hSD.2 _).1 (hyΛ x hx) _ (hyΛ x' hx')
    have h3 : form (σ : E →+* E) J (x • y) (x' • y) = x * te x' * c := by
      have e1 : (fun i => (σ : E →+* E) ((x' • y) i)) = (σ x') • fun i => (σ : E →+* E) (y i) := by
        funext i; simp
      rw [form, e1, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hc, form, hte]
      simp only [smul_eq_mul]
      ring
    rwa [h3] at h2
  set t : E := -((θ : E) * c) with ht
  have htm : t ∈ dInv E (2 * (r - a.val)) := by
    have h1 : θ • c ∈ dInv E (2 * (r - a.val)) := Submodule.smul_mem (dInv E (2 * (r - a.val))).coeToSubmodule θ hmem
    have h2 := Submodule.neg_mem (dInv E (2 * (r - a.val))).coeToSubmodule h1
    have h3 : -(θ • c) = t := by rw [ht, Algebra.smul_def]
    rw [h3] at h2
    exact h2
  have hsum : form (σ : E →+* E) J y y + t + σ t = 0 := by
    rw [← hc, ht, map_neg, map_mul, hfix]
    linear_combination (-c) * hθ
  have horth : ∀ b : Fin r, form (σ : E →+* E) J y (fun i => P i b.castSucc) = 0 ∧
      form (σ : E →+* E) J y (fun i => f i b) = 0 := by
    intro b
    have h1 := ht₀ b
    constructor
    · simp only [hy, form, Matrix.mulVec_neg, dotProduct_neg, neg_eq_zero]
      exact h1.1
    · simp only [hy, form, Matrix.mulVec_neg, dotProduct_neg, neg_eq_zero]
      exact h1.2
  have hγ := GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hD' a y t (fun b _ => (horth b).1) hsum hyΛ htm
  have hent := GlobalTheory.SnMass.VolN.rowE_entries F E σ k r J Λ P f T A s hD' a y t

  have hzS : ∀ (w : InfinitePlace E) (b : Fin r), ((A w).mulVec fun l => w.embedding (y l)) (esI k r b) = 0 := by
    intro w b
    have h1 := coord_zero (σ : E →+* E) w.embedding (hconj _) J (A w) (hMod w) y (fun i => P i b.castSucc)
      (horth b).1 (s b) (hs b).ne' (eI k r b) (by simpa using (hAd w b).1)
    rwa [Hpk_mulVec_eI] at h1
  have hzE : ∀ (w : InfinitePlace E) (b : Fin r), ((A w).mulVec fun l => w.embedding (y l)) (eI k r b) = 0 := by
    intro w b
    have h1 := coord_zero (σ : E →+* E) w.embedding (hconj _) J (A w) (hMod w) y (fun i => f i b)
      (horth b).2 (s b)⁻¹ (inv_ne_zero (hs b).ne') (esI k r b) (by simpa using (hAd w b).2)
    rwa [IntG.Hpk_mulVec_esI] at h1
  have nEE : ∀ b c : Fin r, b ≠ c → eI k r b ≠ eI k r c := by
    intro b c h e
    have h1 := congrArg Fin.val e
    simp only [eI] at h1
    exact h (Fin.ext h1)
  have nES : ∀ b c : Fin r, eI k r b ≠ esI k r c := by
    intro b c e
    have h1 := congrArg Fin.val e
    have := b.isLt
    have := c.isLt
    simp only [eI, esI] at h1
    omega
  have nEW : ∀ (b : Fin r) (j : Fin (k + 1)), eI k r b ≠ wI k r j := by
    intro b j e
    have h1 := congrArg Fin.val e
    have := b.isLt
    simp only [eI, wI] at h1
    omega
  have nWS : ∀ (j : Fin (k + 1)) (b : Fin r), wI k r j ≠ esI k r b := by
    intro j b e
    have h1 := congrArg Fin.val e
    have := b.isLt
    have := j.isLt
    simp only [esI, wI] at h1
    omega
  have nSS : ∀ b c : Fin r, b ≠ c → esI k r b ≠ esI k r c := by
    intro b c h e
    have h1 := congrArg Fin.val e
    have := b.isLt
    have := c.isLt
    simp only [esI] at h1
    exact h (Fin.ext (by omega))
  refine ⟨_, hγ, fun w => ?_, fun β hβ hdeg w => ?_⟩
  · funext j
    change gM A _ w (eI k r a) (wI k r j) = l w j
    have hAy : ((A w).mulVec fun l => w.embedding (y l)) = -((A w).mulVec fun l => w.embedding (t₀ l)) := by
      rw [← Matrix.mulVec_neg]
      congr 1
      funext i
      simp [hy]
    rw [hent w, if_neg (nEW a j), if_neg (nWS j a), if_pos rfl, hlt w j, hAy]
    simp [herm, Matrix.mulVec_neg, star_neg]
  · rcases β with p | b | p | b
    · change gM A _ w (eI k r p.1.1) (eI k r p.1.2) = 0
      have hne : p.1.1 ≠ p.1.2 := p.2.ne
      have h1 : eI k r p.1.2 ≠ esI k r a := nES _ _
      rw [hent w, if_neg (nEE _ _ hne), if_neg h1, herm_bvec_eI, hzS]
      simp
    · have hba : b ≠ a := fun h => hβ (by rw [h])
      show (fun j => gM A _ w (eI k r b) (wI k r j)) = (0 : Fin (k + 1) → ℂ)
      funext j
      rw [hent w, if_neg (nEW b j), if_neg (nWS j a), if_neg (nEE _ _ hba)]
      simp
    · change gM A _ w (eI k r p.1.1) (esI k r p.1.2) = 0
      have hh : herm (Hpk k r) (bvec (esI k r p.1.2)) ((A w).mulVec fun l => w.embedding (y l)) = 0 := by
        rw [herm_bvec_esI, hzE]
        simp
      rw [hent w, if_neg (nES _ _), hh]
      by_cases h2 : p.1.2 = a
      · have h1 : p.1.1 ≠ a := h2 ▸ p.2.ne
        rw [h2, if_pos rfl, if_neg (nEE _ _ h1), hzE]
        simp
      · rw [if_neg (nSS _ _ h2)]
        simp
    · change (gM A _ w (eI k r b) (esI k r b)).im = 0
      have hba : b ≠ a := by
        rintro rfl
        change 2 * r - 2 * b.val ≤ r - b.val at hdeg
        have := b.isLt
        omega
      rw [hent w, if_neg (nES _ _), if_neg (nSS _ _ hba), if_neg (nEE _ _ hba)]
      simp

end GlobalTheory.SnMass.VolN.RowLift
