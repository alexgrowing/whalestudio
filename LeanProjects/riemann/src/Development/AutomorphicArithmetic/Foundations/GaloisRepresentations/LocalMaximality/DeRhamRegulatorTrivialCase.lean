import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationCharStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

private lemma mem_sm_iff {S : Type} [CommRing S] [Algebra ℂ S] {d : ℕ} (R : Subalgebra ℂ S) (f : Fin d → S)
    (T : Set (Fin d)) (m : S) :
    m ∈ sm (Algebra.lmul ℂ S) (Subalgebra.toSubmodule R) (f '' T) ↔
      ∃ c : Fin d → S, (∀ l, c l ∈ R) ∧ (∀ l, l ∉ T → c l = 0) ∧ m = ∑ l, f l * c l := by
  constructor
  · intro hm
    let N : Submodule ℂ S :=
      { carrier := {m | ∃ c : Fin d → S, (∀ l, c l ∈ R) ∧ (∀ l, l ∉ T → c l = 0) ∧ m = ∑ l, f l * c l}
        add_mem' := by
          rintro a b ⟨c, h1, h2, rfl⟩ ⟨c', h1', h2', rfl⟩
          refine ⟨c + c', fun l => R.add_mem (h1 l) (h1' l), fun l hl => by simp [h2 l hl, h2' l hl], ?_⟩
          simp [mul_add, Finset.sum_add_distrib]
        zero_mem' := ⟨0, fun l => R.zero_mem, fun _ _ => rfl, by simp⟩
        smul_mem' := by
          rintro a b ⟨c, h1, h2, rfl⟩
          refine ⟨a • c, fun l => R.smul_mem (h1 l) a, fun l hl => by simp [h2 l hl], ?_⟩
          simp [Finset.smul_sum] }
    have hle : sm (Algebra.lmul ℂ S) (Subalgebra.toSubmodule R) (f '' T) ≤ N := by
      refine iSup₂_le ?_
      rintro _ ⟨l, hl, rfl⟩ _ ⟨r, hr, rfl⟩
      classical
      refine ⟨Pi.single l r, fun l' => ?_, fun l' hl' => ?_, ?_⟩
      · by_cases h : l' = l
        · subst h; simpa using hr
        · simp [Pi.single_eq_of_ne h, R.zero_mem]
      · have : l' ≠ l := fun h => hl' (h ▸ hl)
        simp [Pi.single_eq_of_ne this]
      · simp [Pi.single_apply]
    exact hle hm
  · rintro ⟨c, h1, h2, rfl⟩
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : l ∈ T
    · refine Submodule.mem_iSup_of_mem (f l) (Submodule.mem_iSup_of_mem ⟨l, hl, rfl⟩ ?_)
      exact ⟨c l, h1 l, by simp⟩
    · simp [h2 l hl]

private lemma mem_span_image_iff' {P : Type} [CommRing P] {d : ℕ} (g : Fin d → P) (T : Set (Fin d)) (p : P) :
    p ∈ Ideal.span (g '' T) ↔ ∃ q : Fin d → P, (∀ l, l ∉ T → q l = 0) ∧ p = ∑ l, g l * q l := by
  classical
  constructor
  · intro hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      refine ⟨Pi.single l 1, fun l' hl' => ?_, by simp [Pi.single_apply]⟩
      have : l' ≠ l := fun h => hl' (h ▸ hl)
      simp [Pi.single_eq_of_ne this]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨q, h1, rfl⟩ := ha
      obtain ⟨q', h1', rfl⟩ := hb
      exact ⟨q + q', fun l hl => by simp [h1 l hl, h1' l hl], by simp [mul_add, Finset.sum_add_distrib]⟩
    | smul a b _ hb =>
      obtain ⟨q, h1, rfl⟩ := hb
      refine ⟨fun l => a * q l, fun l hl => by simp [h1 l hl], ?_⟩
      simp only [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
  · rintro ⟨q, h1, rfl⟩
    refine Ideal.sum_mem _ fun l _ => ?_
    by_cases hl : l ∈ T
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨l, hl, rfl⟩)
    · simp [h1 l hl]

private lemma X_mul_mem {A σ : Type} [CommRing A] (s : Set σ) (k : σ) (hk : k ∉ s) (g : MvPolynomial σ A)
    (h : MvPolynomial.X k * g ∈ Ideal.span ((MvPolynomial.X : σ → MvPolynomial σ A) '' s)) :
    g ∈ Ideal.span ((MvPolynomial.X : σ → MvPolynomial σ A) '' s) := by
  classical
  rw [MvPolynomial.mem_ideal_span_X_image] at h ⊢
  intro m hm
  have hm' : Finsupp.single k 1 + m ∈ (MvPolynomial.X k * g).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul']
    simpa [MvPolynomial.mem_support_iff] using hm
  obtain ⟨i, hi, hne⟩ := h _ hm'
  refine ⟨i, hi, ?_⟩
  have : i ≠ k := fun e => hk (e ▸ hi)
  simpa [Finsupp.single_apply, this.symm] using hne

private lemma poly_reg {A : Type} [CommRing A] {d : ℕ} (y : Fin d → A) (k : Fin d) (p : MvPolynomial (Fin d) A)
    (h : (MvPolynomial.X k - MvPolynomial.C (y k)) * p ∈
      Ideal.span ((fun l => (MvPolynomial.X l - MvPolynomial.C (y l) : MvPolynomial (Fin d) A)) '' {l | l < k})) :
    p ∈ Ideal.span ((fun l => (MvPolynomial.X l - MvPolynomial.C (y l) : MvPolynomial (Fin d) A)) '' {l | l < k}) := by
  let σ : MvPolynomial (Fin d) A →ₐ[A] MvPolynomial (Fin d) A :=
    MvPolynomial.aeval fun l => MvPolynomial.X l + MvPolynomial.C (y l)
  let τ : MvPolynomial (Fin d) A →ₐ[A] MvPolynomial (Fin d) A :=
    MvPolynomial.aeval fun l => MvPolynomial.X l - MvPolynomial.C (y l)
  have hσ : ∀ l, σ (MvPolynomial.X l - MvPolynomial.C (y l)) = MvPolynomial.X l := by
    intro l
    simp [σ, MvPolynomial.algebraMap_eq]
  have hτ : ∀ l, τ (MvPolynomial.X l) = MvPolynomial.X l - MvPolynomial.C (y l) := by
    intro l; simp [τ]
  have hτσ : ∀ q, τ (σ q) = q := by
    intro q
    have : τ.comp σ = AlgHom.id A _ := by
      refine MvPolynomial.algHom_ext fun l => ?_
      simp [σ, τ, MvPolynomial.algebraMap_eq]
    exact DFunLike.congr_fun this q
  have himg : ∀ (φ : MvPolynomial (Fin d) A →ₐ[A] MvPolynomial (Fin d) A) (a b : Fin d → MvPolynomial (Fin d) A)
      (_ : ∀ l, φ (a l) = b l) (q) (_ : q ∈ Ideal.span (a '' {l | l < k})), φ q ∈ Ideal.span (b '' {l | l < k}) := by
    intro φ a b hab q hq
    obtain ⟨c, hc, rfl⟩ := (mem_span_image_iff' a _ q).1 hq
    refine (mem_span_image_iff' b _ _).2 ⟨fun l => φ (c l), fun l hl => by simp [hc l hl], ?_⟩
    simp [map_sum, hab]
  have h1 := himg σ _ _ hσ _ h
  rw [map_mul, hσ] at h1
  have h2 := X_mul_mem {l | l < k} k (by simp) _ h1
  have h3 := himg τ _ _ hτ _ h2
  rwa [hτσ] at h3

private lemma reg_abs {S P : Type} [CommRing S] [Algebra ℂ S] [CommRing P] {d : ℕ} (R : Subalgebra ℂ S) (φ : P →+* S)
    (hφ : Function.Injective φ) (hφR : ∀ p, φ p ∈ R) (s : Sˣ) (hs : (s : S) ∈ φ.range) (hs' : ((s⁻¹ : Sˣ) : S) ∈ R)
    (hloc : ∀ m ∈ R, ∃ N : ℕ, (s : S) ^ N * m ∈ φ.range) (g : Fin d → P)
    (hreg : ∀ k p, g k * p ∈ Ideal.span (g '' {l | l < k}) → p ∈ Ideal.span (g '' {l | l < k})) :
    Reg (Algebra.lmul ℂ S) (Subalgebra.toSubmodule R) (fun l => φ (g l)) := by
  intro k m hm hk
  have hup : ∀ (v : S) (N N' : ℕ), N ≤ N' → (s : S) ^ N * v ∈ φ.range → (s : S) ^ N' * v ∈ φ.range := by
    intro v N N' h hv
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add, mul_comm ((s : S) ^ N), mul_assoc]
    exact φ.range.mul_mem (φ.range.pow_mem hs _) hv
  obtain ⟨c, hcR, hc0, hc⟩ := (mem_sm_iff R _ _ _).1 hk
  obtain ⟨N0, hN0⟩ := hloc m hm
  choose Nc hNc using fun l => hloc (c l) (hcR l)
  set N := N0 + ∑ l, Nc l with hN
  obtain ⟨p, hp⟩ := hup m N0 N (by omega) hN0
  choose q hq using fun l => hup (c l) (Nc l) N
    ((Finset.single_le_sum (f := Nc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)).trans (by omega)) (hNc l)
  have hq0 : ∀ l, l ∉ {l | l < k} → q l = 0 := by
    intro l hl
    apply hφ
    rw [hq, hc0 l hl]; simp
  have heq : g k * p = ∑ l, g l * q l := by
    apply hφ
    simp only [map_mul, map_sum, hp, hq]
    have hkm : φ (g k) * m = ∑ l, φ (g l) * c l := by simpa using hc
    calc φ (g k) * ((s : S) ^ N * m) = (s : S) ^ N * (φ (g k) * m) := by ring
      _ = _ := by rw [hkm, Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  have hmem : p ∈ Ideal.span (g '' {l | l < k}) :=
    hreg k p (heq ▸ (mem_span_image_iff' g _ _).2 ⟨q, hq0, rfl⟩)
  obtain ⟨q', hq'0, hq'⟩ := (mem_span_image_iff' g _ _).1 hmem
  refine (mem_sm_iff R _ _ _).2 ⟨fun l => ((s⁻¹ : Sˣ) : S) ^ N * φ (q' l),
    fun l => R.mul_mem (R.pow_mem hs' _) (hφR _), fun l hl => by simp [hq'0 l hl], ?_⟩
  have hsN : ((s⁻¹ : Sˣ) : S) ^ N * (s : S) ^ N = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  calc m = ((s⁻¹ : Sˣ) : S) ^ N * ((s : S) ^ N * m) := by rw [← mul_assoc, hsN, one_mul]
    _ = _ := by
      rw [← hp, hq', map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul]; ring

private lemma exists_phi {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (h : IsPd ℂ (xv x))
    (j : Fin (d + 1)) (J : Finset (Fin (d + 1))) :
    ∃ φ : MvPolynomial (Fin d) (rA ℂ (xv x) J) →+* F ⊗[ℂ] F, Function.Injective φ ∧
      (∀ l, φ (MvPolynomial.X l) = ((x (j.succAbove l) : F) / x j) ⊗ₜ[ℂ] (1 : F)) ∧
      (∀ a, φ (MvPolynomial.C a) = (1 : F) ⊗ₜ[ℂ] (a : F)) ∧
      ∀ (a : rA ℂ (xv x) {j}) (b : rA ℂ (xv x) J), (a : F) ⊗ₜ[ℂ] (b : F) ∈ φ.range := by
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv ℂ F d (xv x) h j
  let Φ : (rA ℂ (xv x) J) ⊗[ℂ] MvPolynomial (Fin d) ℂ ≃ₐ[rA ℂ (xv x) J] MvPolynomial (Fin d) (rA ℂ (xv x) J) :=
    MvPolynomial.algebraTensorAlgEquiv ℂ (rA ℂ (xv x) J)
  let Θ : MvPolynomial (Fin d) ℂ ⊗[ℂ] (rA ℂ (xv x) J) →ₐ[ℂ] F ⊗[ℂ] F :=
    Algebra.TensorProduct.map ((rA ℂ (xv x) {j}).val.comp e.toAlgHom) (rA ℂ (xv x) J).val
  let Ψ : (rA ℂ (xv x) J) ⊗[ℂ] MvPolynomial (Fin d) ℂ →ₐ[ℂ] F ⊗[ℂ] F :=
    Θ.comp (Algebra.TensorProduct.comm ℂ (rA ℂ (xv x) J) (MvPolynomial (Fin d) ℂ)).toAlgHom
  have hΘ : Function.Injective Θ :=
    TensorProduct.map_injective_of_flat_flat ((rA ℂ (xv x) {j}).val.comp e.toAlgHom).toLinearMap
      (rA ℂ (xv x) J).val.toLinearMap
      (Subtype.val_injective.comp e.injective) Subtype.val_injective
  have hΨ : Function.Injective Ψ := hΘ.comp (Algebra.TensorProduct.comm ℂ _ _).injective
  have hΨt : ∀ (b : rA ℂ (xv x) J) (p : MvPolynomial (Fin d) ℂ), Ψ (b ⊗ₜ p) = ((e p : rA ℂ (xv x) {j}) : F) ⊗ₜ[ℂ] (b : F) := by
    intro b p
    simp [Ψ, Θ]
  refine ⟨Ψ.toRingHom.comp Φ.symm.toAlgHom.toRingHom, ?_, ?_, ?_, ?_⟩
  · exact hΨ.comp Φ.symm.injective
  · intro l
    have : Φ.symm (MvPolynomial.X l) = (1 : rA ℂ (xv x) J) ⊗ₜ MvPolynomial.X l :=
      MvPolynomial.algebraTensorAlgEquiv_symm_X _ _ l
    change Ψ (Φ.symm (MvPolynomial.X l)) = _
    rw [this, hΨt, he]
    simp
  · intro a
    have : Φ.symm (MvPolynomial.C a) = a ⊗ₜ (1 : MvPolynomial (Fin d) ℂ) := by
      rw [AlgEquiv.symm_apply_eq]
      simp [Φ, MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
    change Ψ (Φ.symm (MvPolynomial.C a)) = _
    rw [this, hΨt]
    simp
  · intro a b
    refine ⟨Φ (b ⊗ₜ e.symm a), ?_⟩
    change Ψ (Φ.symm (Φ (b ⊗ₜ e.symm a))) = _
    rw [AlgEquiv.symm_apply_apply, hΨt]
    simp

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.deRhamRegulator_trivial_case :
    Reg0 := by
  intro F _ _ d x h I J j hjI hjJ
  obtain ⟨φ, hinj, hX, hC, hr⟩ := exists_phi x h j J
  have hmem : ∀ (a : rA ℂ (xv x) I) (b : rA ℂ (xv x) J), (a : F) ⊗ₜ[ℂ] (b : F) ∈ R0 x I J :=
    fun a b => ⟨a ⊗ₜ b, by simp⟩
  have hgen : ∀ (I' : Finset (Fin (d + 1))) (i a : Fin (d + 1)), i ∈ I' → (x a : F) / x i ∈ rA ℂ (xv x) I' :=
    fun I' i a hi => Algebra.subset_adjoin ⟨i, hi, a, rfl⟩
  set σ : F := ∏ i ∈ I, (x i : F) / x j with hσ
  have hσ0 : σ ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => div_ne_zero (x i).ne_zero (x j).ne_zero
  have hσj : σ ∈ rA ℂ (xv x) {j} := Subalgebra.prod_mem _ fun i _ => hgen _ j i (by simp)
  have hσi : σ⁻¹ ∈ rA ℂ (xv x) I := by
    rw [hσ, ← Finset.prod_inv_distrib]
    refine Subalgebra.prod_mem _ fun i hi => ?_
    rw [inv_div]
    exact hgen _ i j hi
  let s : (F ⊗[ℂ] F)ˣ :=
    ⟨σ ⊗ₜ 1, σ⁻¹ ⊗ₜ 1, by simp [Algebra.TensorProduct.one_def, hσ0], by simp [Algebra.TensorProduct.one_def, hσ0]⟩
  have hφR : ∀ p, φ p ∈ R0 x I J := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [hC]; simpa using hmem 1 a
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p l hp =>
      rw [map_mul, hX]
      refine Subalgebra.mul_mem _ hp ?_
      simpa using hmem ⟨_, hgen I j _ hjI⟩ 1
  have hs : (s : F ⊗[ℂ] F) ∈ φ.range := by simpa [s] using hr ⟨σ, hσj⟩ 1
  have hs' : ((s⁻¹ : (F ⊗[ℂ] F)ˣ) : F ⊗[ℂ] F) ∈ R0 x I J := by
    simpa [s] using hmem ⟨_, hσi⟩ 1
  have hloc : ∀ m ∈ R0 x I J, ∃ N : ℕ, (s : F ⊗[ℂ] F) ^ N * m ∈ φ.range := by
    rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simpa using φ.range.zero_mem⟩
    | tmul a b =>
      obtain ⟨N, hN⟩ := (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart ℂ F d (xv x) h I j hjI a).1 a.2
      refine ⟨N, ?_⟩
      have h1 := hr ⟨_, hN⟩ b
      convert h1 using 1
      simp [s, hσ, Algebra.TensorProduct.tmul_pow, mul_comm]
    | add u v hu hv =>
      obtain ⟨N1, h1⟩ := hu
      obtain ⟨N2, h2⟩ := hv
      refine ⟨N1 + N2, ?_⟩
      have e : (s : F ⊗[ℂ] F) ^ (N1 + N2) * (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val (u + v)) =
          (s : F ⊗[ℂ] F) ^ N2 * ((s : F ⊗[ℂ] F) ^ N1 * Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val u) +
          (s : F ⊗[ℂ] F) ^ N1 * ((s : F ⊗[ℂ] F) ^ N2 * Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val v) := by
        rw [map_add, pow_add]; ring
      change (s : F ⊗[ℂ] F) ^ (N1 + N2) * (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val (u + v)) ∈ φ.range
      rw [e]
      exact φ.range.add_mem (φ.range.mul_mem (φ.range.pow_mem hs _) h1) (φ.range.mul_mem (φ.range.pow_mem hs _) h2)
  let y : Fin d → rA ℂ (xv x) J := fun l => ⟨_, hgen J j (j.succAbove l) hjJ⟩
  have key := reg_abs (R0 x I J) φ hinj hφR s hs hs' hloc
    (fun l => MvPolynomial.X l - MvPolynomial.C (y l)) (fun k p hp => poly_reg y k p hp)
  have hf : f0 x j = fun l => φ (MvPolynomial.X l - MvPolynomial.C (y l)) := by
    funext l
    simp [f0, hX, hC, y]
  rw [hf]
  exact key
