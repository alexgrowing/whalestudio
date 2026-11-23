import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrder
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core

section Lemmas

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]

theorem isFiltration_kerFil (a : S → w.valuationSubring) (N : ℕ)
    (g : S → (Fin N → C) →ₗ[C] W) : IsFiltration a (kerFil a N g) where
  le := fun _ hx => hx.1
  stable := by
    rintro x ⟨hx, h0⟩
    refine ⟨fun i => ?_, fun s => ?_⟩
    · obtain ⟨f, hf⟩ := hx i
      exact ⟨Polynomial.X * f, fun s => by simp [unif, hf s]⟩
    · show g s ((a s : C) • x s) = 0
      rw [map_smul, h0 s, smul_zero]
  saturated := by
    rintro x hx c hc ⟨-, h0⟩
    refine ⟨hx, fun s => ?_⟩
    have hc' : (c : C) ≠ 0 := fun e => hc (Subtype.ext e)
    have h1 := h0 s
    rw [show (c • x) s = (c : C) • x s from rfl, map_smul] at h1
    exact (smul_eq_zero.1 h1).resolve_left hc'

theorem exists_clear_denom {N : ℕ} (y : Fin N → C) :
    ∃ c : w.valuationSubring, c ≠ 0 ∧ ∀ i, (c : C) * y i ∈ w.valuationSubring := by
  have h1 : ∀ i, ∃ c : w.valuationSubring, c ≠ 0 ∧ (c : C) * y i ∈ w.valuationSubring := by
    intro i
    rcases w.valuationSubring.mem_or_inv_mem (y i) with h | h
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · by_cases h0 : y i = 0
      · exact ⟨1, one_ne_zero, by simp [h0, zero_mem]⟩
      · refine ⟨⟨_, h⟩, fun e => h0 ?_, ?_⟩
        · simpa using congrArg (Subtype.val) e
        · simp [h0, one_mem]
  choose c hc hcy using h1
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]
  push_cast
  rw [mul_comm (c i : C), mul_assoc]
  refine mul_mem ?_ (hcy i)
  exact_mod_cast (∏ j ∈ Finset.univ.erase i, c j).2

theorem filSpace_kerFil [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (N : ℕ) (g : S → (Fin N → C) →ₗ[C] W) (s : S) :
    filSpace (kerFil a N g) s = LinearMap.ker (g s) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hf.2 s
  · intro y hy
    obtain ⟨c, hc, hcy⟩ := exists_clear_denom (w := w) y
    let Q : Polynomial w.valuationSubring :=
      ∏ t ∈ Finset.univ.erase s, (Polynomial.X - Polynomial.C (a t))
    have hQ0 : ∀ t, t ≠ s → Q.eval (a t) = 0 := by
      intro t ht
      simp only [Q, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨ht, Finset.mem_univ t⟩) (by simp)
    have hQ : Q.eval (a s) ≠ 0 := by
      simp only [Q, Polynomial.eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.2 fun e => (Finset.mem_erase.1 ht).1 (ha e).symm
    have hQ' : ((Q.eval (a s) : w.valuationSubring) : C) ≠ 0 := fun e => hQ (Subtype.ext e)
    have hc' : (c : C) ≠ 0 := fun e => hc (Subtype.ext e)
    let d : C := ((Q.eval (a s) : w.valuationSubring) : C) * c
    have hd : d ≠ 0 := mul_ne_zero hQ' hc'
    have hmem : d • y ∈ filSpace (kerFil a N g) s := by
      refine Submodule.subset_span (Submodule.mem_map.2 ⟨Pi.single s (d • y), ⟨fun i => ?_, fun t => ?_⟩, by simp⟩)
      · refine ⟨Polynomial.C ⟨_, hcy i⟩ * Q, fun t => ?_⟩
        by_cases ht : t = s
        · subst ht
          simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul,
            Polynomial.eval_C, d]
          push_cast
          ring
        · rw [Pi.single_eq_of_ne ht, Polynomial.eval_mul, hQ0 t ht]
          simp
      · by_cases ht : t = s
        · subst ht
          rw [Pi.single_eq_same, map_smul, LinearMap.mem_ker.1 hy, smul_zero]
        · rw [Pi.single_eq_of_ne ht, map_zero]
    have h2 := Submodule.smul_mem _ d⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2

variable [Fintype S] [DecidableEq S] [Module w.valuationSubring W]
  [IsScalarTower w.valuationSubring C W]

theorem mkQ_mem_eigenSub_iff (a : S → w.valuationSubring) (ha : Function.Injective a) (N : ℕ)
    (g : S → (Fin N → C) →ₗ[C] W) (τ : S) (L : Submodule w.valuationSubring W)
    (hind : ∀ f : S → Fin N → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0)
    (hL : ∀ y, y ∈ L ↔ y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a N, ∑ s, g s (f s) = y)
    (z : Fin N → C) :
    (filSpace (kerFil a N g) τ).mkQ z ∈ eigenSub (lie (freeLattice a N) (kerFil a N g)) τ ↔
      g τ z ∈ L := by
  have hfs : ∀ (s : S) (x : Fin N → C), (filSpace (kerFil a N g) s).mkQ x = 0 ↔ g s x = 0 := by
    intro s x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, filSpace_kerFil a ha N g s,
      LinearMap.mem_ker]
  constructor
  · intro h
    obtain ⟨f, hf, e⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 h)
    have hs : ∀ s, s ≠ τ → g s (f s) = 0 := by
      intro s hs
      have h1 := congrFun e s
      rw [LinearMap.single_apply, Pi.single_eq_of_ne hs] at h1
      exact (hfs s _).1 h1
    have hτ : g τ (f τ) = g τ z := by
      have h1 := congrFun e τ
      rw [LinearMap.single_apply, Pi.single_eq_same] at h1
      have h2 : (filSpace (kerFil a N g) τ).mkQ (f τ - z) = 0 := by
        rw [map_sub, sub_eq_zero]; exact h1
      have h3 := (hfs τ _).1 h2
      rwa [map_sub, sub_eq_zero] at h3
    rw [hL]
    refine ⟨⟨z, rfl⟩, f, hf, ?_⟩
    rw [Finset.sum_eq_single τ (fun s _ h => hs s h) (by simp), hτ]
  · intro h
    obtain ⟨-, f, hf, e⟩ := (hL _).1 h
    have hu : ∀ s, g s (Function.update f τ (f τ - z) s) =
        g s (f s) - if s = τ then g τ z else 0 := by
      intro s
      by_cases hs : s = τ
      · subst hs; simp
      · simp [hs]
    have h0 := hind (Function.update f τ (f τ - z)) (by
      simp only [hu]
      rw [Finset.sum_sub_distrib, e]
      simp)
    refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨f, hf, funext fun s => ?_⟩)
    by_cases hs : s = τ
    · subst hs
      have h1 := h0 s
      rw [hu, if_pos rfl] at h1
      have h2 : (filSpace (kerFil a N g) s).mkQ (f s - z) = 0 := (hfs s _).2 (by rw [map_sub]; exact h1)
      rw [map_sub, sub_eq_zero] at h2
      rw [LinearMap.single_apply, Pi.single_eq_same]
      exact h2
    · have h1 := h0 s
      rw [hu, if_neg hs, sub_zero] at h1
      rw [LinearMap.single_apply, Pi.single_eq_of_ne hs]
      exact (hfs s _).2 h1

theorem isLatticeBasis_mkQ (a : S → w.valuationSubring) (ha : Function.Injective a) (N : ℕ)
    (g : S → (Fin N → C) →ₗ[C] W) (τ : S) {p : ℕ} (v : Fin p → W)
    (hind : ∀ f : S → Fin N → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0)
    (hv : LinearIndependent C v)
    (hL : ∀ y, y ∈ Submodule.span w.valuationSubring (Set.range v) ↔
      y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a N, ∑ s, g s (f s) = y)
    (u : Fin p → Fin N → C) (hu : ∀ i, g τ (u i) = v i) :
    IsLatticeBasis w (fun i => (filSpace (kerFil a N g) τ).mkQ (u i))
      (eigenSub (lie (freeLattice a N) (kerFil a N g)) τ) := by
  have hfs : ∀ x : Fin N → C, (filSpace (kerFil a N g) τ).mkQ x = 0 ↔ g τ x = 0 := by
    intro x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, filSpace_kerFil a ha N g τ,
      LinearMap.mem_ker]
  have hmem := mkQ_mem_eigenSub_iff a ha N g τ _ hind hL
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : g τ (∑ i, c i • u i) = 0 := (hfs _).1 (by
      rw [map_sum]
      simpa only [map_smul] using hc)
    rw [map_sum] at h1
    simp only [map_smul, hu] at h1
    exact Fintype.linearIndependent_iff.1 hv c h1
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (hmem _).2 (by rw [hu]; exact Submodule.subset_span ⟨i, rfl⟩)
    · intro zq hz
      obtain ⟨z, rfl⟩ := (filSpace (kerFil a N g) τ).mkQ_surjective zq
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1
        ((hmem z).1 hz)
      have h0 : (filSpace (kerFil a N g) τ).mkQ (z - ∑ i, (c i : C) • u i) = 0 := (hfs _).2 (by
        rw [map_sub, map_sum, sub_eq_zero, ← hc]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hu]
        exact (algebraMap_smul C (c i) (v i)).symm)
      rw [map_sub, sub_eq_zero, map_sum] at h0
      rw [h0]
      refine sum_mem fun i _ => ?_
      rw [map_smul]
      rw [show (c i : C) • (filSpace (kerFil a N g) τ).mkQ (u i) =
        c i • (filSpace (kerFil a N g) τ).mkQ (u i) from algebraMap_smul C (c i) _]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Lemmas

theorem exists_unit_of_val_eq {C : Type} [Field C] {w : Valuation C ℝ≥0} {x y : C} (hy : y ≠ 0)
    (h : w x = w y) : ∃ ε : (w.valuationSubring)ˣ, x = (ε : w.valuationSubring) * y := by
  have hwy : w y ≠ 0 := (w.ne_zero_iff).2 hy
  have hx : x ≠ 0 := (w.ne_zero_iff).1 (h ▸ hwy)
  have ht : x / y ≠ 0 := div_ne_zero hx hy
  have h1 : w (x / y) = 1 := by rw [map_div₀, h, div_self hwy]
  have h2 : w (x / y)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  refine ⟨⟨⟨x / y, (w.mem_valuationSubring_iff _).2 h1.le⟩,
    ⟨(x / y)⁻¹, (w.mem_valuationSubring_iff _).2 h2.le⟩,
    Subtype.ext (mul_inv_cancel₀ ht), Subtype.ext (inv_mul_cancel₀ ht)⟩, ?_⟩
  show x = x / y * y
  rw [div_mul_cancel₀ _ hy]

theorem det_adapted_core : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (τ : S) (r : S → ℕ) (W : Type) [AddCommGroup W] [Module C W] [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] (g : S → (Fin (p + q) → C) →ₗ[C] W) (v : Fin p → W) (U : Fin (p + q) → Fin (p + q) → C) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), Function.Injective a → (∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0) → (∀ s, Module.finrank C (LinearMap.ker (g s)) = r s) → r τ = q → LinearIndependent C v → (∀ y, y ∈ Submodule.span w.valuationSubring (Set.range v) ↔ y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y) → (∀ i, g τ (U (Fin.castAdd q i)) = v i) → (∀ j, g τ (U (Fin.natAdd p j)) = 0) → IsLatticeBasis w (fun j => U (Fin.natAdd p j)) (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) → IsLatticeBasis w (fun i => ∑ j, A i j • U j) (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) → ∃ ε : (w.valuationSubring)ˣ, A.det * (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q) = (ε : w.valuationSubring) * ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q τ r W _ _ _ _ g v U A ha hind hrank hrq hv hspan hU1 hU2 hM hX
  have hFil := isFiltration_kerFil a (p + q) g
  have hLie := isLatticeBasis_mkQ a ha (p + q) g τ v hind hv hspan
    (fun i => U (Fin.castAdd q i)) hU1
  obtain ⟨c, hc, hdet⟩ := GlobalTheory.FrameModel.det_append_eq_mul_det C w ℓ hℓ0 hℓ1 S a p q
    (kerFil a (p + q) g) τ ha hFil _ _ _ hX hLie hM
  have happ : Fin.append (fun i => U (Fin.castAdd q i)) (fun j => U (Fin.natAdd p j)) = U := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
  have hx : Matrix.of (fun i => ∑ j, A i j • U j) = A * Matrix.of U := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [happ, hx, Matrix.det_mul] at hdet
  have hAU : (A * Matrix.of U).det ≠ 0 := by
    have hu : IsUnit (Matrix.of (fun i => ∑ j, A i j • U j)) :=
      Matrix.linearIndependent_rows_iff_isUnit.1 hX.1
    rw [hx] at hu
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  have hU0 : (Matrix.of U).det ≠ 0 := by
    rw [Matrix.det_mul] at hAU
    exact right_ne_zero_of_mul hAU
  have hcA : c * A.det = 1 := by
    have h1 : (c * A.det) * (Matrix.of U).det = 1 * (Matrix.of U).det := by
      rw [one_mul, mul_assoc]; exact hdet.symm
    exact mul_right_cancel₀ hU0 h1
  have hne : ∀ s ∈ Finset.univ.erase τ, (a τ : C) - (a s : C) ≠ 0 := fun s hs e =>
    (Finset.mem_erase.1 hs).1 (ha (Subtype.ext (sub_eq_zero.1 e))).symm
  have hr : ∀ s, Module.finrank C (filSpace (kerFil a (p + q) g) s) = r s := fun s => by
    rw [filSpace_kerFil a ha (p + q) g s, hrank s]
  have hle : ∀ s, r s ≤ p + q := fun s => by
    rw [← hr s]
    simpa using Submodule.finrank_le (filSpace (kerFil a (p + q) g) s)
  have hval : w (A.det * (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q)) =
      w (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s) := by
    have hwc : w c * w A.det = 1 := by rw [← map_mul, hcA, map_one]
    have hsplit : w ((∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q)) =
        w c * w (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s) := by
      simp only [hr] at hc
      rw [hc, map_pow, map_prod, map_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_pow, ← pow_add, Nat.sub_add_cancel (hle s)]
    rw [map_mul, hsplit, ← mul_assoc, mul_comm (w A.det), hwc, one_mul]
  exact exists_unit_of_val_eq (Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hne s hs)) hval

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core
