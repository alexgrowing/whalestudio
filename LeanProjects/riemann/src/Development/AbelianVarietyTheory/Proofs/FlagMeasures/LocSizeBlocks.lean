import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Size

theorem detOn_of_frame {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (g : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) m ℂ) (X : Matrix m m ℂ) (W : Submodule ℂ (Fin n → ℂ)) (hC : Cᴴ * C = 1)
    (hW : ∀ y, y ∈ W ↔ ∃ u, y = C *ᵥ u) (hg : g * C = C * X) : detOn g W = ‖X.det‖ := by
  have hst : ∀ y ∈ W, Matrix.toLin' g y ∈ W := by
    intro y hy
    obtain ⟨u, rfl⟩ := (hW y).1 hy
    exact (hW _).2 ⟨X *ᵥ u, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]⟩
  let f : (m → ℂ) →ₗ[ℂ] W := (Matrix.toLin' C).codRestrict W fun u => (hW _).2 ⟨u, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun y => ?_⟩
    · have h1 : C *ᵥ u = C *ᵥ v := congrArg Subtype.val h
      have h2 := congrArg (fun y => Cᴴ *ᵥ y) h1
      simpa only [Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] using h2
    · obtain ⟨u, hu⟩ := (hW y).1 y.2
      exact ⟨u, Subtype.ext hu.symm⟩
  let e := LinearEquiv.ofBijective f hf
  have he : (Matrix.toLin' g).restrict hst =
      (e : (m → ℂ) →ₗ[ℂ] W) ∘ₗ Matrix.toLin' X ∘ₗ (e.symm : W →ₗ[ℂ] (m → ℂ)) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨u, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    change g *ᵥ (C *ᵥ u) = C *ᵥ (X *ᵥ u)
    rw [Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]
  unfold detOn
  rw [dif_pos hst, he, LinearMap.det_conj, LinearMap.det_toLin']

theorem detOn_blocks {n a : ℕ} {j : Fin a → ℕ} (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : Fin a → Prop) [DecidablePred p] (W : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ i, (B i)ᴴ * B i = 1) (h2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0)
    (hW : ∀ y, y ∈ W ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i, ¬ p i → u i = 0) ∧ y = ∑ i, B i *ᵥ u i)
    (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ)
    (hg : ∀ i, g * B i = B i * x i) :
    detOn g W = ∏ i ∈ Finset.univ.filter p, ‖(x i).det‖ := by
  let C : Matrix (Fin n) (Σ i : {i // p i}, Fin (j i)) ℂ := Matrix.of fun r s => B s.1 r s.2
  have hCv : ∀ u, C *ᵥ u = ∑ i : {i // p i}, B i *ᵥ fun s => u ⟨i, s⟩ := by
    intro u
    funext r
    simp [C, Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [detOn_of_frame g C (Matrix.blockDiagonal' fun i : {i // p i} => x i) W ?_ ?_ ?_]
  · rw [ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', norm_prod,
      Finset.prod_subtype (Finset.univ.filter p) (p := p) (by simp)]
  · ext ⟨i, s⟩ ⟨k, t⟩
    change ((B i)ᴴ * B k) s t = _
    by_cases h : i = k
    · subst h
      rw [h1]
      simp [Matrix.one_apply]
    · rw [h2 i k (fun e => h (Subtype.ext e)), Matrix.one_apply_ne (fun e => h (congrArg Sigma.fst e))]
      rfl
  · intro y
    rw [hW]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun s => u s.1 s.2, ?_⟩
      rw [hCv, ← Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun i => B i *ᵥ u i),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · rw [hu i h, Matrix.mulVec_zero]
    · rintro ⟨u, rfl⟩
      refine ⟨fun i => if h : p i then fun s => u ⟨⟨i, h⟩, s⟩ else 0, fun i h => dif_neg h, ?_⟩
      rw [hCv, ← Finset.sum_subset (Finset.filter_subset p Finset.univ) ?_,
        Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        beta_reduce
        rw [dif_pos i.2]
      · intro i _ hi
        beta_reduce
        rw [dif_neg (by simpa using hi), Matrix.mulVec_zero]
  · ext r ⟨k, t⟩
    change (g * B k) r t = _
    rw [hg, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [C]
    · intro i _ hi
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hi]
    · simp

theorem locSize_blocks : ∀ (n a : ℕ) (j : Fin a → ℕ) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → SpansFlag B W → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ), (∀ i, (x i).det ≠ 0) → (∀ i, g * B i = B i * x i) → ∀ i, locSize j W g i = ‖(x i).det‖ ^ (-(1 : ℝ) / j i) := by
  intro n a j B W h1 h2 hW g x hx hg i
  unfold locSize
  rw [detOn_blocks B _ _ h1 h2 (hW i.succ) g x hg, detOn_blocks B _ _ h1 h2 (hW i.castSucc) g x hg]
  have e : (Finset.univ.filter fun k : Fin a => k.castSucc < i.succ) =
      insert i (Finset.univ.filter fun k : Fin a => k.castSucc < i.castSucc) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  rw [e, Finset.prod_insert (by simp), mul_div_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hx k)

end GlobalTheory.LeviIso.Size
