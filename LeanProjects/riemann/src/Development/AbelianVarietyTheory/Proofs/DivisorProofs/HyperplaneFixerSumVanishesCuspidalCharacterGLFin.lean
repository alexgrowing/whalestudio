import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow

noncomputable section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.FreeCusp

theorem charpoly_one {F : Type} [Field F] (M : Matrix (Fin 1) (Fin 1) F) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem rootSum_X_sub_C {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (a : F) :
    rootSum θ k (X - C a) = θ (algebraMap F (AlgebraicClosure F) a) ^ k := by
  unfold rootSum
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.roots_X_sub_C]
  simp

theorem cusp_one {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (x : GL (Fin 1) F) :
    cusp θ 1 k x = θ (algebraMap F (AlgebraicClosure F) ((x : Matrix (Fin 1) (Fin 1) F) 0 0)) ^ k := by
  have hs := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  unfold cusp psiG
  rw [psi_eq]
  have hz : ∑ᶠ W : {W : Submodule F (Fin 1 → F) // W ≠ ⊤ ∧ ∀ v ∈ W,
      Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F) v ∈ W},
      psi (rootSum θ k) W.1 ((Matrix.toLin' (x : Matrix (Fin 1) (Fin 1) F)).restrict W.2.2) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    have h1 := Submodule.finrank_lt W.2.1
    rw [Module.finrank_fin_fun] at h1
    haveI : Subsingleton W.1 := (Module.finrank_zero_iff (R := F)).mp (by omega)
    exact PsiPrimitive.psi_trivial _ hs _ _
  rw [hz, sub_zero, Matrix.charpoly_toLin', charpoly_one, rootSum_X_sub_C]
  simp

theorem hfree_one {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (k : ℕ)
    (hk : ¬ k ≡ 0 [MOD Nat.card F - 1]) : HFree (cusp θ 1 k) := by
  intro _
  have hset : {x : GL (Fin 1) F | ∀ i j : Fin 1, (j : ℕ) + 1 < 1 →
      (x : Matrix (Fin 1) (Fin 1) F) i j = (1 : Matrix (Fin 1) (Fin 1) F) i j} = Set.univ :=
    Set.eq_univ_of_forall fun x i j h => absurd h (by omega)
  rw [hset, finsum_mem_univ]
  letI := Fintype.ofFinite (GL (Fin 1) F)
  rw [finsum_eq_sum_of_fintype]
  let f : GL (Fin 1) F →* ℂ := (powMonoidHom k).comp (θ.comp
    ((algebraMap F (AlgebraicClosure F) : F →* AlgebraicClosure F).comp
      ((Units.coeHom F).comp Matrix.GeneralLinearGroup.det)))
  have hf : ∀ x, f x = cusp θ 1 k x := by
    intro x
    rw [cusp_one]
    simp [f, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [← Finset.sum_congr rfl fun x _ => hf x]
  refine sum_hom_units_eq_zero f ?_
  intro h1
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  let x : GL (Fin 1) F := Matrix.GeneralLinearGroup.mk'' (Matrix.of fun _ _ => (u : F))
    (by rw [Matrix.det_fin_one]; exact u.isUnit)
  have hx : f x = 1 := by rw [h1]; rfl
  have hx' : f x = θ (algebraMap F (AlgebraicClosure F) ((u : F) ^ k)) := by
    simp [f, x, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, map_pow]
  rw [hx', ← map_one θ] at hx
  have hne : algebraMap F (AlgebraicClosure F) ((u : F) ^ k) ≠ 0 := by
    rw [_root_.map_ne_zero]; exact pow_ne_zero _ u.ne_zero
  have h2 := hθ _ _ hne one_ne_zero hx
  rw [← map_one (algebraMap F (AlgebraicClosure F))] at h2
  have h3 : (u : F) ^ k = 1 := (algebraMap F (AlgebraicClosure F)).injective h2
  have h4 : u ^ k = 1 := Units.ext (by simpa using h3)
  have h5 := orderOf_dvd_iff_pow_eq_one.mpr h4
  rw [hu, Nat.card_units] at h5
  exact hk (Nat.modEq_zero_iff_dvd.mpr h5)

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin.FreeCusp

variable {F : Type} [Field F]

def hyp {m : ℕ} (l : Fin m) : Submodule F (Fin m → F) := LinearMap.ker (LinearMap.proj l)

theorem mem_hyp {m : ℕ} (l : Fin m) (v : Fin m → F) : v ∈ hyp l ↔ v l = 0 := by
  simp [hyp]

def dg {m : ℕ} (l : Fin m) (d : F) : Matrix (Fin m) (Fin m) F := Matrix.diagonal fun i => if i = l then d else 1

theorem dg_off {m : ℕ} (l : Fin m) (d : F) (i j : Fin m) (hj : j ≠ l) :
    dg l d i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
  by_cases h : i = j
  · subst h; simp [dg, hj]
  · simp [dg, Matrix.one_apply, h]

theorem mem_nilRad_of {m : ℕ} (l : Fin m) (M : Matrix (Fin m) (Fin m) F)
    (h1 : ∀ i j, j ≠ l → M i j = 0) (h2 : M l l = 0) : Matrix.toLin' M ∈ nilRad (hyp l) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [mem_hyp, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = l
    · subst hj; rw [h2, zero_mul]
    · rw [h1 l j hj, zero_mul]
  · rw [mem_hyp] at hv
    funext i
    rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = l
    · subst hj; rw [hv, mul_zero]
    · rw [h1 i j hj, zero_mul]

theorem of_mem_nilRad {m : ℕ} (l : Fin m) (h : Module.End F (Fin m → F)) (hh : h ∈ nilRad (hyp l)) :
    (∀ i j, j ≠ l → LinearMap.toMatrix' h i j = 0) ∧ LinearMap.toMatrix' h l l = 0 := by
  refine ⟨fun i j hj => ?_, ?_⟩
  · rw [LinearMap.toMatrix'_apply, hh.2 _ ((mem_hyp l _).2 (Pi.single_eq_of_ne (Ne.symm hj) _))]
    rfl
  · rw [LinearMap.toMatrix'_apply]
    exact (mem_hyp l _).1 (hh.1 _)

theorem det_of_cols {m : ℕ} (l : Fin m) (hl : (l : ℕ) + 1 = m) (M : Matrix (Fin m) (Fin m) F)
    (h : ∀ i j, j ≠ l → M i j = (1 : Matrix (Fin m) (Fin m) F) i j) : M.det = M l l := by
  have hlt : ∀ j : Fin m, j ≠ l → j < l := fun j hj => by
    rw [Fin.lt_iff_val_lt_val]; have := j.2; have : (j : ℕ) ≠ l := fun e => hj (Fin.ext e); omega
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_single l (fun i _ hi => ?_) (fun h' => absurd (Finset.mem_univ l) h')
    rw [h i i hi, Matrix.one_apply_eq]
  · intro i j hij
    have hj : j ≠ l := fun e => by subst e; exact absurd (hlt i (ne_of_gt hij)) (not_lt.2 (le_of_lt hij))
    rw [h i j hj]; exact Matrix.one_apply_ne (ne_of_gt hij)

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin.FreeCusp

theorem hfree_two_le {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (k m : ℕ) (hm : 2 ≤ m) :
    HFree (cusp θ m k) := by
  intro _
  letI := Fintype.ofFinite F
  let l : Fin m := ⟨m - 1, by omega⟩
  have hl1 : (l : ℕ) + 1 = m := by simp only [l]; omega
  have hjl : ∀ j : Fin m, (j : ℕ) + 1 < m ↔ j ≠ l := fun j => by
    constructor
    · intro h e; rw [e] at h; omega
    · intro h; have := j.2; have : (j : ℕ) ≠ m - 1 := fun e => h (Fin.ext e); omega
  have hs : IsAdditive (rootSum θ k) := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  haveI : Finite (Module.End F (Fin m → F)) := Finite.of_injective _ DFunLike.coe_injective
  have hN : (nilRad (hyp l) : Set (Module.End F (Fin m → F))).Finite := Set.toFinite _
  have hSf : {x : GL (Fin m) F | ∀ i j : Fin m, (j : ℕ) + 1 < m →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j}.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf]
  unfold cusp
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  unfold psiG
  have hNcols : ∀ (d : F) (h : Module.End F (Fin m → F)), h ∈ nilRad (hyp l) → ∀ i j, j ≠ l →
      LinearMap.toMatrix' (Matrix.toLin' (dg l d) + h) i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
    intro d h hh i j hj
    rw [map_add, LinearMap.toMatrix'_toLin', Matrix.add_apply, (of_mem_nilRad l h hh).1 i j hj, add_zero,
      dg_off l d i j hj]
  have hNll : ∀ (d : F) (h : Module.End F (Fin m → F)), h ∈ nilRad (hyp l) →
      LinearMap.toMatrix' (Matrix.toLin' (dg l d) + h) l l = d := by
    intro d h hh
    rw [map_add, LinearMap.toMatrix'_toLin', Matrix.add_apply, (of_mem_nilRad l h hh).2, add_zero]
    simp [dg]
  have hxcols : ∀ x ∈ hSf.toFinset, ∀ i j, j ≠ l →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j := by
    intro x hx i j hj
    exact (hSf.mem_toFinset.1 hx) i j ((hjl j).2 hj)
  have key : ∑ x ∈ hSf.toFinset, psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))
      = ∑ p ∈ (Finset.univ.filter (fun d : F => d ≠ 0)) ×ˢ hN.toFinset,
        psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (dg l p.1) + p.2) := by
    refine Finset.sum_bij'
      (fun x _ => ((x : Matrix (Fin m) (Fin m) F) l l,
        Matrix.toLin' ((x : Matrix (Fin m) (Fin m) F) - dg l ((x : Matrix (Fin m) (Fin m) F) l l))))
      (fun p hp => Matrix.GeneralLinearGroup.mk'' (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2))
        (by
          have hp' := Finset.mem_product.1 hp
          have h1 := (Finset.mem_filter.1 hp'.1).2
          have h2 := hN.mem_toFinset.1 hp'.2
          rw [det_of_cols l hl1 _ (hNcols _ _ h2), hNll _ _ h2]
          exact h1.isUnit)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hd : (x : Matrix (Fin m) (Fin m) F) l l ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det x).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply, det_of_cols l hl1 _ (hxcols x hx)] at this
      refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, hN.mem_toFinset.2 ?_⟩
      refine mem_nilRad_of l _ (fun i j hj => ?_) ?_
      · rw [Matrix.sub_apply, hxcols x hx i j hj, dg_off l _ i j hj, sub_self]
      · rw [Matrix.sub_apply]; simp [dg]
    · intro p hp
      have hp' := Finset.mem_product.1 hp
      have h2 := hN.mem_toFinset.1 hp'.2
      refine hSf.mem_toFinset.2 fun i j hj => ?_
      exact hNcols _ _ h2 i j ((hjl j).1 hj)
    · intro x hx
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      change LinearMap.toMatrix' _ i j = _
      rw [← map_add, add_sub_cancel, LinearMap.toMatrix'_toLin']
    · intro p hp
      have hp' := Finset.mem_product.1 hp
      have h2 := hN.mem_toFinset.1 hp'.2
      change (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2) l l,
        Matrix.toLin' (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2)
          - dg l (LinearMap.toMatrix' (Matrix.toLin' (dg l p.1) + p.2) l l))) = p
      rw [hNll _ _ h2, map_sub, Matrix.toLin'_toMatrix', add_sub_cancel_left]
    · intro x hx
      congr 1
      rw [map_sub, add_sub_cancel]
  rw [key, Finset.sum_product]
  have hA0 : hyp (F := F) l ≠ ⊥ := by
    intro e
    have h0 : Pi.single (⟨0, by omega⟩ : Fin m) (1 : F) ∈ hyp l :=
      (mem_hyp l _).2 (Pi.single_eq_of_ne (fun e' => by have := congrArg Fin.val e'; simp [l] at this; omega) _)
    rw [e, Submodule.mem_bot] at h0
    have := congr_fun h0 ⟨0, by omega⟩
    simp at this
  have hA1 : hyp (F := F) l ≠ ⊤ := by
    intro e
    have h0 : Pi.single l (1 : F) ∈ hyp l := e ▸ Submodule.mem_top
    rw [mem_hyp] at h0
    simp at h0
  refine Finset.sum_eq_zero fun d _ => ?_
  dsimp only
  rw [← finsum_mem_eq_finite_toFinset_sum]
  refine isPrimitive_psi F _ _ hs (hyp l) hA0 hA1 _ fun v hv => ?_
  rw [mem_hyp] at hv ⊢
  rw [Matrix.toLin'_apply, dg, Matrix.mulVec_diagonal, hv, mul_zero]

end GlobalTheory.Shin.FreeCusp

namespace GlobalTheory.Shin

theorem hFree_cusp : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k : ℕ, (2 ≤ m ∨ ¬ k ≡ 0 [MOD Nat.card F - 1]) → HFree (cusp θ m k) := by
  intro F _ _ θ hθ m k h
  rcases h with hm | hk
  · exact FreeCusp.hfree_two_le θ k m hm
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · intro h0; exact absurd h0 (lt_irrefl 0)
      · exact FreeCusp.hfree_one θ hθ k hk
    · exact FreeCusp.hfree_two_le θ k m hm

end GlobalTheory.Shin

end
