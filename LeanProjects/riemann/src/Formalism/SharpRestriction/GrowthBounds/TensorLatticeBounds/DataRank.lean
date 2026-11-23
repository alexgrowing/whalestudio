import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLP

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Const

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

theorem mem_span_one {σ : Type} (F : MvPolynomial σ K) :
    F ∈ Submodule.span R {(1 : MvPolynomial σ K)} ↔ ∃ a : R, F = C (algebraMap R K a) := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_apply]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_apply]⟩

theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by funext t; simp [nuOf]

theorem nablaLTw_le_const (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    nablaLTw R K m 0 g ≤ Submodule.span R {1} := by
  intro F hF
  have h1 := LatticeSystems.la_nablaLTw_le m 0 g hg F hF
  rw [nuOf_zero] at h1
  have h2 := const_of_dualWeyl K _ _ F h1
  obtain ⟨a, ha⟩ := (mem_ccInt R K _).1 (nablaLTw_le_ccInt R K m g hF)
  exact (mem_span_one R K F).2 ⟨a, by rw [ha]; exact h2⟩

theorem applyWord_one (k : ℕ) (w : List (Fin k × Fin k × ℕ)) :
    ∃ a : R, applyWord R w (1 : MvPolynomial (Fin k × Fin k) R) = C a := by
  induction w with
  | nil => exact ⟨1, by simp [applyWord]⟩
  | cons x w ih =>
    obtain ⟨a, ha⟩ := ih
    have h1 : applyWord R (x :: w) (1 : MvPolynomial (Fin k × Fin k) R) =
        rowDiv R x.1 x.2.1 x.2.2 (applyWord R w 1) := rfl
    rw [h1, ha]
    unfold rowDiv
    have h2 : rowGen R x.1 x.2.1 (C a : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C a) := by
      have := (rowGen R (n := k) x.1 x.2.1).commutes a
      rw [MvPolynomial.algebraMap_eq] at this
      rw [this]
      rfl
    rw [h2, Polynomial.coeff_C]
    split_ifs
    · exact ⟨a, rfl⟩
    · exact ⟨0, by simp⟩

theorem weyl_zero_const (k : ℕ) (P : MvPolynomial (Fin k × Fin k) R) (hP : P ∈ weyl R k k le_rfl 0) :
    ∃ a : R, P = C a := by
  unfold weyl at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    have h1 : hw R (le_refl k) (0 : Fin k → ℕ) = 1 := by simp [hw]
    simp only [h1]
    exact applyWord_one R k w
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨c * a, by rw [smul_eq_C_mul, map_mul]⟩

theorem rowAct_one' (k n : ℕ) : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowAct_cancel (k n : ℕ) (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (F : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g⁻¹ (rowAct K g F) = F := by
  have h1 := rowActMul K k n g⁻¹ g
  rw [Matrix.mul_nonsing_inv g hg, rowAct_one'] at h1
  exact congrArg (fun f : MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (Fin k × Fin n) K => f F) h1

theorem deltaLTw_le_const (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    deltaLTw R K m 0 g ≤ Submodule.span R {1} := by
  rintro F ⟨F', hF', rfl⟩
  obtain ⟨P, hP, hPF⟩ := hF'
  rw [nuOf_zero] at hP
  obtain ⟨a, rfl⟩ := weyl_zero_const R _ P hP
  have h1 : rowAct K g F' = C (algebraMap R K a) := by
    have : mapAlgHom (Algebra.ofId R K) (C a : MvPolynomial _ R) = rowAct K g F' := hPF
    rw [← this, mapAlgHom_apply, map_C]
    rfl
  have h2 : F' = C (algebraMap R K a) := by
    rw [← rowAct_cancel K _ _ g hg F', h1]
    simp [rowAct]
  refine (mem_span_one R K _).2 ⟨a, ?_⟩
  simp [h2]

theorem H0_degree_zero_le_constants (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) (hΛ : IsLattice R Λ) :
    H0 R m 0 Λ ≤ Submodule.span R {1} := by
  obtain ⟨g, hg, rfl⟩ := hΛ
  exact (LatticeSystems.H0_le_twisted_nabla m 0 (fun _ _ _ => le_rfl) g hg).trans (nablaLTw_le_const R K m g hg)

theorem Dl0_le_const (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) (hΛ : IsLattice R Λ) :
    Dl0 R m 0 Λ ≤ Submodule.span R {1} := by
  obtain ⟨g, hg, rfl⟩ := hΛ
  unfold Dl0
  rw [if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]
  exact (iInf₂_le g ⟨hg, rfl⟩).trans (deltaLTw_le_const R K m g hg)

theorem tensorLat_le_const {S : Type} [Fintype S] {k n : ℕ} (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, M s ≤ Submodule.span R {1}) : tensorLat R K M ≤ Submodule.span R {1} := by
  unfold tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  choose a ha using fun s => (mem_span_one R K _).1 (h s (hF s))
  refine (mem_span_one R K _).2 ⟨∏ s, a s, ?_⟩
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [ha s, blockEmb, rename_C]

end Const

section Tup

variable {p : ℕ} (G : GAtP p) (h0 : ∀ v, G.P.lam0 v = fun _ _ => 0)

theorem tenV_le_const (M : ∀ v, Submodule G.O (MvPolynomial (Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf))
    (h : ∀ v, M v ≤ Submodule.span G.O {1}) : G.P.tenV M ≤ Submodule.span G.O {1} := by
  unfold Places.tenV
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  choose a ha using fun v => (mem_span_one G.O G.Kf _).1 (h v (hF v))
  refine (mem_span_one G.O G.Kf _).2 ⟨∏ v, a v, ?_⟩
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [ha v, Places.vEmb, rename_C]

include h0 in
theorem Htup_le_const (L : G.P.Tup) (hL : G.P.IsLatTup L) : G.P.Htup L ≤ Submodule.span G.O {1} := by
  refine tenV_le_const G _ fun v => ?_
  unfold Hten
  refine tensorLat_le_const G.O G.Kf _ fun s => ?_
  rw [h0 v, lamAt_zero]
  exact H0_degree_zero_le_constants G.O G.Kf _ _ (LatticeSystems.je_extO_lat G v s.val (L v) (hL v))

include h0 in
theorem HtupW_le_const (L : G.P.Tup) (hL : G.P.IsLatTup L) : G.P.HtupW L ≤ Submodule.span G.O {1} := by
  refine tenV_le_const G _ fun v => ?_
  unfold HtenW
  refine tensorLat_le_const G.O G.Kf _ fun s => ?_
  rw [h0 v, lamAt_zero]
  exact Dl0_le_const G.O G.Kf _ _ (LatticeSystems.je_extO_lat G v s.val (L v) (hL v))

end Tup

end Formalism.MainNotions.G.Inhab

end
