import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagAmple.PlkLoc.LowerTri

open GlobalTheory.FlagEmb

theorem exists_lower_of_rows {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hB : IsUnit B.det)
    (h : ∀ i : Fin n, ∃ c : Fin n → K, (∀ l, i < l → c l = 0) ∧ A i = Matrix.vecMul c B) :
    ∃ L : Matrix (Fin n) (Fin n) K, A = L * B ∧ ∀ i l, i < l → L i l = 0 := by
  refine ⟨A * B⁻¹, by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one], ?_⟩
  intro i l hil
  obtain ⟨c, hc, hA⟩ := h i
  have hrow : (A * B⁻¹) i = c := by
    have h1 : (A * B⁻¹) i = Matrix.vecMul (A i) B⁻¹ := by
      ext k
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [h1, hA, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]
  rw [hrow]
  exact hc l hil

theorem row_mem_span {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (hB : IsUnit B.det) (i : Fin n)
    (h : (i : ℕ) + 1 < n)
    (hp : ∃ r : Kˣ, plk (what₂ A ⟨(i : ℕ) + 1, h⟩) id = (r : K) • plk (what₂ B ⟨(i : ℕ) + 1, h⟩) id) :
    ∃ c : Fin n → K, (∀ l, i < l → c l = 0) ∧ A i = Matrix.vecMul c B := by
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hind : LinearIndependent K (what₂ B ⟨(i : ℕ) + 1, h⟩) := by
    have h0 := Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det B).2 hB)
    have h1 : LinearIndependent K (fun l : Fin ((i : ℕ) + 1) => B (Fin.castLE h.le l)) :=
      h0.comp _ (Fin.castLE_injective _)
    have h2 := h1.map' (LinearEquiv.funCongrLeft K K (finCongr hn)).toLinearMap (LinearEquiv.ker _)
    have he : what₂ B ⟨(i : ℕ) + 1, h⟩ =
        (LinearEquiv.funCongrLeft K K (finCongr hn)).toLinearMap ∘ fun l => B (Fin.castLE h.le l) := by
      funext l c
      rfl
    rw [he]
    exact h2
  obtain ⟨_, hs⟩ := ((GlobalTheory.FlagEmb.PlkSpan.main K (n - 1) ((i : ℕ) + 1) (what₂ B ⟨(i : ℕ) + 1, h⟩)
    (what₂ A ⟨(i : ℕ) + 1, h⟩)).2 hind).2 hp
  have hmem : what₂ A ⟨(i : ℕ) + 1, h⟩ (Fin.last i) ∈ Submodule.span K (Set.range (what₂ B ⟨(i : ℕ) + 1, h⟩)) :=
    hs ▸ Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨fun l => if hl : (l : ℕ) < (i : ℕ) + 1 then d ⟨l, hl⟩ else 0, ?_, ?_⟩
  · intro l hl
    have : ¬ ((l : ℕ) < (i : ℕ) + 1) := by
      have := Fin.lt_def.1 hl
      omega
    simp [this]
  · funext k
    have hk := congrFun hd (Fin.cast hn.symm k)
    simp only [what₂, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.cast_cast, Fin.cast_eq_self] at hk
    have hl : Fin.castLE h.le (Fin.last (i : ℕ)) = i := by ext; simp
    rw [hl] at hk
    rw [← hk, Matrix.vecMul, dotProduct]
    refine Fintype.sum_of_injective (Fin.castLE h.le) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro l hl'
      have : ¬ ((l : ℕ) < (i : ℕ) + 1) := fun hlt => hl' ⟨⟨l, hlt⟩, by ext; simp⟩
      simp [this]
    · intro c
      have hc : ((Fin.castLE h.le c : Fin n) : ℕ) < (i : ℕ) + 1 := by simpa using c.2
      simp only [dif_pos hc]
      rfl

theorem eq_lower_mul_of_plk_prop : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (K : Type) [Field K] (M M' : GlobalTheory.FlagBundle.Mat S.Dw.mult K), (∀ τ, IsUnit (M τ).det) → (∀ τ, IsUnit (M' τ).det) → (∀ x : GlobalTheory.FlagAmple.Step S.Dw, ∃ u : Kˣ, GlobalTheory.FlagAmple.PlkLoc.plkFn M x = (u : K) • GlobalTheory.FlagAmple.PlkLoc.plkFn M' x) → ∀ τ, ∃ L : Matrix (Fin (S.Dw.mult τ)) (Fin (S.Dw.mult τ)) K, M τ = L * M' τ ∧ ∀ i l, i < l → L i l = 0 := by
  intro D A N j S K _ M M' _ hM' hp τ
  refine exists_lower_of_rows (M τ) (M' τ) (hM' τ) fun i => ?_
  by_cases h : (i : ℕ) + 1 < S.Dw.mult τ
  · obtain ⟨u, hu⟩ := hp ⟨τ, ⟨⟨(i : ℕ) + 1, h⟩, Nat.succ_pos _⟩⟩
    exact row_mem_span (M τ) (M' τ) (hM' τ) i h ⟨u, hu⟩
  · refine ⟨Matrix.vecMul (M τ i) (M' τ)⁻¹, fun l hl => ?_, ?_⟩
    · exfalso
      have h1 := Fin.lt_def.1 hl
      have h2 := l.2
      omega
    · rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hM' τ), Matrix.vecMul_one]

end GlobalTheory.FlagAmple.PlkLoc.LowerTri
