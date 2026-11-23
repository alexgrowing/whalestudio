import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.UpSmith
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ComapFgOfValuationRing

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rb

theorem triang_strong (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (n : ℕ) (L : Submodule R (Fin n → R)) (hL : L.FG) :
    ∃ d : Fin n → R, (∀ i c, c ∈ Ideal.span {d i} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c) ∧
      HasLen v R ((Fin n → R) ⧸ L) (∏ i, v (algebraMap R C (d i))) := by
  classical
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  obtain ⟨m, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let ψ : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R w
  have hψ : LinearMap.range ψ = L := by rw [Fintype.range_linearCombination, hw]
  have key : ∀ i : Fin n, ∃ d : R,
      ∀ c, c ∈ Ideal.span {d} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c := by
    intro i
    let π : (Fin n → R) →ₗ[R] ({j : Fin n // j < i} → R) := LinearMap.funLeft R R Subtype.val
    have h1 := comap_fg_of_valuationRing R (Fin m) {j : Fin n // j < i} (π ∘ₗ ψ) ⊥
      Submodule.fg_bot
    have h2 : Ideal.FG (R := R) (((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ)) := h1.map _
    obtain ⟨d, hd⟩ := (IsBezout.isPrincipal_of_FG _ h2).principal
    refine ⟨d, fun c => ?_⟩
    have : Ideal.span {d} = ((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ) := hd.symm
    rw [this]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨ψ a, hψ ▸ LinearMap.mem_range_self ψ a, fun j hj => ?_, rfl⟩
      exact congrFun (show π (ψ a) = 0 from ha) ⟨j, hj⟩
    · rintro ⟨l, hl, h0, rfl⟩
      rw [← hψ] at hl
      obtain ⟨a, rfl⟩ := hl
      refine ⟨a, ?_, rfl⟩
      show π (ψ a) = 0
      funext j
      exact h0 j.1 j.2
  choose d hd using key
  refine ⟨d, hd, ?_⟩
  choose u huL hu0 hud using fun i => (hd i (d i)).1 (Ideal.mem_span_singleton_self _)
  let X : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => u i j
  have hcol : ∀ i, u i ∈ LinearMap.range X.mulVecLin := fun i =>
    ⟨Pi.single i 1, by ext j; simp [X]⟩
  have hrange : LinearMap.range X.mulVecLin = L := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      have : X.mulVecLin a = ∑ i, a i • u i := by
        ext j
        simp [X, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact L.sum_mem fun i _ => L.smul_mem _ (huL i)
    · have hind : ∀ t : ℕ, ∀ l ∈ L, (∀ j : Fin n, (j : ℕ) + t < n → l j = 0) →
          l ∈ LinearMap.range X.mulVecLin := by
        intro t
        induction t with
        | zero =>
          intro l _ h0
          have : l = 0 := funext fun j => h0 j (by simp)
          rw [this]
          exact Submodule.zero_mem _
        | succ t ih =>
          intro l hl h0
          by_cases ht : t < n
          · let i : Fin n := ⟨n - 1 - t, by omega⟩
            have hi : (i : ℕ) = n - 1 - t := rfl
            have hlow : ∀ j, j < i → l j = 0 := fun j hj => h0 j (by
              have := Fin.lt_def.1 hj
              omega)
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((hd i (l i)).2 ⟨l, hl, hlow, rfl⟩)
            have h3 := ih (l - c • u i) (L.sub_mem hl (L.smul_mem _ (huL i))) (fun j hj => by
              rcases lt_or_eq_of_le (show j ≤ i from Fin.le_def.2 (by omega)) with h | h
              · simp [hlow j h, hu0 i j h]
              · subst h
                simp [hud, hc])
            have h4 := Submodule.add_mem _ h3 (Submodule.smul_mem _ c (hcol i))
            simpa using h4
          · exact ih l hl fun j hj => by omega
      intro l hl
      exact hind n l hl fun j hj => by omega
  have hdet : X.det = ∏ i, d i := by
    rw [Matrix.det_of_lowerTriangular X (fun j i h => hu0 i j h)]
    exact Finset.prod_congr rfl fun i _ => hud i
  have := Smith.hasLen_coker_det hv X
  rw [hrange, hdet, map_prod, map_prod] at this
  exact this

theorem triang : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (n : ℕ) (L : Submodule R (Fin n → R)), L.FG → ∃ d : Fin n → R, (∀ i c, c ∈ Ideal.span {d i} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c) ∧ ((∀ i, d i ≠ 0) → HasLen v R ((Fin n → R) ⧸ L) (∏ i, v (algebraMap R C (d i)))) := by
  intro C _ v R _ _ hv n L hL
  obtain ⟨d, h1, h2⟩ := triang_strong C v R hv n L hL
  exact ⟨d, h1, fun _ => h2⟩

end PositivityTheory.HtPt.Rb
