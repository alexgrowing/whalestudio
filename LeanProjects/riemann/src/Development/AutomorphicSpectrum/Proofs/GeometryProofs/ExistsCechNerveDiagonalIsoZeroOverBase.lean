import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEqSpanOfIsFrameAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagDet

theorem alt_triangular {Ω E W : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup W] [Module Ω W] {s : ℕ}
    (f : E [⋀^Fin s]→ₗ[Ω] W) (v w : Fin s → E) (c : Fin s → Ω)
    (h : ∀ i, v i - c i • w i ∈ Submodule.span Ω (w '' {k | k < i})) :
    f v = (∏ i, c i) • f w := by
  classical
  have key : ∀ j : ℕ, f v = f (fun i => if (i : ℕ) < j then c i • w i else v i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih]
      by_cases hj : j < s
      · obtain ⟨i, rfl⟩ : ∃ i : Fin s, (i : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
        have hnew : (fun k : Fin s => if (k : ℕ) < i + 1 then c k • w k else v k) =
            Function.update (fun k : Fin s => if (k : ℕ) < i then c k • w k else v k) i (c i • w i) := by
          funext k
          by_cases hk : k = i
          · rw [hk, Function.update_self, if_pos (Nat.lt_succ_self _)]
          · rw [Function.update_of_ne hk]
            have hk' : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
            by_cases hki : (k : ℕ) < i
            · rw [if_pos hki, if_pos (show (k : ℕ) < i + 1 by omega)]
            · rw [if_neg hki, if_neg (show ¬ ((k : ℕ) < i + 1) by omega)]
        rw [hnew]
        generalize hm : (fun k : Fin s => if (k : ℕ) < i then c k • w k else v k) = m
        have hmi : m i = v i := by
          rw [← hm]
          simp
        have hmk : ∀ k : Fin s, k < i → m k = c k • w k := by
          intro k hk
          rw [← hm]
          simp [Fin.lt_def.1 hk]
        have hzero : ∀ u ∈ Submodule.span Ω (w '' {k | k < i}), f (Function.update m i u) = 0 := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨k, hk, rfl⟩ := hx
            have hki : k ≠ i := ne_of_lt hk
            have hmk' : Function.update m i (w k) k = c k • w k := by
              rw [Function.update_of_ne hki]
              exact hmk k hk
            rw [← Function.update_eq_self k (Function.update m i (w k)), hmk', f.map_update_smul]
            rw [f.map_eq_zero_of_eq _ (i := k) (j := i)
              (by rw [Function.update_self, Function.update_of_ne hki.symm, Function.update_self]) hki,
              smul_zero]
          | zero => exact f.map_coord_zero i (by simp)
          | add x y _ _ hx hy => rw [f.map_update_add, hx, hy, add_zero]
          | smul a x _ hx => rw [f.map_update_smul, hx, smul_zero]
        have hv : v i = c i • w i + (v i - c i • w i) := by abel
        conv_lhs => rw [← Function.update_eq_self i m, hmi, hv, f.map_update_add]
        rw [hzero _ (h i), add_zero]
      · congr 1
        funext k
        have := k.2
        simp [show (k : ℕ) < j by omega, show (k : ℕ) < j + 1 by omega]
  rw [key s]
  have hfun : (fun i : Fin s => if (i : ℕ) < s then c i • w i else v i) = fun i => c i • w i := by
    funext i
    rw [if_pos i.2]
  rw [hfun]
  exact f.toMultilinearMap.map_smul_univ c w

theorem exists_diag {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b b₀ : Fin r → E}
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) :
    ∃ c : Ω, b i - c • b₀ i ∈ flagStep Ω b₀ i := by
  have hb : b i ∈ flagStep Ω b₀ ((i : ℕ) + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩
  have hset : b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = b₀ '' {k | (k : ℕ) < i} ∪ {b₀ i} := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases h : (k : ℕ) < i
      · exact Or.inl ⟨k, h, rfl⟩
      · right
        have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
        have : k = i := Fin.ext (by omega)
        rw [this, Set.mem_singleton_iff]
    · rintro (⟨k, hk, rfl⟩ | hx)
      · exact ⟨k, show (k : ℕ) < (i : ℕ) + 1 by have : (k : ℕ) < i := hk; omega, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, hx.symm⟩
  unfold flagStep at hb ⊢
  rw [hset, Submodule.span_union, Submodule.mem_sup] at hb
  obtain ⟨y, hy, z, hz, hyz⟩ := hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨c, by rw [← hyz, add_sub_cancel_right]; exact hy⟩

end GlobalTheory.CompanionTheory.Ar.FlagDet
