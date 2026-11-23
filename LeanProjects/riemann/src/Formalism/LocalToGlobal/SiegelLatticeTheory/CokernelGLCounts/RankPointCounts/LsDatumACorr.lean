import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAInj

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrLemmas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

private theorem h_finset_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simpa using H.h_smul_left 0 0 y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

private theorem h_add_right_rank_point_counts (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

private theorem h_smul_right_eq_cj_mul (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

private theorem h_zero_right_rank_point_counts (x : V) : H.h x 0 = 0 := by
  simpa using h_add_right_rank_point_counts H x 0 0

theorem mem_perpX_of {f : Fin (r + 1) → V} {v : V} (h : ∀ j : Fin r, H.h v (f j.castSucc) = 0) :
    v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h v x = 0
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact h j
  | zero => exact h_zero_right_rank_point_counts H v
  | add y z _ _ hy hz => rw [h_add_right_rank_point_counts, hy, hz, add_zero]
  | smul a y _ hy => rw [h_smul_right_eq_cj_mul, hy, mul_zero]

theorem z_mem_perpX {f : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) :
    f (Fin.last r) ∈ H.perp (H.X f) :=
  mem_perpX_of H fun j => hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne)

theorem om'_mem_perpX (f f' : Fin (r + 1) → V) : H.om' f f' ∈ H.perp (H.X f) := by
  refine mem_perpX_of H fun j => ?_
  unfold HermSp.om'
  rw [h_sum_smul_left]
  have e := congrFun (congrFun (mul_adjugate (H.Zhat f f')) j.castSucc) (Fin.last r)
  rw [Matrix.smul_apply, one_apply_ne (Fin.castSucc_lt_last j).ne, smul_zero, mul_apply] at e
  rw [← e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [HermSp.Zhat, Matrix.of_apply]
  ring

theorem om'_mem_U (f f' : Fin (r + 1) → V) :
    H.om' f f' ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
  unfold HermSp.om'
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)

theorem decomp_U_perpX {f f' : Fin (r + 1) → V} {T : F} (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hZ : IsUnit (H.Zhat f f').det) {u : V} (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (hp : u ∈ H.perp (H.X f)) :
    ∃ x ∈ H.X f, ∃ β γ : E, u = x + β • f (Fin.last r) + γ • H.om' f f' := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hu
  obtain ⟨a, p, rfl⟩ : ∃ a p, c = Sum.elim a p := ⟨c ∘ Sum.inl, c ∘ Sum.inr, by ext (i | i) <;> rfl⟩
  have hp' : ∀ x ∈ H.X f, H.h (∑ i, Sum.elim a p i • Sum.elim f f' i) x = 0 := hp
  rw [Fintype.sum_sum_type] at hp' ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at hp' ⊢
  obtain ⟨d, hd⟩ := hZ
  have hperp : ∀ j : Fin r, (H.Zhat f f' *ᵥ p) j.castSucc = 0 := by
    intro j
    have h0 := hp' (f j.castSucc) (Submodule.subset_span ⟨j, rfl⟩)
    rw [H.h_add_left, h_finset_sum_smul_left, h_finset_sum_smul_left,
      Finset.sum_eq_zero (fun i _ => by rw [hF.1 _ _ (Or.inr (Fin.castSucc_lt_last j).ne), mul_zero]),
      zero_add] at h0
    refine Eq.trans ?_ h0
    simp only [Matrix.mulVec, dotProduct, HermSp.Zhat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZp : H.Zhat f f' *ᵥ p = Pi.single (Fin.last r) ((H.Zhat f f' *ᵥ p) (Fin.last r)) := by
    funext k
    by_cases hk : k = Fin.last r
    · subst hk
      simp
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
      rw [hperp j, Pi.single_eq_of_ne hk]
  have hp2 : ∀ b, p b = (↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r)) * (H.Zhat f f').adjugate b (Fin.last r) := by
    intro b
    have h1 : (H.Zhat f f').adjugate *ᵥ (H.Zhat f f' *ᵥ p) = (H.Zhat f f').det • p := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 b
    rw [hZp] at h2
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul] at h2
    rw [← hd] at h2
    calc p b = ↑d⁻¹ * (↑d * p b) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by
        rw [← h2]
        simp only [Matrix.mulVec, dotProduct]
        ring
  refine ⟨∑ j : Fin r, a j.castSucc • f j.castSucc, ?_, a (Fin.last r),
    ↑d⁻¹ * (H.Zhat f f' *ᵥ p) (Fin.last r), ?_⟩
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Fin.sum_univ_castSucc (fun i => a i • f i)]
    congr 1
    unfold HermSp.om'
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, ← hp2 b]

theorem Gdet_rel (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (h : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Gdet f₂ f₂' T T' * H.normE (H.Dl f₁ f₁' (r + 1)) =
      H.normE (H.Dl f₂ f₂' (r + 1)) * H.Gdet f₁ f₁' T T' := by
  unfold HermSp.Gdet HermSp.normE
  have h' : M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1)) =
      M.L.cj (H.Dl f₂ f₂' r) * M.L.cj (H.Dl f₁ f₁' (r + 1)) := by
    rw [← map_mul, ← map_mul, h]
  linear_combination (algebraMap F E (T * T')) * (M.L.cj (H.Dl f₁ f₁' r) * M.L.cj (H.Dl f₂ f₂' (r + 1))) * h +
    (algebraMap F E (T * T')) * (H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) * h'

end CorrLemmas

end Formalism.L2.SG.LsDatumA
