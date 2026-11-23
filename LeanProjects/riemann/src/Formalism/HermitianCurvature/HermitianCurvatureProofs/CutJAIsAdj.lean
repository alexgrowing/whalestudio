import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

section IsAdjProof

variable (P : M.Par)

def adjSub : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | IsAdj a}
  mul_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).2
  add_mem' {a b} ha hb := ((Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.1 a b ha hb).1
  algebraMap_mem' z := by
    have h := (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.1 z 1 (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).1
    rw [Algebra.algebraMap_eq_smul_one]
    exact h

theorem adjSub_star {a : (DQ P).Pr} (ha : a ∈ adjSub P) : star a ∈ adjSub P :=
  (Formalism.FourierDecayAlt.P.adjoint_closed P.r P.TT).2.2.2 a ha

theorem gen_adj (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : w ∈ adjSub P :=
  Formalism.FourierDecayAlt.P.adjoint_generators P.r P.TT hτ w hw

abbrev MSa : Subalgebra ℂ (A P (DQ P)) := Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (adjSub P) (M.Ty P)

theorem sc_memMS (hτ : 0 ≤ P.TT) {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : sc P (DQ P) w ∈ MSa P :=
  Formalism.FourierDecayAlt.P.MAx2.Jet.scalar_mem _ _ (gen_adj P hτ hw)

theorem star_memMS {a : A P (DQ P)} (ha : a ∈ MSa P) : star a ∈ MSa P := fun i j => by
  rw [Matrix.star_apply]; exact adjSub_star P (ha j i)

variable {P}

section Lv

variable (hτ : 0 ≤ P.TT) {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hτ hL

theorem lv_p (l : Fin P.r) : L.p l ∈ MSa P := by
  rw [hL.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_pb (l : Fin P.r) : L.pb l ∈ MSa P := by
  rw [hL.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_c (l : Fin P.r) : L.c l ∈ MSa P := by
  rw [hL.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ci (l : Fin P.r) : L.ci l ∈ MSa P := by
  rw [hL.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cb (l : Fin P.r) : L.cb l ∈ MSa P := by
  rw [hL.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_cbi (l : Fin P.r) : L.cbi l ∈ MSa P := by
  rw [hL.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem zeta_mem_self_adjoint : L.ζ ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zi : L.ζi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zb : L.ζb ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_zbi : L.ζbi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_gg : L.GG ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_ggi : L.GGi ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memMS P hτ (by simp [DAlg.gens])
theorem lv_nab : L.nab ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (gen_adj P hτ (by simp [DAlg.gens]))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)
theorem lv_nabs : L.nabs ∈ MSa P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (neg_mem (gen_adj P hτ (by simp [DAlg.gens])))
    (Subalgebra.smul_mem _ (mul_mem (gen_adj P hτ (by simp [DAlg.gens])) (gen_adj P hτ (by simp [DAlg.gens]))) _)

theorem lv_Dr : L.Dr ∈ MSa P := by
  unfold LevelData.Dr
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_c hτ hL l
theorem lv_Drb : L.Drb ∈ MSa P := by
  unfold LevelData.Drb
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cb hτ hL l
theorem lv_Dri : L.Dri ∈ MSa P := by
  unfold LevelData.Dri
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_ci hτ hL l
theorem lv_Drbi : L.Drbi ∈ MSa P := by
  unfold LevelData.Drbi
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lv_cbi hτ hL l

theorem lv_Tprod (Y : ℂ) : L.Tprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (Subalgebra.algebraMap_mem _ _) (lv_p hτ hL l)
  · exact neg_mem (lv_c hτ hL l)
  · exact lv_ci hτ hL l
  · exact zero_mem _

theorem lv_Tvprod (Y : ℂ) : L.Tvprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSa P) (Fin 2) := by
  unfold LevelData.Tvprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tvl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact sub_mem (Subalgebra.algebraMap_mem _ _) (lv_pb hτ hL l)
  · exact neg_mem (lv_cb hτ hL l)
  · exact lv_cbi hτ hL l
  · exact zero_mem _

theorem lv_hat {X : A P (DQ P)} (hX : X ∈ hatSet P L) : X ∈ MSa P := by
  have hl0 : ∀ Y, L.l0 Y ∈ MSa P := fun Y => by
    unfold LevelData.l0
    exact sub_mem (neg_mem (lv_nab hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (lv_zb hτ hL) (lv_ggi hτ hL)))
  have hm0 : ∀ Y, L.m0 Y ∈ MSa P := fun Y => by
    unfold LevelData.m0
    exact sub_mem (neg_mem (lv_nabs hτ hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (zeta_mem_self_adjoint hτ hL) (lv_ggi hτ hL)))
  rcases hX with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · exact mul_mem (lv_Dr hτ hL) (lv_Tprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Drb hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hl0 Y) (lv_Tprod hτ hL Y 0 0)) (lv_Tprod hτ hL Y 1 0))
  · exact mul_mem (lv_Drb hτ hL) (lv_Tvprod hτ hL Y 0 0)
  · exact mul_mem (mul_mem (lv_Dr hτ hL) (lv_gg hτ hL))
      (add_mem (mul_mem (hm0 Y) (lv_Tvprod hτ hL Y 0 0)) (lv_Tvprod hτ hL Y 1 0))

theorem lv_SS (i : ℕ) : SS P (DQ P) i ∈ MSa P := fun a b => by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact zero_mem _

theorem lv_kap (g : M.Ty P → ℂ) : kap P (DQ P) g ∈ MSa P := by
  have : kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) := rfl
  rw [this]
  exact Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => Subalgebra.algebraMap_mem _ _

theorem lv_bdd {b : A P (DQ P)} (hb : b ∈ bddSet P L) : b ∈ MSa P := by
  have hD : L.D ∈ MSa P := mul_mem (lv_Dr hτ hL) (zeta_mem_self_adjoint hτ hL)
  have hDi : L.Di ∈ MSa P := mul_mem (lv_zi hτ hL) (lv_Dri hτ hL)
  have hDb : L.Db ∈ MSa P := mul_mem (lv_Drb hτ hL) (lv_zb hτ hL)
  have hDbi : L.Dbi ∈ MSa P := mul_mem (lv_zbi hτ hL) (lv_Drbi hτ hL)
  have hS : ∀ i, L.Drb * L.Dri * SS P (DQ P) i ∈ MSa P := fun i =>
    mul_mem (mul_mem (lv_Drb hτ hL) (lv_Dri hτ hL)) (lv_SS hτ hL i)
  rcases hb with ((h4 | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h4
    rcases h4 with rfl | rfl | rfl | rfl
    · exact lv_zi hτ hL
    · exact lv_zbi hτ hL
    · exact mul_mem hD hDbi
    · exact mul_mem hDb hDi
  · exact lv_kap hτ hL g
  · exact hS i
  · exact star_memMS P (hS i)

end Lv

theorem transfer_is_adjoint_holds : JAIsAdj := by
  intro P L hτ hL a ha
  have hsub : Submonoid.closure (hatSet P L ∪ bddSet P L) ≤ (MSa P).toSubmonoid :=
    Submonoid.closure_le.2 fun x hx => by
      rcases hx with hx | hx
      · exact lv_hat (le_of_lt hτ) hL hx
      · exact lv_bdd (le_of_lt hτ) hL hx
  intro π π'
  exact hsub ha π π'

end IsAdjProof

end

end Formalism.FourierDecayAlt.P.CutMP.JA
