import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.MemSpanOfSharpG

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem idem_mem_O (L : LocE F E) {x : E} (hx : x * x = x) : x ∈ L.O := by
  rw [L.O_def]
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
  simp [Polynomial.eval₂_sub, sq, hx]

theorem mem_O_of_comp {M : Model F E} (g : SplitG M.L) (x : E) (h1 : (g.e x).1 ∈ 𝒪[F])
    (h2 : (g.e x).2 ∈ 𝒪[F]) : x ∈ M.L.O := by
  rw [M.L.O_def]
  have hx : x = ((g.e x).1 : F) • g.e.symm (1, 0) + ((g.e x).2 : F) • g.e.symm (0, 1) := by
    apply g.e.injective
    simp only [map_add, map_smul, AlgEquiv.apply_symm_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
      Prod.mk_add_mk, add_zero, zero_add]
  have hid : ∀ y : F × F, y * y = y → IsIntegral 𝒪[F] (g.e.symm y) := by
    intro y hy
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    rw [sq, ← map_mul, hy, sub_self]
  have hsc : ∀ (c : F) (hc : c ∈ 𝒪[F]) (y : E), IsIntegral 𝒪[F] y → IsIntegral 𝒪[F] (c • y) := by
    intro c hc y hy
    have e : c • y = algebraMap 𝒪[F] E ⟨c, hc⟩ * y := by
      rw [Algebra.smul_def]
      rfl
    rw [e]
    exact (isIntegral_algebraMap).mul hy
  rw [hx]
  exact (hsc _ h1 _ (hid (1, 0) (by simp))).add (hsc _ h2 _ (hid (0, 1) (by simp)))

theorem comp_of_mem_R {M : Model F E} {g : SplitG M.L} (hs : M.split = some g) {x : E} (hx : x ∈ M.R) :
    (g.e x).1 ∈ 𝒪[F] ∧ (g.e x).2 ∈ 𝒪[F] ∧ ∃ c : 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c := by
  unfold Model.R at hx
  simp only [hs, Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨p, hp, hpe⟩ := hx
  have e1 : (g.e x).1 = (p.1 : F) := by
    have := congrArg Prod.fst hpe
    simpa using this.symm
  have e2 : (g.e x).2 = (p.2 : F) := by
    have := congrArg Prod.snd hpe
    simpa using this.symm
  rw [RingHom.mem_eqLocus] at hp
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst, RingHom.coe_snd] at hp
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hp
  obtain ⟨c, hc⟩ := hp
  refine ⟨by rw [e1]; exact p.1.2, by rw [e2]; exact p.2.2, c, ?_⟩
  rw [e1, e2, mul_comm]
  exact_mod_cast hc.symm

variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem zz_comp {g : SplitG M.L} (hs : M.split = some g) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (T T' : F) (a b : Fin (r + 1)) :
    g.e (HermSp.ZZplusOf M Z T T' a b) =
      ((g.e (Z a b)).1 / (g.q : F) - (if a = Fin.last r ∧ b = Fin.last r then -T / (g.q : F) else 0),
       -((g.e (Z b a)).2 / (g.q : F)) - (if a = Fin.last r ∧ b = Fin.last r then T' / (g.q : F) else 0)) := by
  unfold HermSp.ZZplusOf
  rw [hs]
  simp only [Matrix.of_apply]
  split_ifs with h <;> simp [map_sub, h]

theorem mmInt_G {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (hT : t.T ∈ 𝒪[F])
    (hTT : ∃ c : 𝒪[F], t.T - t.T' = (g.q : F) ^ 2 * c)
    (hR : ∀ a b, HermSp.ZZplusOf M (H.Zhat t.f t.f') t.T t.T' a b ∈ M.R) : MMInt H t := by
  have hq := q_ne g
  obtain ⟨c0, hc0⟩ := hTT
  have hqO : (g.q : F) ∈ 𝒪[F] := g.q.2
  have hR' := fun a b => (zz_comp hg.1 (H.Zhat t.f t.f') t.T t.T' a b) ▸ comp_of_mem_R hg.1 (hR a b)
  have ecj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap := g.e_cj
  have eal : ∀ x : F, g.e (algebraMap F E x) = (x, x) := fun x => by
    rw [AlgEquiv.commutes]; rfl
  have hgen : ∀ i j, H.h (H.MMfam t i) (H.MMfam t j) ∈ M.L.O := by
    intro i j
    have := congrFun (congrFun (gramH_eqG H hg) i) j
    change H.h (H.MMfam t i) (H.MMfam t j) = _ at this
    rw [this]
    rcases i with a | a <;> rcases j with b | b
    · simp only [gramG, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, cor]
      split_ifs
      · exact M.L.O.neg_mem (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T, hT⟩)
      · exact M.L.O.zero_mem
    · simp only [gramG, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      obtain ⟨-, A2, -⟩ := hR' b a
      obtain ⟨A1, -, -⟩ := hR' a b
      apply mem_O_of_comp g
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A2 ⊢
          simp only [map_mul, map_add, ecj, eal, Prod.fst_mul, Prod.fst_add, Prod.fst_swap]
          convert add_mem (neg_mem A2) (mul_mem hqO c0.2) using 1
          field_simp
          linear_combination hc0
        · have h' : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h'' => h ⟨h''.2, h''.1⟩
          simp only [cor, h, h', if_false] at A2 ⊢
          simp only [map_mul, map_add, ecj, eal, Prod.fst_mul, Prod.fst_add, Prod.fst_swap, map_zero,
            Prod.fst_zero, add_zero]
          convert neg_mem A2 using 1
          field_simp
          ring
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A1 ⊢
          simp only [map_mul, map_add, ecj, eal, Prod.snd_mul, Prod.snd_add, Prod.snd_swap]
          convert A1 using 1
          field_simp
          ring
        · simp only [cor, h, if_false] at A1 ⊢
          simp only [map_mul, map_add, ecj, eal, Prod.snd_mul, Prod.snd_add, Prod.snd_swap, map_zero,
            Prod.snd_zero, add_zero]
          convert A1 using 1
          field_simp
          ring
    · simp only [gramG, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
      obtain ⟨-, A2, -⟩ := hR' a b
      obtain ⟨A1, -, -⟩ := hR' b a
      apply mem_O_of_comp g
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A1 ⊢
          simp only [map_mul, map_add, eal, Prod.fst_mul, Prod.fst_add]
          convert A1 using 1
          field_simp
          ring
        · have h' : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h'' => h ⟨h''.2, h''.1⟩
          simp only [cor, h, h', if_false] at A1 ⊢
          simp only [map_mul, map_add, eal, Prod.fst_mul, Prod.fst_add, map_zero, Prod.fst_zero, add_zero]
          convert A1 using 1
          field_simp
          ring
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A2 ⊢
          simp only [map_mul, map_add, eal, Prod.snd_mul, Prod.snd_add]
          convert add_mem (neg_mem A2) (mul_mem hqO c0.2) using 1
          field_simp
          linear_combination hc0
        · simp only [cor, h, if_false] at A2 ⊢
          simp only [map_mul, map_add, eal, Prod.snd_mul, Prod.snd_add, map_zero, Prod.snd_zero, add_zero]
          convert neg_mem A2 using 1
          field_simp
          ring
    · simp only [gramG, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      obtain ⟨-, -, c, A3⟩ := hR' b a
      obtain ⟨-, -, c', A3'⟩ := hR' a b
      apply mem_O_of_comp g
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A3 ⊢
          simp only [map_mul, map_add, map_sub, map_neg, ecj, eal, Prod.fst_mul, Prod.fst_add,
            Prod.fst_sub, Prod.fst_neg, Prod.fst_swap]
          convert neg_mem c.2 using 1
          field_simp at A3 ⊢
          first | linear_combination A3 | linear_combination -A3 | linear_combination (g.q : F) * A3 | linear_combination -(g.q : F) * A3
        · have h' : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h'' => h ⟨h''.2, h''.1⟩
          simp only [cor, h, h', if_false] at A3 ⊢
          simp only [map_mul, map_add, map_sub, map_neg, ecj, eal, Prod.fst_mul, Prod.fst_add,
            Prod.fst_sub, Prod.fst_neg, Prod.fst_swap, map_zero, Prod.fst_zero, sub_zero]
          convert neg_mem c.2 using 1
          field_simp at A3 ⊢
          first | linear_combination A3 | linear_combination -A3 | linear_combination (g.q : F) * A3 | linear_combination -(g.q : F) * A3
      · by_cases h : a = Fin.last r ∧ b = Fin.last r
        · obtain ⟨rfl, rfl⟩ := h
          simp only [cor, and_self, if_true] at A3' ⊢
          simp only [map_mul, map_add, map_sub, map_neg, ecj, eal, Prod.snd_mul, Prod.snd_add,
            Prod.snd_sub, Prod.snd_neg, Prod.snd_swap]
          convert neg_mem c'.2 using 1
          field_simp at A3' ⊢
          first | linear_combination A3' | linear_combination -A3' | linear_combination (g.q : F) * A3' | linear_combination -(g.q : F) * A3'
        · simp only [cor, h, if_false] at A3' ⊢
          simp only [map_mul, map_add, map_sub, map_neg, ecj, eal, Prod.snd_mul, Prod.snd_add,
            Prod.snd_sub, Prod.snd_neg, Prod.snd_swap, map_zero, Prod.snd_zero, sub_zero]
          convert neg_mem c'.2 using 1
          field_simp at A3' ⊢
          first | linear_combination A3' | linear_combination -A3' | linear_combination (g.q : F) * A3' | linear_combination -(g.q : F) * A3'
  have h1 : ∀ i, ∀ m' ∈ MMo H t, H.h (H.MMfam t i) m' ∈ M.L.O := by
    intro i m' hm'
    unfold MMo at hm'
    induction hm' using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hgen i j
    | zero => rw [h_zero_right]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [h_add_right]; exact M.L.O.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, h_smul_right]; exact M.L.O.mul_mem (cj_mem_O M.L a.2) hx
  intro m hm m' hm'
  unfold MMo at hm
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h1 i m' hm'
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul a x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact M.L.O.mul_mem a.2 hx

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
