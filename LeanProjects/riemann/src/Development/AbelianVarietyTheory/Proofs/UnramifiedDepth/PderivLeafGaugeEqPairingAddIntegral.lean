import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstEqOfCoeffEqOfKilled
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.GaugeDeriv

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def linForm {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries (ι ⊕ ι') C :=
  (∑ c : ι, e c w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
    ∑ b : ι', e' b w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)

variable {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem hPullW_eq (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW H e e' = MvPowerSeries.subst (linForm e e') H := rfl

theorem constantCoeff_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries.constantCoeff (linForm e e' w) = 0 := by
  simp [linForm]

theorem hasSubst_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) :
    MvPowerSeries.HasSubst (linForm e e') := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_linForm e e' w)

theorem pderiv_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) (b : ι') :
    MvPowerSeries.pderiv C (Sum.inr b) (linForm e e' w) = MvPowerSeries.C (e' b w) := by
  classical
  simp [linForm, MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = MvPowerSeries.pderiv C w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem sum_toW {M : Type} [AddCommGroup M] [Module C M] (g : Fin 2) (u : I g → C) (F : WV I → M) :
    ∑ w, toW g u w • F w = ∑ k, u k • F ⟨g, k⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single g]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [toW]
  · intro g' _ hg'
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp [toW, hg']
  · simp

theorem pderiv_hPullW (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (g : Fin 2)
    (v' : ι' → I g → C) (b : ι') :
    MvPowerSeries.pderiv C (Sum.inr b) (hPullW H e (fun b => toW g (v' b))) =
      ∑ k, v' b k • hPullW (dVar ⟨g, k⟩ H) e (fun b => toW g (v' b)) := by
  have hs := hasSubst_linForm e (fun b => toW g (v' b))
  rw [hPullW_eq, GlobalTheory.FormalCalc.pderiv_subst hs]
  have key : ∀ w : WV I,
      MvPowerSeries.subst (linForm e (fun b => toW g (v' b))) (MvPowerSeries.pderiv C w H) *
          MvPowerSeries.pderiv C (Sum.inr b) (linForm e (fun b => toW g (v' b)) w) =
        toW g (v' b) w • hPullW (dVar w H) e (fun b => toW g (v' b)) := by
    intro w
    rw [pderiv_linForm, hPullW_eq, dVar_eq, MvPowerSeries.smul_eq_C_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  exact sum_toW g (v' b) (fun w => hPullW (dVar w H) e (fun b => toW g (v' b)))

theorem constantCoeff_upG (g : Fin 2) {F : MvPowerSeries (I g) C}
    (hF : MvPowerSeries.constantCoeff F = 0) : MvPowerSeries.constantCoeff (upG g F) = 0 := by
  unfold upG
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _))
    (fun _ => MvPowerSeries.constantCoeff_X _), hF, map_zero]

variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

theorem hPullW_toLeaf (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d)
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b k, (G (1 - g)).ty (Sum.inl k) ≠ a' → v' b k = 0) (F : MvPowerSeries (WV I) C) :
    hPullW (toLeaf G g a a' F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
      hPullW F (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  rw [hPullW_eq, hPullW_eq]
  apply GlobalTheory.subst_eq_of_coeff_eq_of_killed C (WV I) (ι ⊕ ι') (OnLeafV G g a a')
  · exact constantCoeff_linForm _ _
  · rintro ⟨w1, w2⟩ hw
    have h1 : ∀ c, toW g (e c) ⟨w1, w2⟩ = 0 := by
      intro c
      by_cases h : w1 = g
      · subst h
        simp only [toW]
        exact he c w2 (fun hty => hw (Or.inl ⟨rfl, hty⟩))
      · simp [toW, h]
    have h2 : ∀ b, toW (1 - g) (v' b) ⟨w1, w2⟩ = 0 := by
      intro b
      by_cases h : w1 = 1 - g
      · subst h
        simp only [toW]
        exact hv b w2 (fun hty => hw (Or.inr ⟨rfl, hty⟩))
      · simp [toW, h]
    simp [linForm, h1, h2]
  · intro μ hμ
    rw [show MvPowerSeries.coeff μ (toLeaf G g a a' F) = toLeaf G g a a' F μ from rfl]
    unfold toLeaf
    exact if_pos hμ

theorem odd_val_sub {d : ℕ} [NeZero d] (a : ZMod d) {i : ℕ} (hi : Odd i) (hid : i < d) :
    Odd (a + (i : ZMod d) - a).val := by
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hid]
  exact hi

private theorem hPullW_add (H H' : MvPowerSeries (WV I) C) (e : ι → WV I → C)
    (e' : ι' → WV I → C) :
    hPullW (H + H') e e' = hPullW H e e' + hPullW H' e e' := by
  rw [hPullW_eq, hPullW_eq, hPullW_eq, MvPowerSeries.subst_add (hasSubst_linForm e e')]

private theorem hPullW_sum_smul {κ : Type} [Fintype κ] (c : κ → C) (F : κ → MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW (∑ q, c q • F q) e e' = ∑ q, c q • hPullW (F q) e e' := by
  simp only [hPullW_eq]
  rw [GlobalTheory.FormalCalc.subst_sum' (hasSubst_linForm e e')]
  simp only [MvPowerSeries.subst_smul (hasSubst_linForm e e')]

theorem pderiv_hM : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv C (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  intro C _ V d _ I J _ _ X hAlt g a i hi hid S t ht ι ι' _ _ e v' he hvint hv b
  have hΦ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_upG w.1 ((ht w.1).1 w.2))
  have hLs := hasSubst_linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))
  have hK : ∀ k : I (1 - g), ∃ γ : MvPowerSeries (WV I) C,
      (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧
      v' b k • hPullW (dVar (⟨1 - g, k⟩ : WV I) (X.hL g a (a + (i : ZMod d))))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
        v' b k • hPullW (∑ κ : J g, X.pair g κ k • upG g ((S g).ze (t g) κ))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) +
        v' b k • hPullW (MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) γ)
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
    intro k
    by_cases hk : (X.G (1 - g)).ty (Sum.inl k) = a + (i : ZMod d)
    · obtain ⟨K, ⟨γ, hγ, rfl⟩, hEq⟩ :=
        X.C_eq hAlt g a (a + (i : ZMod d)) (odd_val_sub a hi hid) S t ht k hk
      refine ⟨γ, hγ, ?_⟩
      rw [sub_eq_iff_eq_add'] at hEq
      rw [hEq, hPullW_add, hPullW_toLeaf X.G g a _ e v' he hv,
        hPullW_toLeaf X.G g a _ e v' he hv, smul_add]
    · refine ⟨0, fun μ => ?_, ?_⟩
      · rw [map_zero]
        exact VF.Ge.zero 0
      · rw [hv b k hk]
        simp only [zero_smul, add_zero]
  choose γ hγint hγeq using hK
  refine ⟨∑ k, v' b k • γ k, ?_, ?_⟩
  · intro μ
    rw [map_sum]
    refine VF.Ge.sum (fun k _ => ?_)
    simp only [map_smul, smul_eq_mul]
    exact VF.Ge.mul_int (hvint b k) (hγint k μ)
  · unfold RowData.hM
    rw [pderiv_hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (1 - g) v' b,
      Finset.sum_congr rfl (fun k _ => hγeq k), Finset.sum_add_distrib]
    refine (add_comm _ _).trans ?_
    congr 1
    · simp only [hPullW_eq]
      have hΨ : MvPowerSeries.HasSubst (fun w : WV I =>
          MvPowerSeries.subst (linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)))
            (upG w.1 (t w.1 w.2))) := by
        have h := hΦ.comp hLs
        simp only [MvPowerSeries.substAlgHom_apply] at h
        exact h
      rw [GlobalTheory.FormalCalc.subst_sum' hΨ]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MvPowerSeries.subst_smul hΨ, MvPowerSeries.subst_comp_subst_apply hΦ hLs]
    · simp only [hPullW_sum_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_comm]

end GlobalTheory.GaugeDeriv
