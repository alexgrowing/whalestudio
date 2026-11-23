import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

section Dual

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem dm_mul (f g : Module.End ℂ V) : (f * g).dualMap = g.dualMap * f.dualMap := by
  ext φ x
  rfl

theorem dm_add (f g : Module.End ℂ V) : (f + g).dualMap = f.dualMap + g.dualMap := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_sub (f g : Module.End ℂ V) : (f - g).dualMap = f.dualMap - g.dualMap := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_zero : (0 : Module.End ℂ V).dualMap = 0 := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_one : (1 : Module.End ℂ V).dualMap = 1 := by
  ext φ x
  rfl

theorem dm_sum {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ V) :
    (∑ i ∈ s, f i).dualMap = ∑ i ∈ s, (f i).dualMap := by
  ext φ x
  simp [LinearMap.dualMap_apply, LinearMap.sum_apply, map_sum]

theorem dm_intCast (z : ℤ) : ((z : Module.End ℂ V)).dualMap = (z : Module.End ℂ (Module.Dual ℂ V)) := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_algebraMap (u : ℂ) :
    (algebraMap ℂ (Module.End ℂ V) u).dualMap = algebraMap ℂ (Module.End ℂ (Module.Dual ℂ V)) u := by
  ext φ x
  simp [LinearMap.dualMap_apply, Module.algebraMap_end_apply]

theorem dm_ofFn_prod : ∀ {t : ℕ} (f : Fin t → Module.End ℂ V),
    ((List.ofFn f).prod).dualMap = (List.ofFn fun i => (f i.rev).dualMap).prod
  | 0, f => by simp [dm_one]
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, dm_mul, dm_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => (f i.rev).dualMap), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

theorem glRel_dualE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) : GlRel (dualE E) := by
  intro a b c d
  simp only [dualE]
  rw [← dm_mul, ← dm_mul, ← dm_sub, hE d c b a, dm_sub]
  split_ifs <;> simp_all [dm_zero]

theorem Tm_dualE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) (a b : Fin n) :
    Tm (dualE E) u a b = (Tm E u b a).dualMap := by
  simp only [Tm, dualE, dm_add]
  congr 1
  by_cases h : a = b
  · subst h; simp [dm_algebraMap]
  · rw [if_neg h, if_neg (Ne.symm h), dm_zero]

theorem arg_rev {t : ℕ} (w : ℂ) (j : Fin t) :
    w - (t : ℂ) + 1 + (((Fin.rev j : Fin t) : ℕ) : ℂ) = w - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring

theorem dm_qminorRow {n t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin t → Fin n) (w : ℂ) :
    (qminorRow E (b ∘ Fin.rev) (a ∘ Fin.rev) w).dualMap = qminor (dualE E) a b w := by
  unfold qminor qminorRow
  rw [dm_sum]
  refine Fintype.sum_equiv (PI.UnitaryGroupMassFormula.QmStar.conjRev t) _ _ (fun σ => ?_)
  rw [dm_mul, dm_intCast, dm_ofFn_prod, PI.UnitaryGroupMassFormula.QmStar.sign_conjRev, Int.cast_comm]
  simp only [Function.comp_apply, PI.UnitaryGroupMassFormula.QmStar.conjRev_apply, Fin.rev_rev, arg_rev, Tm_dualE]

end Dual

section Weight

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_prod (H : Module.End ℂ V) : ∀ {n : ℕ} (g : Fin n → Module.End ℂ V) (e : Fin n → ℂ),
    (∀ x, H * g x = g x * H + e x • g x) →
    H * (List.ofFn g).prod = (List.ofFn g).prod * H + (∑ x, e x) • (List.ofFn g).prod
  | 0, g, e, _ => by simp
  | n + 1, g, e, h => by
    have ih := comm_prod H (fun x => g x.succ) (fun x => e x.succ) (fun x => h x.succ)
    rw [List.ofFn_succ, List.prod_cons, ← mul_assoc, h 0, add_mul, mul_assoc, ih, Fin.sum_univ_succ, mul_add,
      add_smul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

theorem comm_pow (H f : Module.End ℂ V) (d : ℂ) (h : H * f = f * H + d • f) (k : ℕ) :
    H * f ^ k = f ^ k * H + ((k : ℂ) * d) • f ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc, h]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, Nat.cast_succ, add_smul, one_mul]
    abel

theorem comm_mono (H : Module.End ℂ V) {n : ℕ} (f : Fin n → Module.End ℂ V) (d : Fin n → ℂ)
    (h : ∀ x, H * f x = f x * H + d x • f x) (a : Fin n → ℕ) :
    H * mono f a = mono f a * H + (∑ x, (a x : ℂ) * d x) • mono f a := by
  unfold mono
  exact comm_prod H (fun x => f x ^ a x) (fun x => (a x : ℂ) * d x) (fun x => comm_pow H (f x) (d x) (h x) (a x))

theorem weight_mono {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hE : GlRel E) (c : Fin n) (m : ℂ)
    (w : V) (hw : E c.castSucc c.castSucc w = m • w) (a : Fin n → ℕ) :
    E c.castSucc c.castSucc (mono (etaK E) a w) = (m + (a c : ℂ)) • mono (etaK E) a w := by
  have hd : ∀ x, E c.castSucc c.castSucc * etaK E x =
      etaK E x * E c.castSucc c.castSucc + (if x = c then (1 : ℂ) else 0) • etaK E x := by
    intro x
    have h := hE c.castSucc c.castSucc x.castSucc (Fin.last n)
    rw [if_neg (Fin.castSucc_lt_last c).ne', sub_zero] at h
    by_cases hx : x = c
    · subst hx
      rw [if_pos rfl] at h
      rw [if_pos rfl, one_smul]
      exact eq_add_of_sub_eq' h
    · rw [if_neg (fun e => hx (Fin.castSucc_injective _ e).symm)] at h
      rw [if_neg hx, zero_smul, add_zero]
      exact sub_eq_zero.mp h
  have hc := congrArg (fun g : Module.End ℂ V => g w) (comm_mono _ (etaK E) _ hd a)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hw, map_smul] at hc
  rw [hc, add_smul]
  congr 2
  simp

end Weight

end Formalism.FourierDecayAlt.P.DegreeMapArithmetic

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr DegreeMapArithmetic

theorem dual_minor : Qr.DualMinor := by
  intro V _ _ n E hE
  refine ⟨glRel_dualE E hE, fun t a b w => ?_⟩
  rw [← dm_qminorRow, ← line_form_of_minor _ n t E hE, PI.UnitaryGroupMassFormula.QmStar.qminor_rev_rev E hE]

theorem qr_multOne_of (hS : Qr.ExistsSingMax) (hD : Qr.DualMinor) (hP : Qr.SpanSing) : Qr.MultOne := by
  intro V _ _ _ n E μ w₁ w₂ hE hIrr h1 h2 hw1
  have : Nontrivial V := hIrr.1
  obtain ⟨ν, ξ₀, -, hξ0, hHW, -⟩ := hS (Module.Dual ℂ V) (n + 1) (dualE E) (hD V (n + 1) E hE).1 ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hdiag : ∀ (a : Fin (n + 1)) (v : V), ξ₀ (E a a v) = ν a * ξ₀ v := by
    intro a v
    have := congrArg (fun ζ : Module.Dual ℂ V => ζ v) (hHW.1 a)
    simpa [dualE, LinearMap.dualMap_apply] using this
  have hlow : ∀ a b : Fin (n + 1), b < a → ∀ v, ξ₀ (E a b v) = 0 := by
    intro a b hab v
    have := congrArg (fun ζ : Module.Dual ℂ V => ζ v) (hHW.2 b a hab)
    simpa [dualE, LinearMap.dualMap_apply] using this
  have key : ∀ w, IsHW (subA E) μ w → ∀ a : Fin n → ℕ, ξ₀ (mono (etaK E) a w) ≠ 0 →
      ∀ c, (a c : ℂ) = ν c.castSucc - μ c := by
    intro w hw a ha c
    have e1 := hdiag c.castSucc (mono (etaK E) a w)
    rw [weight_mono E hE c (μ c) w (hw.1 c) a, map_smul, smul_eq_mul] at e1
    have := mul_right_cancel₀ ha e1
    rw [← this]; ring
  have hex : ∃ a₀ : Fin n → ℕ, ξ₀ (mono (etaK E) a₀ w₁) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw1 (hP V n E ξ₀ μ w₁ hE hIrr hξ0 hlow h1 hcon)
  obtain ⟨a₀, ha₀⟩ := hex
  refine ⟨ξ₀ (mono (etaK E) a₀ w₂) / ξ₀ (mono (etaK E) a₀ w₁), ?_⟩
  set c := ξ₀ (mono (etaK E) a₀ w₂) / ξ₀ (mono (etaK E) a₀ w₁) with hc
  have hw : IsHW (subA E) μ (w₂ - c • w₁) := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · rw [map_sub, map_smul, h1.1 a, h2.1 a, smul_sub, smul_comm]
    · rw [map_sub, map_smul, h1.2 a b hab, h2.2 a b hab, smul_zero, sub_zero]
  have hz : w₂ - c • w₁ = 0 := by
    refine hP V n E ξ₀ μ _ hE hIrr hξ0 hlow hw (fun a => ?_)
    by_contra hne
    have haa : a = a₀ := by
      funext x
      have e1 := key _ hw a hne x
      have e2 := key _ h1 a₀ ha₀ x
      exact Nat.cast_injective (R := ℂ) (e1.trans e2.symm)
    subst haa
    apply hne
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ ha₀, sub_self]
  exact sub_eq_zero.mp hz

end Formalism.FourierDecayAlt.P
