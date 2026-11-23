import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEEnergy
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

theorem lemmaEEnergy_step {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (u : Fin (n + 1) → X → ℝ) (w : X → ℝ)
    (hu : ∀ i, A.Smooth (u i)) (hpsh : ∀ i, IsPsh A (potForm Om.pot (u i))) (j : Fin (n + 1))
    (hj : ∀ x, -1 ≤ u j x ∧ u j x ≤ 0) (hw : A.Smooth w) (hwp : IsPsh A (potForm Om.pot w)) :
    mInt A (fun i => potForm Om.pot (u i)) (fun x => -w x) ≤
      mInt A (fun i => potForm Om.pot (Function.update u j 0 i)) (fun x => -w x) + Om.vol := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j with hσdef
  have hσ : ∀ i : Fin n, σ i.succ ≠ j := by
    intro i h
    have h' : σ (σ i.succ) = σ j := congrArg σ h
    rw [Equiv.swap_apply_self, hσdef, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'
  let d : EnergyStep.Data A Om :=
    { w := w, v := u j, f := fun i => u (σ i.succ), M := 1, w_smooth := hw, w_psh := hwp,
      v_smooth := hu j, v_nonpos := fun x => (hj x).2, le_v := fun x => (hj x).1,
      f_smooth := fun _ => hu _, f_psh := fun _ => hpsh _ }
  have h := EnergyStep.proof A Om d
  rw [← mIntSymm A _ σ, ← mIntSymm A (fun i => potForm Om.pot (Function.update u j 0 i)) σ]
  have e1 : mInt A ((fun i => potForm Om.pot (u i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [σ, d, potForm]
    · simp [d, EnergyStep.Data.T, potForm]
  have e2 : mInt A ((fun i => potForm Om.pot (Function.update u j 0 i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons Om.pot d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      simp [σ, potForm, locPot_add_φ, LocPot.ofFun]
    · simp [d, EnergyStep.Data.T, potForm, Function.update_of_ne (hσ i)]
  rw [e1, e2]
  simpa [d] using h

theorem LemmaEEnergy.proof : LemmaEEnergy.Statement := by
  intro D X _ _ _ A Om v w hv hpsh hb hw hwp
  cases D with
  | zero =>
    have e : (fun i : Fin 0 => potForm Om.pot (v i)) = fun _ => Om.pot := funext fun i => i.elim0
    simp [e]
  | succ n =>
    let u : ℕ → Fin (n + 1) → X → ℝ := fun k i => if (i : ℕ) < k then v i else 0
    have hu : ∀ k i, A.Smooth (u k i) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hv i, st_smooth_const A 0]
    have hup : ∀ k i, IsPsh A (potForm Om.pot (u k i)) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hpsh i, isPsh_add_const Om.isPsh 0]
    have key : ∀ k ≤ n + 1, mInt A (fun i => potForm Om.pot (u k i)) (fun x => -w x) ≤
        mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) + k * Om.vol := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hupd : Function.update (u (k + 1)) ⟨k, hk⟩ 0 = u k := by
          funext i
          by_cases h : i = ⟨k, hk⟩
          · subst h; simp [u]
          · rw [Function.update_of_ne h]
            have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
            by_cases hlt : (i : ℕ) < k
            · simp [u, hlt, Nat.lt_succ_of_lt hlt]
            · have : ¬ (i : ℕ) < k + 1 := by omega
              simp [u, hlt, this]
        have step := lemmaEEnergy_step A Om (u (k + 1)) w (hu _) (hup _) ⟨k, hk⟩
          (fun x => by simpa [u] using hb ⟨k, hk⟩ x) hw hwp
        rw [hupd] at step
        have := ih (by omega)
        push_cast
        linarith
    have h1 := key (n + 1) le_rfl
    have e1 : (fun i => potForm Om.pot (u (n + 1) i)) = fun i => potForm Om.pot (v i) :=
      funext fun i => by simp [u, i.isLt]
    have e0 : mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) =
        mInt A (fun _ => Om.pot) (fun x => -w x) := by
      apply st_mInt_congr_phi
      intro i
      funext x y
      simp [u, potForm, locPot_add_φ, LocPot.ofFun]
    rw [e1, e0] at h1
    simpa using h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
