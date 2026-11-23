import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEScale
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd isPshRsmul maMeasureMono maMeasure_thm mIntegrableCont
  mIntSymm mIntRsmul st_mInt_congr_phi)

theorem isPsh_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P Q : LocPot X} (hP : IsPsh A P) (hU : ∀ x, Q.U x ⊆ P.U x) (hφ : Q.φ = P.φ) : IsPsh A Q := by
  intro x j y hy w
  rw [hφ]
  exact hP x j y ⟨hy.1, hU x hy.2⟩ w

theorem mInt_update_rsmul {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin e) (g : X → ℝ) :
    mInt A (Function.update Φ j ((Φ j).rsmul c)) g = c * mInt A Φ g := by
  obtain _ | n := e
  · exact j.elim0
  set q := Φ ∘ Equiv.swap 0 j with hq
  have h1 : Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j =
      Fin.cons ((q 0).rsmul c) (Fin.tail q) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [hq]
    · have hne : Equiv.swap 0 j i.succ ≠ j := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero _ h
      simp only [Function.comp_apply, Fin.cons_succ, Fin.tail, hq, Function.update_of_ne hne]
  calc mInt A (Function.update Φ j ((Φ j).rsmul c)) g
      = mInt A (Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j) g := (mIntSymm A _ _ g).symm
    _ = mInt A (Fin.cons ((q 0).rsmul c) (Fin.tail q)) g := by rw [h1]
    _ = c * mInt A (Fin.cons (q 0) (Fin.tail q)) g :=
        mIntRsmul A c _ _ (hΦ _) (fun i => hΦ _) g
    _ = c * mInt A Φ g := by rw [Fin.cons_self_tail, hq, mIntSymm]

theorem mInt_rsmul_all {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) :
    mInt A (fun i => (Φ i).rsmul c) g = c ^ e * mInt A Φ g := by
  have key : ∀ k ≤ e, mInt A (fun i : Fin e => if (i : ℕ) < k then (Φ i).rsmul c else Φ i) g =
      c ^ k * mInt A Φ g := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      set Ψ : Fin e → LocPot X := fun i => if (i : ℕ) < k then (Φ i).rsmul c else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := fun i => by
        simp only [hΨ]; split_ifs
        · exact isPotentialRsmul A c _ (hΦ i)
        · exact hΦ i
      have h : (fun i : Fin e => if (i : ℕ) < k + 1 then (Φ i).rsmul c else Φ i) =
          Function.update Ψ ⟨k, hk⟩ ((Ψ ⟨k, hk⟩).rsmul c) := by
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi; simp [hΨ]
        · have hi' : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi, hΨ]
          simp only [Nat.lt_succ_iff_lt_or_eq, hi', or_false]
      rw [h, mInt_update_rsmul A c Ψ hΨp, ih (Nat.le_of_succ_le hk), pow_succ]
      ring
  simpa using key e le_rfl

theorem LemmaEScale.proof : LemmaEScale.Statement := by
  intro D X _ _ _ A Om M v hM hv hpsh
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  have hM0 : M ≠ 0 := by positivity
  have hP : ∀ i, IsPotential A (potForm Om.pot (v i)) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (hv i))
  have hW : ∀ i, IsPotential A (potForm Om.pot fun x => v i x / M) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ fun j => (hv i j).div_const M)
  have hQ := isPotentialRsmul A (M - 1) _ Om.isPot
  have hQpsh := isPshRsmul A (M - 1) _ (by linarith) Om.isPot Om.isPsh
  refine ⟨fun i => ?_, fun g hg hg0 => ?_⟩
  · have h1 := isPshRsmul A M⁻¹ _ (by positivity) (hP i) (hpsh i)
    have h2 := isPshRsmul A (1 - M⁻¹) _ (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hM)
      Om.isPot Om.isPsh
    refine isPsh_of_φ_eq (isPshAdd A _ _ (isPotentialRsmul A _ _ (hP i))
      (isPotentialRsmul A _ _ Om.isPot) h1 h2) (fun x y hy => ⟨hy, hy.1⟩) ?_
    funext x y
    show Om.pot.φ x y + v i y / M = M⁻¹ * (Om.pot.φ x y + v i y) + (1 - M⁻¹) * Om.pot.φ x y
    field_simp
    ring
  have hmono := maMeasureMono A _ (fun _ => Om.pot.rsmul (M - 1)) hP hpsh (fun _ => hQ)
    (fun _ => hQpsh)
  have hS : ∀ i, IsPotential A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPotentialAdd A _ _ (hP i) hQ
  have hSpsh : ∀ i, IsPsh A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPshAdd A _ _ (hP i) hQ (hpsh i) hQpsh
  obtain ⟨_, hT'⟩ := maMeasure_thm A _ hP hpsh
  obtain ⟨_, hS'⟩ := maMeasure_thm A _ hS hSpsh
  have hgm := hg.measurable
  have e1 := (hT' g hgm).2 (mIntegrableCont A _ hP g hg)
  have e2 := (hS' g hgm).2 (mIntegrableCont A _ hS g hg)
  have hint := (hS' g hgm).1.1 (mIntegrableCont A _ hS g hg)
  have hle : mInt A (fun i => potForm Om.pot (v i)) g ≤
      mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g := by
    rw [e1, e2]
    exact integral_mono_measure hmono (Filter.Eventually.of_forall hg0) hint
  have e3 : mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g =
      mInt A (fun i => (potForm Om.pot fun x => v i x / M).rsmul M) g := by
    refine st_mInt_congr_phi A (fun i => ?_) g
    funext x y
    show Om.pot.φ x y + v i y + (M - 1) * Om.pot.φ x y = M * (Om.pot.φ x y + v i y / M)
    field_simp
    ring
  rw [e3, mInt_rsmul_all A M _ hW] at hle
  exact hle

end GroundTheory.Heights₂.Heights.AnalyticLimit
