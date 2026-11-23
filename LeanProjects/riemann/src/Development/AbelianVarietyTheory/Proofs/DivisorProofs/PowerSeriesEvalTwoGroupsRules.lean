import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.SubstCalc

variable {R : Type} [CommRing R]

theorem constantCoeff_subst_of_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem hasSubst_elim {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {d : ℕ} {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_rules_alt : ∀ (R : Type) [CommRing R] (d : ℕ) (τ τ' : Type) [Finite τ] (u v : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ f, at2 (inL f) u v = subst u f) ∧ (∀ f, at2 (inR f) u v = subst v f) ∧ (∀ c c', at2 (c + c') u v = at2 c u v + at2 c' u v ∧ at2 (c - c') u v = at2 c u v - at2 c' u v) ∧ (∀ c, constantCoeff (at2 c u v) = constantCoeff c) ∧ (∀ c, at2 (swap c) u v = at2 c v u) ∧ (∀ (e : ℕ) (μ : Fin e → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin e) R, at2 (subst μ f) u v = subst (fun i => at2 (μ i) u v) f) ∧ (∀ a : τ → MvPowerSeries τ' R, (∀ t, constantCoeff (a t) = 0) → ∀ c, subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, cob2 (addLaw R d) c = 0 → at2 c u v - at2 c (u + u) v + at2 c u (u + v) - at2 c u u = 0 := by
  intro R _ d τ τ' _ u v hu hv
  have hs := hasSubst_elim hu hv
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold at2 inL
    rw [subst_comp_subst_apply hX hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro f
    unfold at2 inR
    rw [subst_comp_subst_apply hY hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro c c'
    unfold at2
    exact ⟨subst_add hs _ _, subst_sub hs _ _⟩
  · intro c
    unfold at2
    exact constantCoeff_subst_of_zero (fun s => by cases s <;> simp [hu, hv]) c
  · intro c
    have hW : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inl i))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp
    unfold swap at2
    rw [subst_comp_subst_apply hW hs]
    congr 1
    funext s
    cases s <;> simp [subst_X hs]
  · intro e μ hμ f
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hs]
  · intro a ha c
    exact subst_powerSeriesEvalTwoGroups hu hv ha c
  · intro c hc
    set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim u v) with hw
    have hw0 : ∀ t, constantCoeff (w t) = 0 := fun t => by
      rcases t with t | t | t <;> simp [hw, hu, hv]
    have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
    have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
      unfold x1; rw [subst_X hsw]; rfl
    have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = u i := fun i => by
      unfold x2; rw [subst_X hsw]; rfl
    have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = v i := fun i => by
      unfold x3; rw [subst_X hsw]; rfl
    have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        op (addLaw R d) a b = a + b := by
      intro a b ha hb
      funext i
      unfold op addLaw at2
      have := hasSubst_elim ha hb
      rw [subst_add this, subst_X this, subst_X this]
      rfl
    have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        ∀ i, constantCoeff ((a + b) i) = 0 := by
      intro a b ha hb i; simp [ha, hb]
    have key := congrArg (subst w) hc
    unfold cob2 at key
    rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
    rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
      subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
      subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
    have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
      intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
    rw [e, e] at key
    simp only [h1, h2, h3] at key
    have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
      simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
    rw [e0] at key
    convert key using 2

end GlobalTheory.Katz.SubstCalc
