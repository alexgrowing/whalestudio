import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermSumRight

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem colN {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ζ * X)).re = 0) (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0 := by
  have orth : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) →
      herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) v = 0 := by
    intro v hv
    refine herm_zero_of_trace hζ _ v (hN _ (xuv_lieN z a v hv)) (hN _ (xuv_lieN z a _ ?_))
    intro b hb; simp [hv b hb]
  intro i hi
  by_cases h1 : i.val < r
  · have e := herm_es (ζ *ᵥ bvec (eI k r a)) ⟨i.val, h1⟩
    rw [show eI k r ⟨i.val, h1⟩ = i from Fin.ext rfl] at e
    rw [← e]
    refine orth _ (fun b hb => ?_)
    have : esI k r b ≠ esI k r ⟨i.val, h1⟩ := by
      intro h; have := congrArg Fin.val h; simp [esI] at this; omega
    simp [bvec, this]
  · by_cases h2 : i.val ≤ r + k
    · have hw := herm_w (ζ *ᵥ bvec (eI k r a)) i (by omega) h2
      have h0 : herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) (bvec i) = 0 := by
        refine orth _ (fun b hb => ?_)
        have : esI k r b ≠ i := by
          intro h; have := congrArg Fin.val h; simp [esI] at this; omega
        simp [bvec, this]
      rw [hw] at h0
      split_ifs at h0 with h3
      · exact neg_eq_zero.1 h0
      · exact h0
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by
        apply Fin.ext; simp [esI]; omega
      have e2 := herm_e (ζ *ᵥ bvec (eI k r a)) ⟨2 * r + k - i.val, by omega⟩
      rw [← e] at e2
      rw [← e2]
      refine orth _ (fun b hb => ?_)
      have : esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp [esI, eI] at this; omega
      simp [bvec, this]

theorem flt_bvec (a : ℕ) (c : Fin r) (hc : c.val < a) : Flt (k := k) a (bvec (eI k r c)) := by
  intro i hi
  have : i ≠ eI k r c := by intro h; rw [h] at hi; simp [eI] at hi; omega
  simp [bvec, this]

theorem flt_zero_eq (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt 0 y) : y = 0 := by
  funext i; exact hy i (Nat.zero_le _)

theorem stepNil (ζ : B.Mat k r) (N : ℕ) (hζN : ζ ^ N = 0) (a : Fin r)
    (hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0)
    (hkill : ∀ y, Flt a.val y → ζ *ᵥ y = 0) : Flt a.val (ζ *ᵥ bvec (eI k r a)) := by
  set ea := bvec (eI k r a) with hea
  set x := ζ *ᵥ ea with hx
  set xa := x (eI k r a)
  have hea1 : ea (eI k r a) = 1 := by simp [hea, bvec]
  have hy : Flt a.val (x - xa • ea) := by
    intro i hi
    by_cases he : i = eI k r a
    · rw [he]; simp only [Pi.sub_apply, Pi.smul_apply, hea1, smul_eq_mul, mul_one]; exact sub_self _
    · have hi' : a.val < i.val := by
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
      simp [hcol i hi', hea, bvec, he]
  have hζx : ζ *ᵥ x = xa • x := by
    have e : x = xa • ea + (x - xa • ea) := by abel
    conv_lhs => rw [e]
    rw [mulVec_add, mulVec_smul, hkill _ hy, add_zero]
  have hp : ∀ m, (ζ ^ (m + 1)) *ᵥ ea = xa ^ m • x := by
    intro m
    induction m with
    | zero => simp [hx]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hζx, smul_smul, pow_succ]
  have hxa : xa = 0 := by
    cases N with
    | zero =>
      exfalso
      have := congrFun (congrArg (fun M => M *ᵥ ea) hζN) (eI k r a)
      simp [hea1] at this
    | succ m =>
      have := congrFun (hp m) (eI k r a)
      rw [hζN, zero_mulVec] at this
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      have h2 : xa ^ (m + 1) = 0 := by rw [pow_succ]; exact this.symm
      exact (pow_eq_zero_iff'.1 h2).1
  have : x = x - xa • ea := by rw [hxa, zero_smul, sub_zero]
  rw [this]; exact hy

theorem killX (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0)
    (ξ η : B.Mat k r) (hξ : B.inLie k r ξ) (N : ℕ) (hξN : ξ ^ N = 0) (hηN : η ^ N = 0)
    (hgη : g * η = ξ * g)
    (colξ : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ξ *ᵥ bvec (eI k r a)) i = 0)
    (colη : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (η *ᵥ bvec (eI k r a)) i = 0) :
    ∀ a, a ≤ r → ∀ y, Flt a y → ξ *ᵥ y = 0 ∧ η *ᵥ y = 0 := by
  have hξg : ∀ y, ξ *ᵥ (g *ᵥ y) = g *ᵥ (η *ᵥ y) := by
    intro y; rw [mulVec_mulVec, mulVec_mulVec, hgη]
  intro a
  induction a with
  | zero =>
    intro _ y hy
    rw [flt_zero_eq y hy, mulVec_zero, mulVec_zero]
    exact ⟨rfl, rfl⟩
  | succ a ih =>
    intro ha y hy
    have IH := ih (by omega)
    set a' : Fin r := ⟨a, by omega⟩
    have hxξ : Flt a (ξ *ᵥ bvec (eI k r a')) := stepNil ξ N hξN a' (colξ a') (fun y hy => (IH y hy).1)
    have hxη : Flt a (η *ᵥ bvec (eI k r a')) := stepNil η N hηN a' (colη a') (fun y hy => (IH y hy).2)
    have hξa : ξ *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_ii z z' g a (by omega) (hD a (by omega)) _ hxξ (fun c hc => ?_)
      rw [herm_skew hξ, hξg, (IH _ (flt_bvec a c hc)).2, mulVec_zero, herm_zero_right, neg_zero]
    have hηa : η *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_i z z' g a (by omega) (hD a (by omega)) _ hxη (fun c hc => ?_)
      rw [← hξg, herm_skew hξ, (IH _ (flt_bvec a c hc)).1, herm_zero_right, neg_zero]
    set ya := y (eI k r a')
    have hrest : Flt a (y - ya • bvec (eI k r a')) := by
      intro i hi
      by_cases he : i = eI k r a'
      · rw [he]; simp [bvec, ya]
      · have hi' : a + 1 ≤ i.val := by
          have : i.val ≠ a := fun h => he (Fin.ext h)
          omega
        simp [hy i hi', bvec, he]
    have e : y = ya • bvec (eI k r a') + (y - ya • bvec (eI k r a')) := by abel
    rw [e, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hξa, hηa, (IH _ hrest).1, (IH _ hrest).2]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
