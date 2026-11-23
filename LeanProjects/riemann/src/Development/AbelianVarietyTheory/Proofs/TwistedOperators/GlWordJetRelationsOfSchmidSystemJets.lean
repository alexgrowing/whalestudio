import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicLeftInvariantDerivativeCalculusNearOnStatement

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.FunRel

variable {n : ℕ} (ε : Fin n → Bool) {B B' : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup B'] [NormedSpace ℂ B']

theorem Rw_cons (p : Fin n × Fin n) (l : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ → B) :
    Rw ε (p :: l) g = Rz (thE ε p) (Rw ε l g) := rfl

theorem Rw_append (l₁ l₂ : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ → B) :
    Rw ε (l₁ ++ l₂) g = Rw ε l₁ (Rw ε l₂ g) := by
  unfold Rw
  exact List.foldr_append ..

theorem Rz_congr (Z : Matrix (Fin n) (Fin n) ℂ) {g g' : Matrix (Fin n) (Fin n) ℂ → B}
    (h : g =ᶠ[𝓝 1] g') : Rz Z g =ᶠ[𝓝 1] Rz Z g' := by
  filter_upwards [h.eventuallyEq_nhds] with z hz
  simp only [Rz, hz.fderiv_eq]

theorem Rw_congr (l : List (Fin n × Fin n)) {g g' : Matrix (Fin n) (Fin n) ℂ → B}
    (h : g =ᶠ[𝓝 1] g') : Rw ε l g =ᶠ[𝓝 1] Rw ε l g' := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    rw [Rw_cons, Rw_cons]
    exact Rz_congr _ ih

theorem Rw_zero (l : List (Fin n × Fin n)) :
    Rw ε l (fun _ => (0 : B)) = fun _ => 0 := by
  induction l with
  | nil => simp [Rw]
  | cons p l ih =>
    rw [Rw_cons, ih]
    funext z
    simp [Rz]

theorem Rw_analytic [CompleteSpace B] (l : List (Fin n × Fin n)) {g : Matrix (Fin n) (Fin n) ℂ → B}
    (h : AnalyticAt ℂ g 1) : AnalyticAt ℂ (Rw ε l g) 1 := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    rw [Rw_cons]
    exact (GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one n B (Rw ε l g) ih).1 (thE ε p)

private lemma rz_sum_clm_eventuallyEq_of_analyticAt [CompleteSpace B] {ι : Type} [Fintype ι] (L : ι → B →L[ℂ] B')
    (Z : Matrix (Fin n) (Fin n) ℂ) {k : ι → Matrix (Fin n) (Fin n) ℂ → B} (hk : ∀ i, AnalyticAt ℂ (k i) 1) :
    Rz Z (fun z => ∑ i, L i (k i z)) =ᶠ[𝓝 1] fun z => ∑ i, L i (Rz Z (k i) z) := by
  have hd : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∀ i, DifferentiableAt ℂ (k i) z :=
    Filter.eventually_all.2 fun i => (hk i).eventually_analyticAt.mono fun z hz => hz.differentiableAt
  filter_upwards [hd] with z hz
  have hF : HasFDerivAt (fun w => ∑ i, L i (k i w)) (∑ i, (L i).comp (fderiv ℂ (k i) z)) z := by
    refine (HasFDerivAt.sum (u := Finset.univ) (A := fun i => (L i) ∘ k i)
      fun i _ => (L i).hasFDerivAt.comp z (hz i).hasFDerivAt).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun w => by simp [Finset.sum_apply]
  simp only [Rz, hF.fderiv, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply]

theorem Rw_sum [CompleteSpace B] {ι : Type} [Fintype ι] (L : ι → B →L[ℂ] B') (l : List (Fin n × Fin n))
    {g : ι → Matrix (Fin n) (Fin n) ℂ → B} (h : ∀ i, AnalyticAt ℂ (g i) 1) :
    Rw ε l (fun z => ∑ i, L i (g i z)) =ᶠ[𝓝 1] fun z => ∑ i, L i (Rw ε l (g i) z) := by
  induction l with
  | nil => exact Filter.EventuallyEq.rfl
  | cons p l ih =>
    simp only [Rw_cons]
    exact (Rz_congr _ ih).trans (rz_sum_clm_eventuallyEq_of_analyticAt L _ fun i => Rw_analytic ε l (h i))

theorem Rw_clm [CompleteSpace B] (L : B →L[ℂ] B') (l : List (Fin n × Fin n))
    {g : Matrix (Fin n) (Fin n) ℂ → B} (h : AnalyticAt ℂ g 1) :
    Rw ε l (fun z => L (g z)) =ᶠ[𝓝 1] fun z => L (Rw ε l g z) := by
  have hs := Rw_sum ε (fun _ : Unit => L) l (g := fun _ => g) fun _ => h
  simpa using hs

private lemma rz_sub_eventuallyEq_of_analyticAt [CompleteSpace B] (Z : Matrix (Fin n) (Fin n) ℂ)
    {k k' : Matrix (Fin n) (Fin n) ℂ → B} (hk : AnalyticAt ℂ k 1) (hk' : AnalyticAt ℂ k' 1) :
    Rz Z (fun z => k z - k' z) =ᶠ[𝓝 1] fun z => Rz Z k z - Rz Z k' z := by
  filter_upwards [hk.eventually_analyticAt, hk'.eventually_analyticAt] with z h₁ h₂
  have hF : HasFDerivAt (fun w => k w - k' w) (fderiv ℂ k z - fderiv ℂ k' z) z :=
    h₁.differentiableAt.hasFDerivAt.sub h₂.differentiableAt.hasFDerivAt
  simp only [Rz, hF.fderiv, _root_.sub_apply]

theorem Rw_sub [CompleteSpace B] (l : List (Fin n × Fin n))
    {g g' : Matrix (Fin n) (Fin n) ℂ → B} (h : AnalyticAt ℂ g 1) (h' : AnalyticAt ℂ g' 1) :
    Rw ε l (fun z => g z - g' z) =ᶠ[𝓝 1] fun z => Rw ε l g z - Rw ε l g' z := by
  induction l with
  | nil => exact Filter.EventuallyEq.rfl
  | cons p l ih =>
    simp only [Rw_cons]
    exact (Rz_congr _ ih).trans (rz_sub_eventuallyEq_of_analyticAt _ (Rw_analytic ε l h) (Rw_analytic ε l h'))

theorem Rw_left [CompleteSpace B] (Y : Matrix (Fin n) (Fin n) ℂ) (l : List (Fin n × Fin n))
    {g : Matrix (Fin n) (Fin n) ℂ → B} (h : AnalyticAt ℂ g 1) :
    (fun z => fderiv ℂ (Rw ε l g) z (Y * z)) =ᶠ[𝓝 1] Rw ε l (fun z => fderiv ℂ g z (Y * z)) := by
  induction l with
  | nil => exact Filter.EventuallyEq.rfl
  | cons p l ih =>
    simp only [Rw_cons]
    exact ((GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one n B (Rw ε l g) (Rw_analytic ε l h)).2.2 Y (thE ε p)).trans (Rz_congr _ ih)

theorem analytic_left [CompleteSpace B] (Y : Matrix (Fin n) (Fin n) ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ → B} (h : AnalyticAt ℂ g 1) :
    AnalyticAt ℂ (fun z => fderiv ℂ g z (Y * z)) 1 := by
  have hY : AnalyticAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => Y * z) 1 := by
    exact analyticAt_const.mul analyticAt_id
  have hD : AnalyticAt ℂ (fderiv ℂ g) 1 := h.fderiv
  exact AnalyticAt.comp (f := fun z => (Y * z, fderiv ℂ g z)) (x := 1)
    ((ContinuousLinearMap.apply ℂ B : Matrix (Fin n) (Fin n) ℂ →L[ℂ]
      (Matrix (Fin n) (Fin n) ℂ →L[ℂ] B) →L[ℂ] B).analyticAt_bilinear (Y * 1, fderiv ℂ g 1))
    (hY.prod hD)

theorem sgn_mul (a b c : Fin n) : sgn ε a b * sgn ε b c = sgn ε a c := by
  simp only [Formalism.REAL.sgn]
  generalize ε a = x
  generalize ε b = y
  generalize ε c = w
  cases x <;> cases y <;> cases w <;> norm_num

theorem thE_mul (a b c d : Fin n) :
    thE ε (a, b) * thE ε (c, d) = -(if d = a then thE ε (c, b) else 0) := by
  simp only [thE]
  split_ifs with hda
  · subst hda
    have key : ((sgn ε d b : ℝ) : ℂ) * ((sgn ε c d : ℝ) : ℂ) = ((sgn ε c b : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, mul_comm, sgn_mul]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.single_mul_single_same, smul_smul, neg_mul_neg, key,
      mul_one, neg_smul, neg_neg]
  · have hne : a ≠ d := Ne.symm hda
    rw [Matrix.smul_mul, Matrix.mul_smul]
    simp [hne]

private lemma rz_sub_left (X Y : Matrix (Fin n) (Fin n) ℂ)
    (k : Matrix (Fin n) (Fin n) ℂ → B) : Rz (X - Y) k = fun z => Rz X k z - Rz Y k z := by
  funext z
  simp only [Rz, mul_sub, map_sub]

private lemma rw_rz_ite_apply_one [CompleteSpace B] (P : Prop) [Decidable P] (l₁ l₂ : List (Fin n × Fin n))
    (p : Fin n × Fin n) (g : Matrix (Fin n) (Fin n) ℂ → B) :
    Rw ε l₁ (Rz (if P then thE ε p else 0) (Rw ε l₂ g)) 1 =
      if P then Rw ε l₁ (Rz (thE ε p) (Rw ε l₂ g)) 1 else 0 := by
  split_ifs
  · rfl
  · have h0 : Rz (0 : Matrix (Fin n) (Fin n) ℂ) (Rw ε l₂ g) = fun _ => 0 := by
      funext z
      simp [Rz]
    rw [h0, Rw_zero]

theorem Rw_comm [CompleteSpace B] (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ → B} (h : AnalyticAt ℂ g 1) :
    Rw ε (l₁ ++ (a, b) :: (c, d) :: l₂) g 1 - Rw ε (l₁ ++ (c, d) :: (a, b) :: l₂) g 1 =
      (if b = c then Rw ε (l₁ ++ (a, d) :: l₂) g 1 else 0) -
        (if d = a then Rw ε (l₁ ++ (c, b) :: l₂) g 1 else 0) := by
  have T := GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one n B (Rw ε l₂ g) (Rw_analytic ε l₂ h)
  have TA := GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one n B _ (T.1 (thE ε (a, b)))
  have TZ := GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one n B _ (T.1 (thE ε (c, d)))
  have e1 : Rw ε l₁ (Rz (thE ε (a, b)) (Rz (thE ε (c, d)) (Rw ε l₂ g))) 1 -
      Rw ε l₁ (Rz (thE ε (c, d)) (Rz (thE ε (a, b)) (Rw ε l₂ g))) 1 =
      Rw ε l₁ (Rz (thE ε (a, b) * thE ε (c, d) - thE ε (c, d) * thE ε (a, b)) (Rw ε l₂ g)) 1 :=
    (Rw_sub ε l₁ (TZ.1 (thE ε (a, b))) (TA.1 (thE ε (c, d)))).eq_of_nhds.symm.trans
      (Rw_congr ε l₁ (T.2.1 (thE ε (a, b)) (thE ε (c, d)))).eq_of_nhds
  have e2 : Rw ε l₁ (Rz (thE ε (a, b) * thE ε (c, d) - thE ε (c, d) * thE ε (a, b)) (Rw ε l₂ g)) 1 =
      Rw ε l₁ (Rz (if b = c then thE ε (a, d) else 0) (Rw ε l₂ g)) 1 -
        Rw ε l₁ (Rz (if d = a then thE ε (c, b) else 0) (Rw ε l₂ g)) 1 := by
    rw [thE_mul, thE_mul, neg_sub_neg, rz_sub_left]
    exact (Rw_sub ε l₁ (T.1 _) (T.1 _)).eq_of_nhds
  simp only [Rw_append, Rw_cons]
  rw [e1, e2, rw_rz_ite_apply_one, rw_rz_ite_apply_one]

private lemma rw_nil (g : Matrix (Fin n) (Fin n) ℂ → B) : Rw ε [] g = g := by
  simp [Rw]

theorem jetRel_funJet : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → FunEquiv ε E j f → FunSchmid ε E Λ u j f → JetRel ε E Λ u j (funJet ε f) := by
  intro V W _ _ _ _ n ε E _ Λ u j f hf hE hS
  have T := GlobalTheory.T.holomorphicLeftInvariantDerivative_calculus_near_one n _ f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l₁ l₂ a b c d
    have hc := Rw_comm ε l₁ l₂ a b c d hf
    ext y x
    have hcx := congrArg (fun S : W →L[ℂ] W => ⟪y, S x⟫_ℂ) hc
    simp only [_root_.sub_apply, inner_sub_right] at hcx
    split_ifs at hcx ⊢ <;> simpa [funJet_apply] using hcx
  · intro l a b hab y x x' hx
    have hev : (fun z => Rz (thE ε (a, b)) f z x) =ᶠ[𝓝 1] fun z => f z x' :=
      (hE a b hab).mono fun z hz => hz.1 x x' hx
    have e1 := (Rw_clm ε (ContinuousLinearMap.apply ℂ W x) l (T.1 (thE ε (a, b)))).eq_of_nhds
    have e2 := (Rw_clm ε (ContinuousLinearMap.apply ℂ W x') l hf).eq_of_nhds
    have e3 := (Rw_congr ε l hev).eq_of_nhds
    simp only [ContinuousLinearMap.apply_apply] at e1 e2
    rw [funJet_apply, funJet_apply, Rw_append, Rw_cons, rw_nil, ← e1, e3, e2]
  · intro l a b hab y y' x hy
    have hev : (fun z => ⟪y, fderiv ℂ f z (thE ε (a, b) * z) x⟫_ℂ) =ᶠ[𝓝 1] fun z => ⟪y', f z x⟫_ℂ :=
      (hE a b hab).mono fun z hz => hz.2 y y' x hy
    have hL := (Rw_left ε (thE ε (a, b)) l hf).eq_of_nhds
    have e1 := (Rw_clm ε ((innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)) l
      (analytic_left (thE ε (a, b)) hf)).eq_of_nhds
    have e2 := (Rw_clm ε ((innerSL ℂ y').comp (ContinuousLinearMap.apply ℂ W x)) l hf).eq_of_nhds
    have e3 := (Rw_congr ε l hev).eq_of_nhds
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply] at e1 e2
    simp only [mul_one] at hL
    rw [funJet_apply, funJet_apply, Rw_cons]
    show ⟪y, fderiv ℂ (Rw ε l f) 1 (1 * thE ε (a, b)) x⟫_ℂ = _
    rw [one_mul, hL, ← e1, e3, e2]
  · intro l G hG y
    have hs := Rw_sum ε (fun p => (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W (G p))) l
      (g := fun p => Rz (thE ε p) f) fun p => T.1 _
    have h0 : (fun z => ∑ p, ((innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W (G p)))
        (Rz (thE ε p) f z)) =ᶠ[𝓝 1] fun _ => (0 : ℂ) := by
      filter_upwards [hS G hG] with z hz
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply]
      rw [← inner_sum]
      show ⟪y, ∑ p, fderiv ℂ f z (z * thE ε p) (G p)⟫_ℂ = 0
      rw [hz, inner_zero_right]
    have e1 := (hs.symm.trans (Rw_congr ε l h0)).eq_of_nhds
    rw [Rw_zero] at e1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply] at e1
    simp only [funJet_apply, Rw_append, Rw_cons, rw_nil]
    exact e1

end GlobalTheory.SphJet.FunRel
