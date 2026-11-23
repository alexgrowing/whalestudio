import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.HhZero

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

open PrismSpan

variable {P Q : Type} [Group P] [Group Q]

def ColKillP : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ (u : Q), (∀ g, g * u = u * g) → ∀ (q : ℕ) (f : Polynomial ℝ),
    (∀ c : (Fin (q + 2) → P) → ℝ, InvS (pr.ker : Set P) c → dc c = 0 →
      ∃ e : (Fin (q + 1) → P) → ℝ, InvS (pr.ker : Set P) e ∧
        Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f c = dc e) →
    ∀ {a : ℕ} (x : Bi P Q (a + 1) (q + 2)), PInv pr x → dv x = 0 →
      ∃ E : Bi P Q (a + 1) (q + 1), PInv pr E ∧ Polynomial.aeval (TcL (s u) (a + 1) (q + 2)) f x = dv E

section
variable (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g)
include hs hu

theorem ru_tc {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) :
    Ru u z - Tc (s u) z = dv (Tc (s u) (Hv (s u)⁻¹ z)) := by
  have hpz : ∀ (n : ℕ) (y : Fin n → P),
      prism (fun p => p * (s u)⁻¹) (0 : (Fin (n + 1) → P) → ℝ) y = 0 := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [prism_succ]
      have : (fun w : Fin (n + 1) → P => (0 : (Fin (n + 2) → P) → ℝ) (Fin.cons (y 0) w)) = 0 := rfl
      rw [this, ih]
      simp
  rw [ru_eq pr s hs u hu hz]
  funext x y
  have h := prism_dc (fun p => p * (s u)⁻¹) b (z x) (fun j => (s u)⁻¹ * y j * s u)
  have h0 : dc (z x) = 0 := congrFun hdz x
  rw [h0, hpz, add_zero] at h
  simp only [Pi.sub_apply]
  exact h.symm

theorem pow_closed {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) :
    ∀ k : ℕ, PInv pr (((RuL (P := P) u a (b + 2)) ^ k) z) ∧ dv (((RuL (P := P) u a (b + 2)) ^ k) z) = 0 := by
  intro k
  induction k with
  | zero => exact ⟨hz, hdz⟩
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := ih
    generalize ((RuL (P := P) u a (b + 2)) ^ k) z = w at h1 h2
    refine ⟨?_, ?_⟩
    · intro g x y
      change w (fun i => (fun i => pr g * x i) i * u) (fun j => g * y j) = w (fun i => x i * u) y
      simp only [mul_assoc]
      exact h1 g (fun i => x i * u) y
    · funext x y
      exact congrFun (congrFun h2 (fun i => x i * u)) y

theorem pow_diff {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) :
    ∀ k : ℕ, ∃ E : Bi P Q a (b + 1), PInv pr E ∧
      ((RuL (P := P) u a (b + 2)) ^ k) z - ((TcL (s u) a (b + 2)) ^ k) z = dv E := by
  have htr : ∀ (n : ℕ) (G : (Fin (n + 1) → P) → ℝ) (g : P) (y : Fin n → P),
      prism (fun p => p * (s u)⁻¹) G (fun j => g * y j) =
        prism (fun p => p * (s u)⁻¹) (fun v => G (fun j => g * v j)) y := by
    intro n
    induction n with
    | zero => intro G g y; rfl
    | succ n ih =>
      intro G g y
      rw [prism_succ, prism_succ]
      have e1 : (Fin.cons (g * y 0) (fun i => g * y i * (s u)⁻¹) : Fin (n + 2) → P) =
          fun j => g * (Fin.cons (y 0) (fun i => y i * (s u)⁻¹) : Fin (n + 2) → P) j := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [mul_assoc]
      have e2 : ∀ v : Fin (n + 1) → P, (Fin.cons (g * y 0) (fun j => g * v j) : Fin (n + 2) → P) =
          fun j => g * (Fin.cons (y 0) v : Fin (n + 2) → P) j := by
        intro v
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp
      have ih' := ih (fun w => G (Fin.cons (g * y 0) w)) g (Fin.tail y)
      simp only [e2] at ih'
      simp only [e1]
      congr 1
  have hg : ∀ g : P, pr ((s u)⁻¹ * g * s u) = pr g := by
    intro g
    rw [map_mul, map_mul, map_inv, hs, mul_assoc, hu (pr g), ← mul_assoc, inv_mul_cancel, one_mul]
  have hTcP : ∀ {c : ℕ} (F : Bi P Q a c), PInv pr F → PInv pr (Tc (s u) F) := by
    intro c F hF g x y
    have h := hF ((s u)⁻¹ * g * s u) x (fun j => (s u)⁻¹ * y j * s u)
    rw [hg] at h
    change F (fun i => pr g * x i) (fun j => (s u)⁻¹ * (g * y j) * s u) = F x (fun j => (s u)⁻¹ * y j * s u)
    rw [← h]
    congr 1
    funext j
    group
  have hHvP : ∀ {c : ℕ} (F : Bi P Q a (c + 1)), PInv pr F → PInv pr (Hv (s u)⁻¹ F) := by
    intro c F hF g x y
    change prism (fun p => p * (s u)⁻¹) (F (fun i => pr g * x i)) (fun j => g * y j) =
      prism (fun p => p * (s u)⁻¹) (F x) y
    rw [htr]
    congr 1
    funext v
    exact hF g x v
  have hdvadd : ∀ A B : Bi P Q a (b + 1), dv (A + B) = dv A + dv B := by
    intro A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  intro k
  induction k with
  | zero =>
    refine ⟨0, fun g x y => rfl, ?_⟩
    funext x y
    simp [dv, dc]
  | succ k ih =>
    obtain ⟨E, hE, hEq⟩ := ih
    obtain ⟨hw1, hw2⟩ := pow_closed pr s hs u hu hz hdz k
    refine ⟨Tc (s u) (Hv (s u)⁻¹ (((RuL (P := P) u a (b + 2)) ^ k) z)) + Tc (s u) E, ?_, ?_⟩
    · intro g x y
      simp only [Pi.add_apply]
      rw [hTcP _ (hHvP _ hw1) g x y, hTcP _ hE g x y]
    · have h1 := ru_tc pr s hs u hu hw1 hw2
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      generalize ((RuL (P := P) u a (b + 2)) ^ k) z = w at hEq h1 hw1 hw2 ⊢
      generalize ((TcL (s u) a (b + 2)) ^ k) z = T at hEq ⊢
      have hsplit : RuL (P := P) u a (b + 2) w - TcL (s u) a (b + 2) T =
          (RuL (P := P) u a (b + 2) w - TcL (s u) a (b + 2) w) + TcL (s u) a (b + 2) (w - T) := by
        rw [map_sub]
        abel
      rw [hsplit, hEq, hdvadd]
      change (Ru u w - Tc (s u) w) + Tc (s u) (dv E) = _
      rw [h1]
      rfl

theorem aeval_diff {a b : ℕ} {z : Bi P Q a (b + 2)} (hz : PInv pr z) (hdz : dv z = 0) (f : Polynomial ℝ) :
    ∃ E : Bi P Q a (b + 1), PInv pr E ∧
      Polynomial.aeval (RuL (P := P) u a (b + 2)) f z - Polynomial.aeval (TcL (s u) a (b + 2)) f z = dv E := by
  have hdvadd : ∀ A B : Bi P Q a (b + 1), dv (A + B) = dv A + dv B := by
    intro A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  have hdvsmul : ∀ (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A := by
    intro c A
    funext x y
    simp [dv, dc, Finset.mul_sum, mul_left_comm]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨E1, h1, e1⟩ := hp
    obtain ⟨E2, h2, e2⟩ := hq
    refine ⟨E1 + E2, ?_, ?_⟩
    · intro g x y
      simp only [Pi.add_apply]
      rw [h1 g x y, h2 g x y]
    · rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hdvadd, ← e1, ← e2]
      abel
  | monomial n c =>
    obtain ⟨E, hE, e⟩ := pow_diff pr s hs u hu hz hdz n
    refine ⟨c • E, ?_, ?_⟩
    · intro g x y
      simp only [Pi.smul_apply]
      rw [hE g x y]
    · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← smul_sub, e, hdvsmul]

end

theorem e2VanishingFirstColumn_of_colKillP (hK : ColKillP) : E2VanishingFirstColumn := by
  intro P Q _ _ pr s hs u hu m hm q hq w hw hdw hdh
  have hdvadd : ∀ {a b : ℕ} (A B : Bi P Q a (b + 1)), dv (A + B) = dv A + dv B := by
    intro a b A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  have hdvsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A := by
    intro a b c A
    funext x y
    simp [dv, dc, Finset.mul_sum, mul_left_comm]
  obtain ⟨f, hf1, hf⟩ := hm q hq
  obtain ⟨E1, hE1, e1⟩ := hK P Q pr s hs u hu q f hf (a := 0) w hw hdw
  obtain ⟨E2, hE2, e2⟩ := aeval_diff pr s hs u hu hw hdw f
  have hfix : RuL (P := P) u 1 (q + 2) w = w := by
    funext x y
    have hsa : ∀ j : Fin 1, Fin.succAbove (1 : Fin 2) j = 0 := by
      intro j
      fin_cases j
      rfl
    have h := congrFun (congrFun hdh (fun i : Fin 2 => if i = 0 then x 0 * u else x 0)) y
    simp [dh, dc, Fin.sum_univ_two, hsa] at h
    change w (fun i => x i * u) y = w x y
    have hx1 : (fun i : Fin 1 => x i * u) = fun _ => x 0 * u := by
      funext i; rw [Subsingleton.elim i 0]
    have hx2 : x = fun _ => x 0 := by
      funext i; rw [Subsingleton.elim i 0]
    rw [hx1]
    conv_rhs => rw [hx2]
    linarith
  have hev : ∀ g : Polynomial ℝ, Polynomial.aeval (RuL (P := P) u 1 (q + 2)) g w = g.eval 1 • w := by
    intro g
    induction g using Polynomial.induction_on' with
    | add p r hp hr => rw [map_add, LinearMap.add_apply, hp, hr, Polynomial.eval_add, add_smul]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
        Polynomial.eval_monomial, one_pow, mul_one]
      congr 1
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
  rw [hev, e1] at e2
  refine ⟨(f.eval 1)⁻¹ • (E2 + E1), ?_, ?_⟩
  · intro g x y
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [hE1 g x y, hE2 g x y]
  · rw [hdvsmul, hdvadd, ← e2, sub_add_cancel, smul_smul, inv_mul_cancel₀ hf1, one_smul]

theorem e2VanishingOtherColumns_of_colKillP (hK : ColKillP) : E2VanishingOtherColumns := by
  intro P Q _ _ pr s hs u hu m hm p q hq x hx hdx hdh
  have hpz : ∀ (n : ℕ) (y : Fin n → Q), prism (fun v => v * u) (0 : (Fin (n + 1) → Q) → ℝ) y = 0 := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [prism_succ]
      have : (fun w : Fin (n + 1) → Q => (0 : (Fin (n + 2) → Q) → ℝ) (Fin.cons (y 0) w)) = 0 := rfl
      rw [this, ih]
      simp
  have hlin : ∀ (n : ℕ) (k : ℕ) (c : Fin k → ℝ) (F : Fin k → (Fin (n + 1) → Q) → ℝ) (y : Fin n → Q),
      prism (fun v => v * u) (fun w => ∑ i, c i * F i w) y = ∑ i, c i * prism (fun v => v * u) (F i) y := by
    intro n
    induction n with
    | zero =>
      intro k c F y
      change (0 : ℝ) = ∑ i, c i * (0 : ℝ)
      simp
    | succ n ih =>
      intro k c F y
      rw [prism_succ]
      simp only [prism_succ]
      rw [ih k c (fun i w => F i (Fin.cons (y 0) w)) (Fin.tail y), ← Finset.sum_sub_distrib]
      congr 1
      funext i
      ring
  have htr : ∀ (n : ℕ) (G : (Fin (n + 1) → Q) → ℝ) (g : Q) (y : Fin n → Q),
      prism (fun v => v * u) G (fun j => g * y j) =
        prism (fun v => v * u) (fun v => G (fun j => g * v j)) y := by
    intro n
    induction n with
    | zero => intro G g y; rfl
    | succ n ih =>
      intro G g y
      rw [prism_succ, prism_succ]
      have e1 : (Fin.cons (g * y 0) (fun i => g * y i * u) : Fin (n + 2) → Q) =
          fun j => g * (Fin.cons (y 0) (fun i => y i * u) : Fin (n + 2) → Q) j := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [mul_assoc]
      have e2 : ∀ v : Fin (n + 1) → Q, (Fin.cons (g * y 0) (fun j => g * v j) : Fin (n + 2) → Q) =
          fun j => g * (Fin.cons (y 0) v : Fin (n + 2) → Q) j := by
        intro v
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp
      have ih' := ih (fun w => G (Fin.cons (g * y 0) w)) g (Fin.tail y)
      simp only [e2] at ih'
      simp only [e1]
      congr 1
  let H : Bi P Q (p + 1) (q + 2) := fun x' y => prism (fun v => v * u) (fun x'' => x x'' y) x'
  have hA : dh H = Ru u x - x := by
    funext x' y
    have h := prism_dc (fun v => v * u) p (fun x'' => x x'' y) x'
    have h0 : dc (fun x'' => x x'' y) = 0 := by
      funext v
      exact congrFun (congrFun hdh v) y
    rw [h0, hpz, add_zero] at h
    exact h
  have hB : PInv pr H := by
    intro g x' y
    change prism (fun v => v * u) (fun x'' => x x'' (fun j => g * y j)) (fun i => pr g * x' i) =
      prism (fun v => v * u) (fun x'' => x x'' y) x'
    rw [htr]
    congr 1
    funext v
    exact hx g v y
  have hC : dv H = 0 := by
    funext x' y
    change dc (fun y' => prism (fun v => v * u) (fun x'' => x x'' y') x') y = 0
    simp only [dc]
    have := hlin (p + 1) (q + 3) (fun i => (-1) ^ (i : ℕ)) (fun i x'' => x x'' (fun j => y (i.succAbove j))) x'
    rw [← this]
    have h0 : (fun w => ∑ i : Fin (q + 3), (-1 : ℝ) ^ (i : ℕ) * x w (fun j => y (i.succAbove j))) = 0 := by
      funext w
      exact congrFun (congrFun hdx w) y
    rw [h0, hpz]
  have hdvadd : ∀ {a b : ℕ} (A B : Bi P Q a (b + 1)), dv (A + B) = dv A + dv B := by
    intro a b A B
    funext x y
    simp [dv, dc, Finset.sum_add_distrib, mul_add]
  have hdvsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q a (b + 1)), dv (c • A) = c • dv A := by
    intro a b c A
    funext x y
    simp [dv, dc, Finset.mul_sum, mul_left_comm]
  have hdhadd : ∀ {a b : ℕ} (A B : Bi P Q (a + 1) b), dh (A + B) = dh A + dh B := by
    intro a b A B
    funext x y
    simp [dh, dc, Finset.sum_add_distrib, mul_add]
  have hdhsmul : ∀ {a b : ℕ} (c : ℝ) (A : Bi P Q (a + 1) b), dh (c • A) = c • dh A := by
    intro a b c A
    funext x y
    simp [dh, dc, Finset.mul_sum, mul_left_comm]
  have hD : ∀ g : Polynomial ℝ, PInv pr (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) ∧
      dv (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) = 0 := by
    intro g
    induction g using Polynomial.induction_on' with
    | add r t hr ht =>
      refine ⟨?_, ?_⟩
      · intro g' x' y
        rw [map_add, LinearMap.add_apply]
        simp only [Pi.add_apply]
        rw [hr.1 g' x' y, ht.1 g' x' y]
      · rw [map_add, LinearMap.add_apply, hdvadd, hr.2, ht.2, add_zero]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      obtain ⟨h1, h2⟩ := pow_closed pr s hs u hu hB hC n
      refine ⟨?_, ?_⟩
      · intro g' x' y
        simp only [Pi.smul_apply]
        rw [h1 g' x' y]
      · rw [hdvsmul, h2, smul_zero]
  have hE : ∀ (g : Polynomial ℝ) (F : Bi P Q (p + 1) (q + 2)),
      Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) g (dh F) =
        dh (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g F) := by
    intro g F
    induction g using Polynomial.induction_on' with
    | add r t hr ht =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hr, ht, hdhadd]
    | monomial n c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hdhsmul]
      congr 1
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
        rfl
  obtain ⟨f, hf1, hf⟩ := hm q hq
  obtain ⟨E1, hE1, e1⟩ := hK P Q pr s hs u hu q f hf (a := p + 1) x hx hdx
  obtain ⟨E2, hE2, e2⟩ := aeval_diff pr s hs u hu hx hdx f
  have e1' : Polynomial.aeval (TcL (s u) (p + 2) (q + 2)) f x = dv E1 := e1
  have hfx : Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) f x = dv E2 + dv E1 := by
    rw [← e1', ← e2, sub_add_cancel]
  set c := f.eval 1 with hc
  have hroot : (f - Polynomial.C c).IsRoot 1 := by simp [Polynomial.IsRoot, hc]
  have hdiv := (Polynomial.mul_divByMonic_eq_iff_isRoot (a := (1 : ℝ))).mpr hroot
  rw [mul_comm] at hdiv
  set g := (f - Polynomial.C c) /ₘ (Polynomial.X - Polynomial.C 1)
  have hkey : Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) f x - c • x =
      dh (Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H) := by
    have h := congrArg (fun r => Polynomial.aeval (RuL (P := P) u (p + 2) (q + 2)) r x) hdiv
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, map_one, Module.End.one_apply, one_smul] at h
    rw [← h, ← hE, hA, map_sub]
    rfl
  obtain ⟨hG1, hG2⟩ := hD g
  refine ⟨-(c⁻¹) • Polynomial.aeval (RuL (P := P) u (p + 1) (q + 2)) g H, c⁻¹ • (E2 + E1), ?_, ?_, ?_, ?_⟩
  · intro g' x' y
    simp only [Pi.smul_apply]
    rw [hG1 g' x' y]
  · rw [hdvsmul, hG2, smul_zero]
  · intro g' x' y
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [hE1 g' x' y, hE2 g' x' y]
  · rw [hdhsmul, hdvsmul, hdvadd, ← hkey, ← hfx]
    rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hf1, one_smul]
    abel

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
