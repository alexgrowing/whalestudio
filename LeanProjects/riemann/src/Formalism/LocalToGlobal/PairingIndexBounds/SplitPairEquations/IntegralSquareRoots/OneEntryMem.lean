import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ZeroInjectionMemFourthPower

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Ker

section Gen

variable {n : Type} [Fintype n] [DecidableEq n] {N N' : ℕ}

def ent (k : Fin N' × Fin N) (z : n → Fin N' → Fin N → ℂ) : n → ℂ := fun τ => z τ k.1 k.2

def setE (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w : n → ℂ) : n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) = k then w τ else z τ i j

def repl (a : n → ℂ) (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ) : n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) ∈ s then a τ else z τ i j

omit [Fintype n] [DecidableEq n] in
theorem ent_putL (k p : Fin N' × Fin N) (x : n → ℂ) : ent p (putL n N N' k x) = if p = k then x else 0 := by
  funext τ
  by_cases h : p = k <;> simp [ent, putL, h]

omit [Fintype n] [DecidableEq n] in
theorem ent_setE (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w : n → ℂ) : ent k (setE z k w) = w := by
  funext τ
  simp [ent, setE]

omit [Fintype n] [DecidableEq n] in
theorem setE_ent (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) : setE z k (ent k z) = z := by
  funext τ i j
  by_cases h : (i, j) = k
  · subst h; simp [ent, setE]
  · simp [setE, h]

omit [Fintype n] [DecidableEq n] in
theorem setE_add (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (w x : n → ℂ) :
    setE z k w + putL n N N' k x = setE z k (w + x) := by
  funext τ i j
  by_cases h : (i, j) = k <;> simp [setE, putL, h]

theorem form_put (L : PeriodPair) (y : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) (x : n → ℂ) :
    formV (Formalism.L2.Th1.F.area L) n N N' y (putL n N N' k x) = matH (hOne L n) (ent k y) x := by
  rw [formV_sum, ← Fintype.sum_prod_type' (f := fun i j => matH (hOne L n) (fun τ => y τ i j)
    (fun τ => putL n N N' k x τ i j))]
  rw [Finset.sum_eq_single k]
  · have : (fun τ => putL n N N' k x τ k.1 k.2) = x := by
      have := ent_putL k k x
      rw [if_pos rfl] at this
      exact this
    rw [this]
    rfl
  · intro p _ hp
    have : (fun τ => putL n N N' k x τ p.1 p.2) = 0 := by
      have := ent_putL k p x
      rw [if_neg hp] at this
      exact this
    rw [this, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem alphaQ_put (c : ℝ) (L : PeriodPair) (k : Fin N' × Fin N) (x : n → ℂ) :
    alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N') (putL n N N' k x) = alphaQ c (matH (hOne L n)) x := by
  unfold alphaQ qOf
  rw [form_put, ent_putL, if_pos rfl]

theorem oneEntry_mem (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {F : (n → Fin N' → Fin N → ℂ) → ℂ}
    (hF : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N')) (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N) :
    (fun w => F (setE z k w)) ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM := by
  refine ⟨?_, ?_⟩
  · intro w _
    have e : (fun w => F (setE z k w)) =
        F ∘ (fun w => setE z k 0 + (LinearMap.toContinuousLinearMap (putL n N N' k)) w) := by
      funext w
      show F (setE z k w) = F (setE z k 0 + putL n N N' k w)
      rw [setE_add, zero_add]
    rw [e]
    exact (hF.1 _ (Set.mem_univ _)).comp
      (analyticAt_const.add ((LinearMap.toContinuousLinearMap (putL n N N' k)).analyticAt w))
  · intro x hx w
    have h := hF.2 (putL n N N' k x) (putL_mem ΛM N N' k hx) (setE z k w)
    rw [alphaQ_put] at h
    simp only [opU] at h ⊢
    rw [setE_add, form_put, form_put, ent_setE, ent_putL, if_pos rfl] at h
    exact h

theorem tens_spans (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {θ : (n → ℂ) → ℂ} (hθ0 : θ ≠ 0)
    (hline : ∀ G ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, G = a • θ)
    (N N' : ℕ) :
    ∀ F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'), ∃ a : ℂ, F = a • tensPow θ N N' := by
  intro F hF
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, θ a₀ ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hθ0 (funext hno)
  have step : ∀ (z : n → Fin N' → Fin N → ℂ) (k : Fin N' × Fin N),
      F z * θ a₀ = F (setE z k a₀) * θ (ent k z) := by
    intro z k
    obtain ⟨a, ha⟩ := hline _ (oneEntry_mem c L ΛM hF z k)
    have h1 : F (setE z k (ent k z)) = a * θ (ent k z) := congrFun ha (ent k z)
    have h2 : F (setE z k a₀) = a * θ a₀ := congrFun ha a₀
    rw [setE_ent] at h1
    rw [h1, h2]
    ring
  have ind : ∀ (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ),
      F z * θ a₀ ^ s.card = F (repl a₀ s z) * ∏ p ∈ s, θ (ent p z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z
      have : repl a₀ (∅ : Finset (Fin N' × Fin N)) z = z := by
        funext τ i j
        simp [repl]
      simp [this]
    | insert k s hk ih =>
      intro z
      have key := step (repl a₀ s z) k
      have e1 : setE (repl a₀ s z) k a₀ = repl a₀ (insert k s) z := by
        funext τ i j
        by_cases h : (i, j) = k <;> simp [setE, repl, Finset.mem_insert, h]
      have e2 : ent k (repl a₀ s z) = ent k z := by
        funext τ
        simp [ent, repl, hk]
      rw [e1, e2] at key
      rw [Finset.card_insert_of_notMem hk, pow_succ, ← mul_assoc, ih z, Finset.prod_insert hk]
      linear_combination (∏ p ∈ s, θ (ent p z)) * key
  refine ⟨F (fun τ _ _ => a₀ τ) / θ a₀ ^ (Finset.univ : Finset (Fin N' × Fin N)).card, ?_⟩
  funext z
  have h := ind Finset.univ z
  have e1 : repl a₀ (Finset.univ : Finset (Fin N' × Fin N)) z = fun τ _ _ => a₀ τ := by
    funext τ i j
    simp [repl]
  have e2 : tensPow θ N N' z = ∏ p : Fin N' × Fin N, θ (ent p z) := by
    unfold tensPow
    exact (Fintype.prod_prod_type' (f := fun i j => θ fun τ => z τ i j)).symm
  rw [e1] at h
  show F z = _ * tensPow θ N N' z
  rw [e2, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ ha₀)]
  exact h

end Gen

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Ker.Base D cc δ}

theorem thZeroSpans (hS : B.StdOK) (N N' : ℕ) : B.ThZeroSpans N N' := by
  intro F hF
  have e : TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have h0' : TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have h1 : F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')
      (alphaQ B.cq (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) := by
    refine Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := B.qInt0 hS N N' x hx
    exact al_eq D B.tor x m hm
  rw [e, h0'] at h1
  exact tens_spans B.cq B.L B.lamM (B.thMM_ne_zero hS)
    (isThM_spans _ _ _ _ _ _ hS B.kappa_ne_zero (B.thMM_spec hS)) N N' F h1

end Formalism.L2.PairingIndexBounds.Eq.J
