import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftQuantumMinor.QuantumMinorLeftHermitian

private theorem eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.EabH H a b (fun x => f (h * x)) = fun x => Formalism.QuantumDeterminants.EabH H a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.EabH, Formalism.REAL.RdV, mul_assoc]

private theorem qdTop_eabH_comp_mul_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H h : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b (fun x => f (h * x)) =
      fun x => Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) u a b f (h * x) := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, eabH_comp_mul_left]

private theorem foldr_apply_comp_mul_left_of_forall_mem {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : Matrix (Fin n) (Fin n) ℂ) (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hL T' (by simp [hT']))]
    exact hL T (by simp) _

theorem qnMinorLeft : Formalism.FourierDecayAlt.Q.QMinorLeftH := by
  intro E _ _ n t H f a b u h
  funext x
  simp only [Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hL : ∀ T ∈ List.ofFn (fun k : Fin t =>
      Formalism.QuantumDeterminants.Top (Formalism.QuantumDeterminants.EabH H) (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)),
      ∀ f' : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f' (h * x)) = fun x => T f' (h * x) := by
    intro T hT f'
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hT
    exact qdTop_eabH_comp_mul_left H h _ _ _ f'
  rw [foldr_apply_comp_mul_left_of_forall_mem h _ hL f]

theorem quantum_minor_left : Formalism.FourierDecayAlt.Q.QMinorLeftH := qnMinorLeft
