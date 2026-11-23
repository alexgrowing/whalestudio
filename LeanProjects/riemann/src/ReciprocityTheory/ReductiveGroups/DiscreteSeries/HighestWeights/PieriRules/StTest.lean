import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem pieriSt_mem_khwSub_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (v : W) :
    v ∈ khwSub ε E ν ↔ Formalism.REAL.KHighest ε E ν v := by
  simp only [khwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, Formalism.REAL.KHighest,
    Formalism.REAL.IsWeight]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b h => h2 a b h.1 h.2⟩

theorem pieriSt_isKHWVec_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (μ : Fin n → ℝ) (v : W) :
    IsKHWVec ε E μ v ↔ Formalism.REAL.KHighest ε E μ v := Iff.rfl

theorem pieriSt_tensAct_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] {n : ℕ} (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A M a b x i = A a b (x i) + ∑ j, M a b i j • x j := by
  simp [tensAct]

theorem pieriSt_kRel_stdM {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.KRel ε (stdM n) := by
  intro a b c d _ _
  simp only [stdM]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pieriSt_stdM_diag {n : ℕ} (a : Fin n) :
    stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hai : a = i
    · subst hai; simp [stdM, stdWt]
    · simp [stdM, stdWt, hai, Pi.single_apply]
  · simp [stdM, Matrix.single_apply, hij]
    intro h1 h2; exact hij (h1.symm.trans h2)

theorem pieriSt_tensHW_inhabited {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.KRel ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KUnit ε (0 : Fin n → Fin n → Module.End ℂ ℂ) ∧
    Formalism.REAL.KHighest ε (0 : Fin n → Fin n → Module.End ℂ ℂ) 0 (1 : ℂ) ∧
    Formalism.REAL.kSpan ε (0 : Fin n → Fin n → Module.End ℂ ℂ) (1 : ℂ) = ⊤ ∧
    Formalism.REAL.KRel ε (stdM n) ∧
    (∀ a, stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, pieriSt_kRel_stdM ε, pieriSt_stdM_diag⟩
  · intro a b c d _ _; simp
  · intro a b _ x y; simp
  · exact ⟨fun a => by simp, fun a b _ _ => by simp⟩
  · refine eq_top_iff.mpr fun v _ => ?_
    simp only [Formalism.REAL.kSpan, Submodule.mem_sInf, Set.mem_ofPred_eq]
    rintro S ⟨h1, _⟩
    have : v = v • (1 : ℂ) := by simp
    rw [this]
    exact S.smul_mem v h1

theorem pieriSt_count_inhabited {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : KG ε =>
      (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) k : unitary (Matrix Unit Unit ℂ)) : Matrix Unit Unit ℂ)) ∧
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ =>
        (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) (γ t) : unitary (Matrix Unit Unit ℂ)) :
          Matrix Unit Unit ℂ) i j)
        ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) X i j) 0) ∧
    Formalism.REAL.KRel ε (fun a b => (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) ∧
    (∀ a, (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1) =
      Matrix.diagonal fun i => (((fun _ : Unit => (0 : Fin n → ℝ)) i a : ℝ) : ℂ)) ∧
    Function.Injective (fun _ : Unit => (0 : Fin n → ℝ)) ∧
    (∑ i : Unit, weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) =
      (Fintype.card Unit : ℝ) * weylK ε 0) ∧
    (∀ i : Unit, ¬ KDom ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) →
      weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) = 0) ∧
    Nonempty (KType ε 0) := by
  refine ⟨?_, ?_, ?_, ?_, fun a b _ => Subsingleton.elim a b, ?_, ?_, ⟨trivialKType ε⟩⟩
  · simp only [MonoidHom.one_apply]; exact continuous_const
  · intro X _ γ _ i j
    simp only [MonoidHom.one_apply, LinearMap.zero_apply]
    exact hasDerivAt_const _ _
  · intro a b c d _ _; simp
  · intro a; ext i j; simp
  · simp
  · intro i h
    exact absurd (fun a b _ _ => by simp) h

theorem pieriSt_cartan_inhabited {n : ℕ} (ε : Fin n → Bool) :
    (∀ a : Fin n, ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1)) *ᵥ
      (fun _ : Unit => (1 : ℂ)) = (((0 : Fin n → ℝ) a : ℝ) : ℂ) • (fun _ : Unit => (1 : ℂ))) ∧
    (∀ a b : Fin n, a < b → ε a = ε b →
      ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) *ᵥ
        (fun _ : Unit => (1 : ℂ)) = 0) ∧
    (fun _ : Unit => (1 : ℂ)) ≠ 0 ∧
    Formalism.REAL.KHighest ε (kunits (trivialKType ε)) 0 (trivialKType ε).w ∧ (trivialKType ε).w ≠ 0 := by
  refine ⟨fun a => by ext; simp, fun a b _ _ => by ext; simp, fun h => by simpa using congrFun h (), ?_, ?_⟩
  · exact ⟨fun a => (trivialKType ε).w_wt a, fun a b hab he => (trivialKType ε).w_hw a b hab he⟩
  · show (1 : ℂ) ≠ 0; exact one_ne_zero

end ReciprocityTheory.ChartRestriction.DS.HW
