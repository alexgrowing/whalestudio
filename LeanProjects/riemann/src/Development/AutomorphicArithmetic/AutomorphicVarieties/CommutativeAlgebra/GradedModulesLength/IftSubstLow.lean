import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

open MvPowerSeries Formalism.FG.SolveVAux

variable {E σ τ Y : Type} [CommRing E] [AddCommGroup Y]

private theorem ift_P_mem {w : σ → Y} {w' : τ → Y} {k : σ → MvPowerSeries τ E}
    (hw : ∀ i, k i ∈ wtPart E w' (w i)) (e : σ →₀ ℕ) : P k e ∈ wtPart E w' (Finsupp.weight w e) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [P_zero, map_zero]; exact one_mem_wtPart E w'
  | add e₁ e₂ h₁ h₂ => rw [P_add, map_add]; exact mul_mem_wtPart E w' h₁ h₂
  | single i n =>
    rw [P_single, Finsupp.weight_single]
    exact SetLike.pow_mem_graded n (hw i)

private theorem ift_subst_mem [Finite σ] {w : σ → Y} {w' : τ → Y} {k : σ → MvPowerSeries τ E}
    (hk : ∀ i, Low 1 (k i)) (hw : ∀ i, k i ∈ wtPart E w' (w i)) {j : Y} {g : MvPowerSeries σ E}
    (hg : g ∈ wtPart E w j) : subst k g ∈ wtPart E w' j := by
  intro n hn
  rw [coeff_subst (hasSubst_of_low hk)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases he : Finsupp.weight w e = j
  · have := ift_P_mem hw e n (he ▸ hn)
    simp only [P] at this
    rw [this, smul_zero]
  · rw [hg e he, zero_smul]

private theorem ift_subst_low [Finite σ] {k : σ → MvPowerSeries τ E} (hk : ∀ i, Low 1 (k i)) {N : ℕ}
    {g : MvPowerSeries σ E} (hg : Low N g) : Low N (subst k g) := by
  intro d hd
  rw [coeff_subst (hasSubst_of_low hk)]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rcases lt_or_ge e.degree N with he | he
  · rw [hg e he, zero_smul]
  · have := low_P hk e d (by omega)
    simp only [P] at this
    rw [this, smul_zero]

private theorem ift_lim_mem [Finite σ] {w : σ → Y} {w' : τ → Y} {G : σ → MvPowerSeries τ E}
    {g : σ → MvPowerSeries σ E} (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j))
    (hGw : ∀ i, G i ∈ wtPart E w' (w i)) (hgw : ∀ i, g i ∈ wtPart E w (w i)) (i : σ) :
    Formalism.FG.SolveVAux.lim G g i ∈ wtPart E w' (w i) := by
  have hs : ∀ n i, Formalism.FG.SolveVAux.seq G g n i ∈ wtPart E w' (w i) := by
    intro n
    induction n with
    | zero => exact fun i => zero_mem _
    | succ n ih =>
      intro i
      rw [seq_succ]
      exact sub_mem (hGw i) (ift_subst_mem (seq_low hG hg n) ih (hgw i))
  intro d hd
  rw [coeff_lim]
  exact hs _ i d hd

private theorem ift_low_two {p : MvPowerSeries σ E} (h0 : constantCoeff p = 0)
    (h1 : ∀ i, coeff (Finsupp.single i 1) p = 0) : Low 2 p := by
  intro d hd
  rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h | h
  · exact (low_one_iff p).2 h0 d h
  · obtain ⟨i, rfl⟩ := degree_eq_one d h
    exact h1 i

private theorem ift_coeff_X [DecidableEq σ] (i j : σ) :
    coeff (Finsupp.single i 1) (X j : MvPowerSeries σ E) = if i = j then 1 else 0 := by
  classical
  rw [coeff_X]
  simp [Finsupp.single_left_inj one_ne_zero]

private theorem ift_expand [Fintype σ] (g : MvPowerSeries σ E) :
    Low 2 (g - (constantCoeff g • 1 + ∑ s, coeff (Finsupp.single s 1) g • X s)) := by
  classical
  refine ift_low_two (by simp [map_sum]) fun i => ?_
  simp [map_sum, ift_coeff_X, coeff_one]

end SlopeTestRemainingChoices

private theorem ift_span {E ι κ M : Type} [Field E] [Fintype ι] [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    [Module E M] (hc : Fintype.card κ = Fintype.card ι) (c : Matrix κ ι E) (L : Matrix ι κ E) (h : c * L = 1)
    (v : ι → M) (hv : ∀ i, ∑ k, c i k • v k = 0) (k : ι) : v k = 0 := by
  classical
  have h' : L * c = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).1 h
  have : ∑ i, L k i • ∑ k', c i k' • v k' = ∑ k', (L * c) k k' • v k' := by
    simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  simpa [hv, h', Matrix.one_apply] using this.symm

open MvPowerSeries Formalism.FG.SolveVAux in
theorem UpperTheory.V.Alg.M.ift_holds :
    ∀ (E τ ι X : Type) [Field E] [Fintype τ] [Fintype ι] [AddCommGroup X] (wt : τ → X) (z : ι → MvPowerSeries τ E),
      (∀ k, z k ∈ wtPart E wt 0 ∧ MvPowerSeries.constantCoeff (z k) = 0) → Nat.card {i // wt i = 0} = Fintype.card ι →
      (∀ i, wt i = 0 → ∃ c : ι → E, ∀ i', MvPowerSeries.coeff (Finsupp.single i' 1) (∑ k, c k • z k) =
        MvPowerSeries.coeff (Finsupp.single i' 1) (MvPowerSeries.X i : MvPowerSeries τ E)) →
      ∃ ψ : MvPowerSeries τ E →ₐ[E] MvPowerSeries {i // wt i ≠ 0} E,
        (∀ j, ∀ g ∈ wtPart E wt j, ψ g ∈ wtPart E (fun i : {i // wt i ≠ 0} => wt i) j) ∧ (∀ k, ψ (z k) = 0) ∧
        (∀ g, MvPowerSeries.constantCoeff (ψ g) = MvPowerSeries.constantCoeff g) ∧
        ∀ g (i : {i // wt i ≠ 0}), MvPowerSeries.coeff (Finsupp.single i 1) (ψ g) = MvPowerSeries.coeff (Finsupp.single i.1 1) g := by
  intro E τ ι Y _ _ _ _ wt z hz hcard hc
  classical
  choose c hc using hc
  let G : τ → MvPowerSeries {i // wt i ≠ 0} E := fun i => if h : wt i = 0 then 0 else X ⟨i, h⟩
  let g : τ → MvPowerSeries τ E := fun i => if h : wt i = 0 then ∑ k, c i h k • z k - X i else 0
  have hG : ∀ j, Low 1 (G j) := fun j => by
    rw [low_one_iff]
    simp only [G]
    split_ifs <;> simp
  have hg : ∀ j, Low 2 (g j) := fun j => by
    simp only [g]
    split_ifs with h
    · refine ift_low_two (by simp [map_sum, fun k => (hz k).2]) fun i => ?_
      rw [map_sub, hc, sub_self]
    · exact low_of_zero _
  have hGw : ∀ i, G i ∈ wtPart E (fun i : {i // wt i ≠ 0} => wt i) (wt i) := fun i => by
    simp only [G]
    split_ifs with h
    · exact zero_mem _
    · exact X_mem_wtPart E (fun i : {i // wt i ≠ 0} => wt i) ⟨i, h⟩
  have hgw : ∀ i, g i ∈ wtPart E wt (wt i) := fun i => by
    simp only [g]
    split_ifs with h
    · refine sub_mem (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_) (X_mem_wtPart E wt i)
      rw [h]; exact (hz k).1
    · exact zero_mem _
  have hl := lim_low hG hg
  have hs := hasSubst_of_low hl
  let ψ : MvPowerSeries τ E →ₐ[E] MvPowerSeries {i // wt i ≠ 0} E := substAlgHom hs
  have hψ : ∀ f, ψ f = subst (Formalism.FG.SolveVAux.lim G g) f := fun f => substAlgHom_apply hs f
  have hX : ∀ i, ψ (X i) = G i - ψ (g i) := fun i => by
    rw [hψ, hψ, subst_X hs]; exact (lim_fixed hG hg i).symm
  have hlow : ∀ f, Low 2 f → Low 2 (ψ f) := fun f hf => by rw [hψ]; exact ift_subst_low hl hf
  have key : ∀ f (d : {i // wt i ≠ 0} →₀ ℕ), d.degree < 2 → coeff d (ψ f) =
      constantCoeff f * coeff d (1 : MvPowerSeries {i // wt i ≠ 0} E) +
        ∑ s, coeff (Finsupp.single s 1) f * coeff d (G s) := fun f d hd => by
    have := hlow _ (ift_expand f) d hd
    rw [map_sub, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [map_add, map_smul, map_one, map_sum, hX, map_sub, hlow _ (hg _) d hd, sub_zero, smul_eq_mul]
  refine ⟨ψ, fun j f hf => ?_, ?_, fun f => ?_, fun f i => ?_⟩
  · rw [hψ]; exact ift_subst_mem hl (ift_lim_mem hG hg hGw hgw) hf
  · refine ift_span (E := E) (κ := {i // wt i = 0}) (by rw [← hcard, Nat.card_eq_fintype_card])
      (Matrix.of fun i k => c i.1 i.2 k) (Matrix.of fun k i => coeff (Finsupp.single i.1 1) (z k)) ?_
      (fun k => ψ (z k)) fun i => ?_
    · ext i i'
      have := hc i.1 i.2 i'.1
      rw [ift_coeff_X] at this
      simp only [map_sum, map_smul, smul_eq_mul] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Subtype.ext_iff, eq_comm]
    · have := hX i.1
      simp only [G, g, dif_pos i.2, map_sub, map_sum, map_smul] at this
      simp only [Matrix.of_apply]
      linear_combination this
  · have := key f 0 (by simp)
    rw [← coeff_zero_eq_constantCoeff_apply, this]
    simp [fun s => hG s 0 (by simp)]
  · rw [key f _ (by simp), Finset.sum_eq_single i.1]
    · simp [G, i.2, coeff_one]
    · intro s _ hs
      simp only [G]
      split_ifs with h
      · simp
      · rw [ift_coeff_X, if_neg (fun h' => hs (by rw [h'])), mul_zero]
    · simp
