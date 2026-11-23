import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0EqSumOfSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDifferentialOperatorDepthEqIInfMonomiStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

namespace DepthAdd

noncomputable section

section Support

variable {C : Type} [Field C] {σ : Type}

def SuppIn (T : Set σ) (g : MvPowerSeries σ C) : Prop :=
  ∀ α : σ →₀ ℕ, coeff α g ≠ 0 → ∀ y ∈ α.support, y ∈ T

theorem suppIn_mono {T T' : Set σ} (h : T ⊆ T') {g : MvPowerSeries σ C} (hg : SuppIn T g) :
    SuppIn T' g := fun α hα y hy => h (hg α hα y hy)

theorem suppIn_mul {T : Set σ} {f g : MvPowerSeries σ C} (hf : SuppIn T f) (hg : SuppIn T g) :
    SuppIn T (f * g) := by
  classical
  intro α hα y hy
  rw [coeff_mul] at hα
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : coeff p.1 f ≠ 0 := left_ne_zero_of_mul hne
  have h2 : coeff p.2 g ≠ 0 := right_ne_zero_of_mul hne
  rw [← hp, Finsupp.mem_support_iff, Finsupp.add_apply] at hy
  by_cases h : p.1 y = 0
  · rw [h, zero_add] at hy
    exact hg _ h2 y (Finsupp.mem_support_iff.2 hy)
  · exact hf _ h1 y (Finsupp.mem_support_iff.2 h)

theorem suppIn_one (T : Set σ) : SuppIn T (1 : MvPowerSeries σ C) := by
  classical
  intro α hα y hy
  rw [coeff_one] at hα
  split_ifs at hα with h
  · subst h; simp at hy
  · exact absurd rfl hα

theorem suppIn_pow {T : Set σ} {f : MvPowerSeries σ C} (hf : SuppIn T f) (n : ℕ) :
    SuppIn T (f ^ n) := by
  induction n with
  | zero => simpa using suppIn_one (C := C) T
  | succ n ih => rw [pow_succ]; exact suppIn_mul ih hf

theorem suppIn_finsuppProd {T : Set σ} {τ : Type} (β : τ →₀ ℕ) (a : τ → MvPowerSeries σ C)
    (h : ∀ i ∈ β.support, SuppIn T (a i)) : SuppIn T (β.prod fun i n => a i ^ n) :=
  Finset.prod_induction _ (SuppIn T) (fun _ _ => suppIn_mul) (suppIn_one T)
    (fun i hi => suppIn_pow (h i hi) _)

theorem suppIn_add {T : Set σ} {f g : MvPowerSeries σ C} (hf : SuppIn T f) (hg : SuppIn T g) :
    SuppIn T (f + g) := by
  intro α hα
  rw [map_add] at hα
  by_cases h : coeff α f = 0
  · rw [h, zero_add] at hα; exact hg α hα
  · exact hf α h

theorem suppIn_zero (T : Set σ) : SuppIn T (0 : MvPowerSeries σ C) := by
  intro α hα; simp at hα

theorem suppIn_smul {T : Set σ} {f : MvPowerSeries σ C} (c : C) (hf : SuppIn T f) :
    SuppIn T (c • f) := by
  intro α hα
  rw [map_smul, smul_eq_mul] at hα
  exact hf α (right_ne_zero_of_mul hα)

theorem suppIn_X {T : Set σ} {y : σ} (hy : y ∈ T) : SuppIn T (X y : MvPowerSeries σ C) := by
  classical
  intro α hα z hz
  rw [coeff_X] at hα
  split_ifs at hα with h
  · subst h
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hz
    exact hz ▸ hy
  · exact absurd rfl hα

theorem suppIn_sum {T : Set σ} {τ : Type} (s : Finset τ) (f : τ → MvPowerSeries σ C)
    (h : ∀ i ∈ s, SuppIn T (f i)) : SuppIn T (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (SuppIn T) (fun _ _ => suppIn_add) (suppIn_zero T) h

theorem suppIn_subst {T : Set σ} {τ : Type} {a : τ → MvPowerSeries σ C} (ha : HasSubst a)
    (h : ∀ i, SuppIn T (a i)) (f : MvPowerSeries τ C) : SuppIn T (subst a f) := by
  intro α hα
  rw [coeff_subst ha] at hα
  by_contra hc
  apply hα
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  have : coeff α (e.prod fun s n => a s ^ n) = 0 := by
    by_contra hne
    exact hc (suppIn_finsuppProd e a (fun i _ => h i) α hne)
  rw [this, smul_zero]

end Support

section Factor

variable {C : Type} [Field C] {σ : Type}

theorem mfact_add_of_disjoint {α₁ α₂ : σ →₀ ℕ} (h : Disjoint α₁.support α₂.support) :
    (mfact (α₁ + α₂) : C) = mfact α₁ * mfact α₂ := by
  unfold mfact
  exact Finsupp.prod_add_index_of_disjoint h _

theorem mfact_zero' : (mfact (0 : σ →₀ ℕ) : C) = 1 := by
  unfold mfact; exact Finsupp.prod_zero_index

theorem derivAt0_monomial (γ : σ →₀ ℕ) (c : C) (g : MvPowerSeries σ C) :
    derivAt0 (MvPolynomial.monomial γ c) g = c * mfact γ * coeff γ g := by
  classical
  rw [derivAt0_eq_sum_of_subset _ g (MvPolynomial.support_monomial_subset), Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def derivAt0Hom (g : MvPowerSeries σ C) : MvPolynomial σ C →+ C where
  toFun P := derivAt0 P g
  map_zero' := by simp [derivAt0]
  map_add' P Q := by
    classical
    show derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g
    rw [derivAt0_eq_sum_of_subset (P + Q) g (MvPolynomial.support_add (p := P) (q := Q)),
      derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
      derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_add]
    ring

theorem derivAt0_sum {τ : Type} (s : Finset τ) (f : τ → MvPolynomial σ C) (g : MvPowerSeries σ C) :
    derivAt0 (∑ i ∈ s, f i) g = ∑ i ∈ s, derivAt0 (f i) g :=
  map_sum (derivAt0Hom g) f s

theorem derivAt0_one (g : MvPowerSeries σ C) :
    derivAt0 (1 : MvPolynomial σ C) g = constantCoeff g := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, derivAt0_monomial,
    mfact_zero', coeff_zero_eq_constantCoeff_apply, one_mul, one_mul]

theorem coeff_mul_split {T : Set σ} {A B : MvPowerSeries σ C} (hA : SuppIn T A)
    (hB : SuppIn Tᶜ B) {α₁ α₂ : σ →₀ ℕ} (h₁ : ∀ y ∈ α₁.support, y ∈ T)
    (h₂ : ∀ y ∈ α₂.support, y ∉ T) :
    coeff (α₁ + α₂) (A * B) = coeff α₁ A * coeff α₂ B := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_single (α₁, α₂) (fun p hp hne => ?_)
    (fun h => (h (by rw [Finset.HasAntidiagonal.mem_antidiagonal])).elim)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_contra hc
  have hp1 : coeff p.1 A ≠ 0 := left_ne_zero_of_mul hc
  have hp2 : coeff p.2 B ≠ 0 := right_ne_zero_of_mul hc
  apply hne
  have key : p.1 = α₁ := by
    ext y
    have e := congrArg (fun f => f y) hp
    simp only [Finsupp.add_apply] at e
    by_cases hy : y ∈ T
    · have a2 : α₂ y = 0 := by
        by_contra hz; exact h₂ y (Finsupp.mem_support_iff.2 hz) hy
      have b2 : p.2 y = 0 := by
        by_contra hz; exact hB _ hp2 y (Finsupp.mem_support_iff.2 hz) hy
      omega
    · have a1 : α₁ y = 0 := by
        by_contra hz; exact hy (h₁ y (Finsupp.mem_support_iff.2 hz))
      have b1 : p.1 y = 0 := by
        by_contra hz; exact hy (hA _ hp1 y (Finsupp.mem_support_iff.2 hz))
      omega
  refine Prod.ext key ?_
  rw [key] at hp
  exact add_left_cancel hp

theorem derivAt0_mul_split {T : Set σ} (P Q : MvPolynomial σ C) (A B : MvPowerSeries σ C)
    (hP : ∀ α ∈ P.support, ∀ y ∈ α.support, y ∈ T)
    (hQ : ∀ α ∈ Q.support, ∀ y ∈ α.support, y ∉ T)
    (hA : SuppIn T A) (hB : SuppIn Tᶜ B) :
    derivAt0 (P * Q) (A * B) = derivAt0 P A * derivAt0 Q B := by
  classical
  have hPQ : P * Q = ∑ α₁ ∈ P.support, ∑ α₂ ∈ Q.support,
      MvPolynomial.monomial (α₁ + α₂) (P.coeff α₁ * Q.coeff α₂) := by
    conv_lhs => rw [P.as_sum, Q.as_sum]
    rw [Finset.sum_mul_sum]
    simp_rw [MvPolynomial.monomial_mul]
  rw [hPQ, derivAt0_sum]
  simp_rw [derivAt0_sum, derivAt0_monomial]
  unfold derivAt0
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α₁ h₁ => Finset.sum_congr rfl fun α₂ h₂ => ?_
  have hd : Disjoint α₁.support α₂.support :=
    Finset.disjoint_left.2 fun y y₁ y₂ => hQ α₂ h₂ y y₂ (hP α₁ h₁ y y₁)
  rw [mfact_add_of_disjoint hd, coeff_mul_split hA hB (hP α₁ h₁) (hQ α₂ h₂)]
  ring

end Factor

section Columns

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)}
  {κ : Type} [Fintype κ] {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
  [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C)

omit [CharZero C] in
theorem hasSubst_of_constantCoeff_eq_zero {τ σ : Type} [Finite τ] {a : τ → MvPowerSeries σ C}
    (h : ∀ i, constantCoeff (a i) = 0) : HasSubst a :=
  ⟨fun i => by rw [h i]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩

omit [CharZero C] [Fintype κ] in
theorem colLin_const (c : κ) (e : Fin (d c)) :
    constantCoeff (∑ a, u c a e • (X ⟨c, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := by
  simp

theorem expAlong_const (x : Σ b, Fin (d b)) : constantCoeff (expAlong G u x) = 0 := by
  unfold expAlong
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_eq_zero (colLin_const u x.1))
    (colLin_const u x.1) ((expOf_twoSided_unique C v (d x.1) (G x.1)).1.1 x.2)

omit [CharZero C] [Fintype κ] in

theorem expAlong_suppIn (x : Σ b, Fin (d b)) :
    SuppIn {y : Σ b, ι b | y.1 = x.1} (expAlong G u x) := by
  unfold expAlong
  exact suppIn_subst (hasSubst_of_constantCoeff_eq_zero (colLin_const u x.1))
    (fun e => suppIn_sum _ _ fun a _ => suppIn_smul _ (suppIn_X rfl)) _

theorem hasSubst_expAlong : HasSubst (expAlong G u) :=
  hasSubst_of_constantCoeff_eq_zero (expAlong_const G u)

def monAlong (γ : (Σ b, Fin (d b)) →₀ ℕ) : MvPowerSeries (Σ b, ι b) C :=
  subst (expAlong G u) (monomial γ (1 : C))

theorem monAlong_add (γ₁ γ₂ : (Σ b, Fin (d b)) →₀ ℕ) :
    monAlong G u (γ₁ + γ₂) = monAlong G u γ₁ * monAlong G u γ₂ := by
  unfold monAlong
  rw [← subst_mul (hasSubst_expAlong G u), monomial_mul_monomial, one_mul]

theorem monAlong_suppIn (γ : (Σ b, Fin (d b)) →₀ ℕ) (S : Set κ) (h : ∀ x ∈ γ.support, x.1 ∈ S) :
    SuppIn {y : Σ b, ι b | y.1 ∈ S} (monAlong G u γ) := by
  unfold monAlong
  rw [subst_monomial (hasSubst_expAlong G u), map_one, one_mul]
  refine suppIn_finsuppProd γ _ fun x hx => suppIn_mono ?_ (expAlong_suppIn G u x)
  intro y hy
  show y.1 ∈ S
  rw [show y.1 = x.1 from hy]
  exact h x hx

theorem monAlong_const (γ : (Σ b, Fin (d b)) →₀ ℕ) :
    constantCoeff (monAlong G u γ) = 1 ∨ constantCoeff (monAlong G u γ) = 0 := by
  classical
  by_cases hγ : γ = 0
  · left
    unfold monAlong
    rw [subst_monomial (hasSubst_expAlong G u), hγ]
    simp
  · right
    unfold monAlong
    refine constantCoeff_subst_eq_zero (hasSubst_expAlong G u) (expAlong_const G u) ?_
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg (fun h => hγ h.symm)]

omit [CharZero C] [Fintype κ] in
theorem monAlong_int (γ : (Σ b, Fin (d b)) →₀ ℕ) : MvIsInt v (monomial γ (1 : C)) := by
  classical
  intro α
  unfold IsIntV
  rw [coeff_monomial]
  split_ifs <;> simp

end Columns

theorem toE_add (x y : WithTop ℝ) : toE (x + y) = toE x + toE y := rfl

theorem toE_top : toE (⊤ : WithTop ℝ) = ⊤ := rfl

theorem one_support_vac {C : Type} [Field C] {σ : Type} :
    ∀ α ∈ (1 : MvPolynomial σ C).support, ∀ y ∈ α.support, False := by
  intro α hα y hy
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hα
  subst hα
  simp at hy

theorem exists_monomial_depth_eq (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type)
    [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C)
    (R : MvPolynomial (Σ b, ι b) C) :
    ∃ γ, depth G u R = toE (v (derivAt0 R (monAlong G u γ))) := by
  have hfin : {β : (Σ b, Fin (d b)) →₀ ℕ | β.degree ≤ R.totalDegree}.Finite :=
    Finsupp.finite_of_degree_le _
  obtain ⟨γ, hγ, hmin⟩ := Set.exists_min_image _
    (fun γ => toE (v (derivAt0 R (monAlong G u γ)))) hfin ⟨0, by simp⟩
  refine ⟨γ, ?_⟩
  rw [GlobalTheory.T.formalGroupDifferentialOperatorDepth_eq_iInf_monomial C v κ d G ι u R]
  exact le_antisymm (iInf₂_le γ hγ) (le_iInf₂ fun β hβ => hmin β hβ)

end

end DepthAdd

open DepthAdd in

theorem depth_mul_of_disjoint_columns : ∀ (C : Type) [Field C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ)
    (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (u : ∀ b, ι b → Fin (d b) → C) (S : Set κ) (P Q : MvPolynomial (Σ b, ι b) C),
    (∀ x ∈ P.vars, x.1 ∈ S) → (∀ x ∈ Q.vars, x.1 ∉ S) →
      depth G u (P * Q) = depth G u P + depth G u Q := by
  intro C _ _ v κ _ _ d G ι _ _ u S P Q hP hQ
  classical
  have hP' : ∀ α ∈ P.support, ∀ y ∈ α.support, y ∈ {y : Σ b, ι b | y.1 ∈ S} :=
    fun α hα y hy => hP y ((MvPolynomial.mem_vars y).2 ⟨α, hα, hy⟩)
  have hQ' : ∀ α ∈ Q.support, ∀ y ∈ α.support, y ∉ {y : Σ b, ι b | y.1 ∈ S} :=
    fun α hα y hy => hQ y ((MvPolynomial.mem_vars y).2 ⟨α, hα, hy⟩)
  let l : ((Σ b, Fin (d b)) →₀ ℕ) → ((Σ b, Fin (d b)) →₀ ℕ) := fun γ => γ.filter fun x => x.1 ∈ S
  let r : ((Σ b, Fin (d b)) →₀ ℕ) → ((Σ b, Fin (d b)) →₀ ℕ) := fun γ => γ.filter fun x => x.1 ∉ S
  have hsplit : ∀ γ, monAlong G u γ = monAlong G u (l γ) * monAlong G u (r γ) := fun γ => by
    rw [← monAlong_add]
    congr 1
    ext x
    by_cases hx : x.1 ∈ S <;> simp [l, r, Finsupp.filter_apply, hx]
  have hA : ∀ γ, SuppIn {y : Σ b, ι b | y.1 ∈ S} (monAlong G u (l γ)) := fun γ =>
    monAlong_suppIn G u _ S fun x hx => by
      by_contra h
      simp [l, h] at hx
  have hB : ∀ γ, SuppIn {y : Σ b, ι b | y.1 ∈ S}ᶜ (monAlong G u (r γ)) := fun γ =>
    monAlong_suppIn G u _ Sᶜ fun x hx h => by
      simp [r, h] at hx
  have h1 : ∀ γ, toE (v (derivAt0 (P * Q) (monAlong G u γ))) =
      toE (v (derivAt0 P (monAlong G u (l γ)))) + toE (v (derivAt0 Q (monAlong G u (r γ)))) :=
    fun γ => by
      rw [hsplit γ, derivAt0_mul_split P Q _ _ hP' hQ' (hA γ) (hB γ), v.map_mul, toE_add]
  have h2 : ∀ γ, toE (v (derivAt0 P (monAlong G u (l γ)))) ≤
      toE (v (derivAt0 P (monAlong G u γ))) := fun γ => by
    have e := derivAt0_mul_split P 1 _ _ hP'
      (fun α hα y hy => (one_support_vac α hα y hy).elim) (hA γ) (hB γ)
    rw [mul_one, derivAt0_one, ← hsplit γ] at e
    rw [e]
    rcases monAlong_const G u (r γ) with h | h
    · rw [h, mul_one]
    · rw [h, mul_zero, v.map_zero, toE_top]; exact le_top
  have h3 : ∀ γ, toE (v (derivAt0 Q (monAlong G u (r γ)))) ≤
      toE (v (derivAt0 Q (monAlong G u γ))) := fun γ => by
    have e := derivAt0_mul_split 1 Q _ _
      (fun α hα y hy => (one_support_vac α hα y hy).elim) hQ' (hA γ) (hB γ)
    rw [one_mul, derivAt0_one, ← hsplit γ] at e
    rw [e]
    rcases monAlong_const G u (l γ) with h | h
    · rw [h, one_mul]
    · rw [h, zero_mul, v.map_zero, toE_top]; exact le_top
  have h5 : ∀ R γ, depth G u R ≤ toE (v (derivAt0 R (monAlong G u γ))) := fun R γ =>
    iInf_le_of_le ⟨monomial γ 1, monAlong_int γ⟩ le_rfl
  obtain ⟨γ₀, e₀⟩ := exists_monomial_depth_eq C v κ d G ι u (P * Q)
  obtain ⟨γ₁, e₁⟩ := exists_monomial_depth_eq C v κ d G ι u P
  obtain ⟨γ₂, e₂⟩ := exists_monomial_depth_eq C v κ d G ι u Q
  apply le_antisymm
  · have hl : l (l γ₁ + r γ₂) = l γ₁ := by
      ext x
      by_cases hx : x.1 ∈ S <;> simp [l, r, Finsupp.filter_apply, hx]
    have hr : r (l γ₁ + r γ₂) = r γ₂ := by
      ext x
      by_cases hx : x.1 ∈ S <;> simp [l, r, Finsupp.filter_apply, hx]
    refine (h5 _ (l γ₁ + r γ₂)).trans ?_
    rw [h1, hl, hr, e₁, e₂]
    exact add_le_add (h2 γ₁) (h3 γ₂)
  · rw [e₀, h1]
    exact add_le_add (h5 P _) (h5 Q _)

end GlobalTheory.FGDepth
