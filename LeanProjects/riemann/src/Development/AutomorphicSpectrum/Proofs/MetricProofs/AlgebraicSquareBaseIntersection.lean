import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareXiIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareIntersectionPullbackStatement

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SqFirst

theorem isSmoothHerm_of_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    {A : HermLine ι} {A' : HermLine ι'} (hb : IsBlockMap κ v) (hA : IsSmoothHerm A)
    (hp : IsPullHerm κ v A A') : IsSmoothHerm A' := by
  have hh : A'.h = A.h ∘ (fun (z' : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z' (v p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hh]
  refine ContDiffOn.comp hA ?_ ?_
  · exact (contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)).contDiffOn
  · intro z hz k
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨⟨k₁, i⟩, hp'⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have e : κ k₁ = κ k := by
      have := hb.2.2.1 ⟨k₁, i⟩
      rw [hp'] at this
      exact this.symm
    obtain rfl := hb.1 e
    exact ⟨i, by simpa [hp'] using hi'⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pull_one_of_base {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K} {xi2 : K → ℤ} (Q : AlgSq P d k₀ xi2)
    {A : HermLine ι} {A₀ : HermLine Q.ιW} (hb : FromBase k₀ A) (h : IsPullHerm (Q.κ 0) (Q.v 0) A A₀) :
    IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := by
  have hκ : ∀ k, k ≠ k₀ → Q.κ 0 k = Q.κ 1 k := fun k hk => by
    obtain ⟨i, -⟩ := Q.arithY.2.1.2.2 k
    have := congrArg Sigma.fst (Q.same ⟨k, i⟩ hk)
    rwa [(Q.block 0).2.2.1, (Q.block 1).2.2.1] at this
  refine ⟨?_, fun z' => ?_⟩
  · rw [h.1]
    funext k'
    rcases Q.all k' with ⟨k, rfl⟩ | rfl
    · by_cases hk : k = k₀
      · subst hk
        have hn : ¬ ∃ k', Q.κ 1 k' = Q.κ 0 k := by
          rintro ⟨k', hk'⟩
          by_cases h' : k' = k
          · subst h'
            exact Q.new ⟨k', hk'.symm⟩
          · exact h' ((Q.block 0).1 ((hκ k' h').trans hk'))
        rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
        rfl
      · rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hκ k hk, (Q.block 1).1.extend_apply]
    · have hn : ¬ ∃ k', Q.κ 0 k' = Q.κ 1 k₀ := Q.new
      rw [pullDeg, pullDeg, (Q.block 1).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
      rfl
  · rw [h.2]
    exact hb.2 _ _ fun p hp => by rw [Q.same p hp]

theorem swap_nat {V : Type*} {n : ℕ} (I : (Fin n → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin n → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin n), I (L ∘ σ) = I L)
    (f : ℕ → V) (hf : ∀ j, S (f j)) (a b : ℕ) (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by
  rw [← hI (fun j => f j) (fun j => hf j) (Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩)]
  congr 1
  funext j
  simp only [Function.comp, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

theorem interp_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (k i j : ℕ) : S (interp k i x₁ x₂ a j) := by
  unfold interp
  split_ifs <;> assumption

theorem consWord_mem {V : Type*} {S : V → Prop} {x x₁ x₂ a : V} (h₀ : S x) (h₁ : S x₁) (h₂ : S x₂)
    (h₃ : S a) (k i j : ℕ) : S (consWord k i x x₁ x₂ a j) := by
  unfold consWord
  split_ifs <;> assumption

theorem word_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (D k i : ℕ) (j : Fin D) : S (word D k i x₁ x₂ a j) := by
  unfold word
  split_ifs <;> assumption

theorem consWord_left {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₁ x₁ x₂ a) (consWord_mem h₁ h₁ h₂ h₃ k i) 0 2 (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem consWord_right {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₂ x₁ x₂ a j) = I (fun j => interp k i x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₂ x₁ x₂ a) (consWord_mem h₂ h₁ h₂ h₃ k i) 1 (2 * i + 1)
      (by omega) (by omega),
    swap_nat I S hI (interp k i x₁ x₂ a) (interp_mem h₁ h₂ h₃ k i) 2 (2 * i + 2) (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem firstHalf : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ (A : HermLine ι) (A₀ : HermLine Q.ιW), IsSmoothHerm A → FromBase k₀ A → IsPullHerm (Q.κ 0) (Q.v 0) A A₀ → II K ι P (d + 2) (fun _ => A) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → II K ι P (d + 2) (mix (2 * k) Xi A) = -∑ i ∈ Finset.range k, (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1 A A₀ hAs hAb hA0
  have hR := GlobalTheory.T.algebraic_square_xi_intersection hIn II hII K ι P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1
  obtain ⟨hP1, hP0⟩ := GlobalTheory.T.algebraic_square_intersection_pullback hIn II hII K ι P d k₀ xi2 Q
  have hX0 : IsSmoothHerm X₀ := isSmoothHerm_of_pull (Q.block 0) hsm h0
  have hX1 : IsSmoothHerm X₁ := isSmoothHerm_of_pull (Q.block 1) hsm h1
  have hA0s : IsSmoothHerm A₀ := isSmoothHerm_of_pull (Q.block 0) hAs hA0
  have hA1 : IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := pull_one_of_base Q hAb hA0
  have hdeg : ((X₁.a (Q.κ 1 k₀) : ℤ) : ℝ) = -2 := by
    rw [h1.1, pullDeg, (Q.block 1).1.extend_apply, hxi, Q.xi_two_base_eq_neg_two]
    norm_num
  have hsym : ∀ L : Fin (d + 3) → HermLine Q.ιW, (∀ j, IsSmoothHerm (L j)) →
      ∀ σ : Equiv.Perm (Fin (d + 3)), II Q.KW Q.ιW Q.PW (d + 3) (L ∘ σ) = II Q.KW Q.ιW Q.PW (d + 3) L :=
    fun L hL σ => (hII.1 Q.KW Q.ιW).1 Q.PW (d + 3) L σ Q.arithW hL
  have hrot : ∀ (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L' j)) →
      IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) =
        II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons N L') := by
    intro L' N hL' hN
    rw [Fin.snoc_eq_cons_rotate]
    refine hsym (Fin.cons N L') (fun j => ?_) (finRotate _)
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hN
    · simpa using hL' j
  refine ⟨?_, ?_⟩
  · have e1 := hP1 (fun _ => A) (fun _ => A₀) X₁ (fun _ => hAs) (fun _ => hA0) hX1
    have e2 := hP0 (Fin.snoc (α := fun _ => HermLine ι) (fun _ => A) Xi)
      (Fin.snoc (α := fun _ => HermLine Q.ιW) (fun _ => A₀) X₁)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using hsm
        · simpa using hAs)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using h1
        · simpa using hA1)
    rw [e2, hdeg] at e1
    linarith
  · intro k hk hkD
    set g : ℕ → ℝ := fun i =>
      II Q.KW Q.ιW Q.PW (d + 3) (fun j : Fin (d + 3) => interp k i X₀ X₁ A₀ j) with hg
    have hstep : ∀ i ∈ Finset.range k,
        2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) = g (i + 1) - g i := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have e0 : (Fin.cons X₀ (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₀ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₀ X₀ X₁ A₀
      have e1 : (Fin.cons X₁ (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₁ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₁ X₀ X₁ A₀
      rw [← hR (word (d + 1) k i X₀ X₁ A₀) (word_mem hX0 hX1 hA0s _ _ _), e0, e1]
      have l := consWord_left (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      have r := consWord_right (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      rw [l, r]
    have h00 : g 0 = 0 := by
      rw [← hP0 (mix (1 + 2 * k) Xi A) (mix (1 + 2 * k) X₁ A₀)
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption)]
      simp only [hg]
      congr 1
      funext j
      simp only [interp, mix]
      split_ifs <;> first | rfl | omega | contradiction
    have hgk : g k = -2 * II K ι P (d + 2) (mix (2 * k) Xi A) := by
      have e := hP1 (mix (2 * k) Xi A) (mix (2 * k) X₀ A₀) X₁
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption) hX1
      rw [hrot _ X₁ (fun j => by unfold mix; split_ifs <;> assumption) hX1, hdeg] at e
      rw [← e]
      simp only [hg]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [interp]
      simp only [Fin.cons_succ, interp, mix, Fin.val_succ]
      split_ifs <;> first | rfl | omega | contradiction
    have hsum := Finset.sum_range_sub g k
    rw [← Finset.sum_congr rfl hstep, ← Finset.mul_sum, h00, hgk] at hsum
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.SqFirst
