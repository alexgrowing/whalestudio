import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead

theorem det_of_key {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (f : Fin m → ℕ) (hf : Function.Injective f)
    (h : ∀ i j, f i < f j → A i j = 0) : A.det = ∏ i, A i i := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, f (σ i) < f i := by
      by_contra hne
      simp only [not_exists, not_lt] at hne
      apply hσ
      have hsum : ∑ i, f (σ i) = ∑ i, f i := Equiv.sum_comp σ f
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hne i)).mp hsum.symm
      refine Equiv.ext (fun i => ?_)
      exact (hf (heq i (Finset.mem_univ i)).symm : σ i = i)
    have hz : ∏ j, A (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h _ _ hi)
    rw [hz, smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ 1) h1

private theorem minor_col_lemma {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : IsLowerUni X)
    (S I : Finset (Fin N)) (a b : Fin N) (hb : b ∈ S) (hIS : I.erase a = S.erase b)
    (hcol : ∀ d ∈ I, d ≠ a → X d b = 0) (k : ℕ) (hI : I.card = k) (hS : S.card = k)
    (p q : Fin k) (hp : I.orderEmbOfFin hI p = a) (hq : S.orderEmbOfFin hS q = b) :
    (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)).det = (-1) ^ ((p : ℕ) + (q : ℕ)) * X a b := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := Finset.card_pos.mpr ⟨b, hb⟩; omega⟩
  have hcol' : ∀ i, i ≠ p → X (I.orderEmbOfFin hI i) b = 0 := by
    intro i hi
    refine hcol _ (Finset.orderEmbOfFin_mem I hI i) (fun h1 => hi ?_)
    apply (I.orderEmbOfFin hI).injective
    rw [h1, hp]
  have hT : (S.erase b).card = n := by
    rw [Finset.card_erase_of_mem hb, hS, Nat.add_sub_cancel]
  have hg' : ⇑(S.orderEmbOfFin hS) ∘ q.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne q x ((S.orderEmbOfFin hS).injective (h1.trans hq.symm)),
        Finset.orderEmbOfFin_mem S hS _⟩
    · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove q)
  have hg : ⇑(I.orderEmbOfFin hI) ∘ p.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, ← hIS, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne p x ((I.orderEmbOfFin hI).injective (h1.trans hp.symm)),
        Finset.orderEmbOfFin_mem I hI _⟩
    · exact (I.orderEmbOfFin hI).strictMono.comp (Fin.strictMono_succAbove p)
  have hdetT : (X.submatrix ((S.erase b).orderEmbOfFin hT) ((S.erase b).orderEmbOfFin hT)).det = 1 := by
    rw [det_of_key _ (fun i => (((S.erase b).orderEmbOfFin hT i : Fin N) : ℕ)) ?_ ?_]
    · exact Finset.prod_eq_one (fun i _ => hX.1 _)
    · intro i j hij
      exact ((S.erase b).orderEmbOfFin hT).injective (Fin.ext hij)
    · intro i j hij
      exact hX.2 _ _ hij
  rw [Matrix.det_succ_column _ q, Finset.sum_eq_single p]
  · have e1 : (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)) p q = X a b := by
      rw [Matrix.submatrix_apply, hp, hq]
    rw [e1, Matrix.submatrix_submatrix, hg, hg', hdetT, mul_one]
  · intro i _ hi
    rw [Matrix.submatrix_apply, hq, hcol' i hi, mul_zero, zero_mul]
  · intro h1
    exact absurd (Finset.mem_univ p) h1

theorem exists_sign {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) (ha : a ∉ S) (hb : b ∈ S) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ X : Matrix (Fin N) (Fin N) ℂ, IsLowerUni X → (∀ d ∈ S, d ≠ b → X d b = 0) →
      minorIJ X (insert a (S.erase b)) S = c * X a b := by
  have haS : a ∉ S.erase b := fun h1 => ha (Finset.mem_of_mem_erase h1)
  have hcard : (insert a (S.erase b)).card = S.card := by
    rw [Finset.card_insert_of_notMem haS, Finset.card_erase_of_mem hb]
    have := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  obtain ⟨p, hp⟩ : ∃ p, (insert a (S.erase b)).orderEmbOfFin hcard p = a := by
    have h1 : a ∈ Set.range ((insert a (S.erase b)).orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_insert_self _ _
    exact h1
  obtain ⟨q, hq⟩ : ∃ q, S.orderEmbOfFin rfl q = b := by
    have h1 : b ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hb
    exact h1
  refine ⟨(-1) ^ ((p : ℕ) + (q : ℕ)), pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero), fun X hX hcol => ?_⟩
  rw [minorIJ, dif_pos hcard]
  refine minor_col_lemma X hX S _ a b hb (Finset.erase_insert haS) ?_ _ hcard rfl p q hp hq
  intro d hd hda
  rcases Finset.mem_insert.mp hd with h1 | h1
  · exact absurd h1 hda
  · exact hcol d (Finset.mem_of_mem_erase h1) (Finset.ne_of_mem_erase h1)

theorem minor_replace : ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (a b : Fin N), IsLowerUni X → a ∉ S → b ∈ S → b < a → (∀ c ∈ S, c ≠ b → X c b = 0) → minorIJ X (insert a (S.erase b)) S = pSgn S a b * X a b ∧ pSgn S a b ≠ 0 := by
  intro N X S a b hX ha hb hba hcol
  obtain ⟨c, hc0, hc⟩ := exists_sign S a b ha hb
  have hab : a ≠ b := (ne_of_lt hba).symm
  have hY : IsLowerUni (1 + Matrix.single a b (1 : ℂ)) := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply,
        if_neg (fun h1 => hab (h1.1.trans h1.2.symm)), add_zero]
    · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hij), Matrix.single_apply,
        if_neg (fun h1 => lt_asymm hba (by rw [h1.1, h1.2]; exact hij)), add_zero]
  have hYcol : ∀ d ∈ S, d ≠ b → (1 + Matrix.single a b (1 : ℂ)) d b = 0 := by
    intro d hd hdb
    have hda : d ≠ a := fun h1 => ha (h1 ▸ hd)
    rw [Matrix.add_apply, Matrix.one_apply_ne hdb, Matrix.single_apply,
      if_neg (fun h1 => hda h1.1.symm), add_zero]
  have hp : pSgn S a b = c := by
    rw [pSgn, hc _ hY hYcol, Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply,
      if_pos ⟨rfl, rfl⟩, zero_add, mul_one]
  rw [hp]
  exact ⟨hc X hX hcol, hc0⟩

end GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead
