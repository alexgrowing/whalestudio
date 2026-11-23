import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal

open MvPolynomial GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagAnti

theorem sum_range_le_sum (n : ℕ) : ∀ S : Finset ℕ, S.card = n → ∑ i ∈ Finset.range n, i ≤ ∑ s ∈ S, s := by
  induction n with
  | zero => intro S _; simp
  | succ n ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hmem := S.max'_mem hne
    have hM : n ≤ S.max' hne := by
      have hsub : S ⊆ Finset.range (S.max' hne + 1) := fun x hx =>
        Finset.mem_range.2 (Nat.lt_succ_of_le (S.le_max' x hx))
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    have hc : (S.erase (S.max' hne)).card = n := by
      rw [Finset.card_erase_of_mem hmem]; omega
    have := ih _ hc
    rw [Finset.sum_range_succ, ← Finset.add_sum_erase S _ hmem]
    omega

theorem le_sum_of_injective {n : ℕ} {f : Fin n → ℕ} (hf : Function.Injective f) : n * (n - 1) / 2 ≤ ∑ i, f i := by
  have h := sum_range_le_sum n (Finset.univ.image f)
    (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin])
  rw [Finset.sum_image (fun x _ y _ h => hf h), Finset.sum_range_id] at h
  exact h

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem swapAt_swapAt (τ : ι) (a b : Fin N) (x : ι × Fin N) : swapAt τ a b (swapAt τ a b x) = x := by
  rcases x with ⟨t, i⟩
  by_cases h : t = τ
  · subst h; simp [swapAt]
  · simp [swapAt, h]

theorem swapAt_conj (τ : ι) {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) :
    swapAt τ b c ∘ swapAt τ a b ∘ swapAt τ b c = swapAt τ a c := by
  funext x
  have e := congrArg (fun w : Equiv.Perm (Fin N) => w x.2) (Equiv.swap_mul_swap_mul_swap hab hac)
  simp only [Equiv.Perm.mul_apply] at e
  by_cases h : x.1 = τ
  · simp [swapAt, h, e, Equiv.swap_comm c a]
  · simp [swapAt, h]

theorem anti_swap (L : Pol ι N →ₗ[ℝ] ℝ)
    {k : ℕ} (hL : ∀ (τ : ι) (a b : Fin N), (b : ℕ) = a + 1 → ∀ P : Pol ι N, P.IsHomogeneous k →
      L (rename (swapAt τ a b) P) = -L P)
    (τ : ι) {a c : Fin N} (hac : a < c) (P : Pol ι N) (hP : P.IsHomogeneous k) :
    L (rename (swapAt τ a c) P) = -L P := by
  obtain ⟨d, hd⟩ : ∃ d, (c : ℕ) = a + 1 + d := ⟨c - (a + 1), by have := Fin.lt_def.1 hac; omega⟩
  clear hac
  induction d generalizing c P with
  | zero => exact hL τ a c (by omega) P hP
  | succ d ih =>
    let b : Fin N := ⟨a + 1 + d, by omega⟩
    have hb : (b : ℕ) = a + 1 + d := rfl
    have hab : a ≠ b := fun h => by rw [← h] at hb; omega
    have hac : a ≠ c := fun h => by rw [← h] at hd; omega
    have hbc : (c : ℕ) = b + 1 := by omega
    rw [← swapAt_conj τ hab hac, ← rename_rename, ← rename_rename,
      hL τ b c hbc _ ((hP.rename_isHomogeneous).rename_isHomogeneous), ih (c := b) _ (hP.rename_isHomogeneous) hb,
      hL τ b c hbc _ hP, neg_neg]

theorem rename_swapAt_monomial (τ : ι) {a b : Fin N} {m : (ι × Fin N) →₀ ℕ} (h : m (τ, a) = m (τ, b)) (r : ℝ) :
    rename (swapAt τ a b) (monomial m r) = monomial m r := by
  have inj : Function.Injective (swapAt τ a b) :=
    Function.LeftInverse.injective (g := swapAt τ a b) (swapAt_swapAt τ a b)
  suffices hm : m.mapDomain (swapAt τ a b) = m by rw [rename_monomial, hm]
  ext x
  rw [← swapAt_swapAt τ a b x, Finsupp.mapDomain_apply inj, swapAt_swapAt]
  rcases x with ⟨σ, i⟩
  by_cases hσ : σ = τ
  · subst hσ
    by_cases ha : i = a
    · subst ha; simp [swapAt, h]
    · by_cases hb : i = b
      · subst hb; simp [swapAt, h]
      · simp [swapAt, Equiv.swap_apply_of_ne_of_ne ha hb]
  · simp [swapAt, hσ]

theorem eq_zero_of_anti (L : Pol ι N →ₗ[ℝ] ℝ)
    {k : ℕ} (hL : ∀ (τ : ι) (a b : Fin N), (b : ℕ) = a + 1 → ∀ P : Pol ι N, P.IsHomogeneous k →
      L (rename (swapAt τ a b) P) = -L P)
    (hk : k < dimFl ι N) {P : Pol ι N} (hP : P.IsHomogeneous k) : L P = 0 := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg := hP (mem_support_iff.1 hm)
  have hsum : ∑ x, m x = k := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have hsplit : ∑ τ : ι, ∑ i : Fin N, m (τ, i) = k := by
    rw [← Fintype.sum_prod_type']
    exact hsum
  have hlt : ∑ τ : ι, ∑ i : Fin N, m (τ, i) < ∑ _τ : ι, N * (N - 1) / 2 := by
    rw [hsplit, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    unfold dimFl at hk
    exact hk
  obtain ⟨τ, -, hτ⟩ := Finset.exists_lt_of_sum_lt hlt
  have hni : ¬ Function.Injective fun i : Fin N => m (τ, i) := fun hinj =>
    (le_sum_of_injective hinj).not_gt hτ
  obtain ⟨a, b, hab, hne⟩ : ∃ a b : Fin N, m (τ, a) = m (τ, b) ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, h, hne⟩ := hni
    exact ⟨a, b, h, hne⟩
  have hmon : (monomial m (coeff m P)).IsHomogeneous k := isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_weight_one]; exact hdeg)
  rcases lt_or_gt_of_ne hne with h | h
  · have e := anti_swap L hL τ h (monomial m (coeff m P)) hmon
    rw [rename_swapAt_monomial τ hab] at e
    linarith
  · have e := anti_swap L hL τ h (monomial m (coeff m P)) hmon
    rw [rename_swapAt_monomial τ hab.symm] at e
    linarith

section Reduction

open GlobalTheory.FlagForm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem isHomogeneous_rootForm (x : ι × Fin N) : (rootForm x : FormPol ι N).IsHomogeneous 1 := by
  unfold rootForm
  refine (IsHomogeneous.sum _ _ _ fun a _ => ?_).sub (IsHomogeneous.sum _ _ _ fun b _ => ?_)
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _

theorem isHomogeneous_toForm {P : Pol ι N} {k : ℕ} (hP : P.IsHomogeneous k) : (toForm P).IsHomogeneous k := by
  show IsHomogeneous (eval₂ (algebraMap ℝ (FormPol ι N)) rootForm P) k
  have := hP.eval₂ (algebraMap ℝ (FormPol ι N)) rootForm (fun r => isHomogeneous_C _ r) isHomogeneous_rootForm
  rwa [one_mul] at this

theorem isHomogeneous_bcForm (τ : ι) : (bcForm τ : FormPol ι N).IsHomogeneous 1 := by
  unfold bcForm
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  split_ifs
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_zero _ _ _

theorem isHomogeneous_pSum_two (τ : ι) : (pSum τ 2 : Pol ι N).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _

theorem sum_ite_lt (N : ℕ) : ∑ a : Fin N, ∑ b : Fin N, (if a < b then 1 else 0 : ℕ) = N * (N - 1) / 2 := by
  rw [Finset.sum_comm]
  have e (b : Fin N) : ∑ a : Fin N, (if a < b then 1 else 0 : ℕ) = b := by
    rw [Finset.sum_boole, Nat.cast_id, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem weight_volExp : Finsupp.weight 1 (volExp : (ι × Fin N × Fin N) →₀ ℕ) = dimFl ι N := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  have e (p : ι × Fin N × Fin N) : (volExp : (ι × Fin N × Fin N) →₀ ℕ) p = if p.2.1 < p.2.2 then 1 else 0 := rfl
  simp only [e, Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, sum_ite_lt, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

theorem formDeg_eq_zero {ω : FormPol ι N} {k : ℕ} (hω : ω.IsHomogeneous k) (hk : k ≠ dimFl ι N) :
    formDeg ω = 0 := by
  have hv : Finsupp.degree (volExp : (ι × Fin N × Fin N) →₀ ℕ) = dimFl ι N := by
    rw [Finsupp.degree_eq_weight_one]; exact weight_volExp
  rw [formDeg, hω.coeff_eq_zero (fun h => hk (h.symm.trans hv)), zero_div]

noncomputable def defect (hh : Pol ι N →ₗ[ℝ] ℝ) (τ : ι) : Pol ι N →ₗ[ℝ] ℝ where
  toFun Q := hh (pSum τ 2 * Q) - formDeg (bcForm τ * toForm Q)
  map_add' P Q := by
    simp only [mul_add, map_add, toForm, formDeg, coeff_add, add_div]
    ring
  map_smul' c Q := by
    simp only [mul_smul_comm, map_smul, toForm, formDeg, coeff_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem eq_formDeg_of_swap (hh : Pol ι N →ₗ[ℝ] ℝ) (hHh : GlobalTheory.FlagZ.IsHh ι N hh) (τ : ι)
    (hswap : ∀ (σ : ι) (a b : Fin N), (b : ℕ) = a + 1 → ∀ Q : Pol ι N, Q.IsHomogeneous (dimFl ι N - 1) →
      hh (pSum τ 2 * rename (swapAt σ a b) Q) - formDeg (bcForm τ * toForm (rename (swapAt σ a b) Q)) =
        -(hh (pSum τ 2 * Q) - formDeg (bcForm τ * toForm Q)))
    (Q : Pol ι N) : hh (pSum τ 2 * Q) = formDeg (bcForm τ * toForm Q) := by
  suffices h : defect hh τ Q = 0 from sub_eq_zero.1 h
  rw [← sum_homogeneousComponent Q, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := homogeneousComponent_isHomogeneous k Q
  by_cases e : k + 1 = dimFl ι N
  · obtain rfl : k = dimFl ι N - 1 := by omega
    exact eq_zero_of_anti (defect hh τ) (fun σ a b hab P hP => hswap σ a b hab P hP) (by omega) hk
  · show hh _ - formDeg _ = 0
    rw [hHh.eq_zero (d := 2 + k) (by omega) ((isHomogeneous_pSum_two τ).mul hk),
      formDeg_eq_zero ((isHomogeneous_bcForm τ).mul (isHomogeneous_toForm hk)) (by omega), sub_zero]

end Reduction

end GlobalTheory.FlagAnti
