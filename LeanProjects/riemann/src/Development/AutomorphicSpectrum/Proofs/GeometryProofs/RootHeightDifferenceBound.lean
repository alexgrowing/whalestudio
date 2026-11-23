import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalBoundHeightCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.CloseHt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

section Places

variable {L : Type} [Field L] [NumberField L]

lemma log_sup_support {ι : Type} [Fintype ι] (x : ι → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := by
  classical
  obtain ⟨i₀, hi₀⟩ := hx
  haveI : Nonempty ι := ⟨i₀⟩
  have hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0),
      Function.mulSupport fun v : FinitePlace L => v (x i)).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_
    exact FinitePlace.mulSupport_finite (by simpa using hi)
  refine hS.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ i, x i ≠ 0 → v (x i) = 1 := by
    intro i hi
    by_contra h
    exact hn (Set.mem_biUnion (by simpa using hi) h)
  have h2 : ∀ i, v (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h1 i hi).le
  have h3 : (⨆ i, v (x i)) = 1 := by
    have hle : (⨆ i, v (x i)) ≤ 1 := ciSup_le h2
    have hge : (1 : ℝ) ≤ ⨆ i, v (x i) := by
      have hb : BddAbove (Set.range fun i => v (x i)) := (Set.finite_range _).bddAbove
      calc (1 : ℝ) = v (x i₀) := (h1 i₀ hi₀).symm
        _ ≤ _ := le_ciSup hb i₀
    exact le_antisymm hle hge
  simp [h3]

lemma block_support {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (a : K → ℝ)
    (x : ∀ k, ι k → L) (hx : ∀ k, ∃ i, x k i ≠ 0) :
    (Function.support fun v : FinitePlace L => ∑ k, a k * Real.log (⨆ i, v (x k i))).Finite := by
  refine (Set.finite_iUnion fun k => log_sup_support (x k) (hx k)).subset fun v hv => ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_iUnion.2 ⟨k, right_ne_zero_of_mul hk⟩

lemma avg_mem (S : (L →+* ℂ) → ℝ) {lo hi : ℝ} (h : ∀ σ, S σ ∈ Set.Icc lo hi) :
    (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ, S σ ∈ Set.Icc lo hi := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∀ r : ℝ, ∑ _σ : L →+* ℂ, r = Module.finrank ℚ L * r := fun r => by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  have h1 : Module.finrank ℚ L * lo ≤ ∑ σ, S σ := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).1
  have h2 : ∑ σ, S σ ≤ Module.finrank ℚ L * hi := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).2
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hd]
    linarith
  · rw [inv_mul_eq_div, div_le_iff₀ hd]
    linarith

end Places

section Join

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]

lemma ptHt_sub_join (a₁ : K₁ → ℝ) (a₂ : K₂ → ℝ) (φ₁ : ((Σ k, ι₁ k) → ℂ) → ℝ) (φ₂ : ((Σ k, ι₂ k) → ℂ) → ℝ)
    (L : Type) [Field L] [NumberField L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ptHt a₁ φ₁ L (fun p => z (joinInl ι₁ ι₂ p)) - ptHt a₂ φ₂ L (fun p => z (joinInr ι₁ ι₂ p)) =
      ptHt (Sum.elim a₁ (-a₂))
        (fun Z => φ₁ (fun p => Z (joinInl ι₁ ι₂ p)) - φ₂ (fun p => Z (joinInr ι₁ ι₂ p))) L z := by
  unfold ptHt
  rw [← mul_sub]
  congr 1
  have s₁ := block_support (L := L) (ι := ι₁) a₁ (fun k i => z (joinInl ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inl k))
  have s₂ := block_support (L := L) (ι := ι₂) a₂ (fun k i => z (joinInr ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inr k))
  have e : (∑ᶠ v : FinitePlace L, ∑ k, Sum.elim a₁ (-a₂) k * Real.log (⨆ i, v (z ⟨k, i⟩))) =
      (∑ᶠ v : FinitePlace L, ∑ k, a₁ k * Real.log (⨆ i, v (z (joinInl ι₁ ι₂ ⟨k, i⟩)))) -
        ∑ᶠ v : FinitePlace L, ∑ k, a₂ k * Real.log (⨆ i, v (z (joinInr ι₁ ι₂ ⟨k, i⟩))) := by
    rw [← finsum_sub_distrib s₁ s₂]
    refine finsum_congr fun v => ?_
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rfl
  rw [e]
  simp only [Finset.sum_sub_distrib]
  simp only [joinInl, joinInr]
  ring

end Join

section Embed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {L : Type} [Field L]

lemma aeval_emb (σ : L →+* ℂ) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (comp_aeval_apply (R := ℤ) (f := z) σ.toIntAlgHom f).symm

lemma ptsOver_emb (σ : L →+* ℂ) {P : Ideal (MRing ι)} {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) :
    (fun p => σ (z p)) ∈ ptsOver ℂ P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_emb, hz.2 f hf, map_zero]

lemma hasVal_emb (σ : L →+* ℂ) {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {z : (Σ k, ι k) → L} {w : L}
    (h : HasVal y a u z w) : HasVal y a u (fun p => σ (z p)) (σ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, h0, h1⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_emb]
    exact (map_ne_zero σ).2 h0
  · rw [aeval_emb, aeval_emb, h1, map_mul]

end Embed

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

lemma line_a (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp [RootModel.line, M.x_deg]

lemma coef_eq {M R : RootModel Ψ N} (h : M.kA = R.kA) (lam : Wt Ψ N) (s : ℝ) (j : Option (Ψ × Fin N)) :
    M.coef lam s j = R.coef lam s j := by
  cases j with
  | none => simp [RootModel.coef, h]
  | some r => rfl

lemma sum_abs_coef (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) :
    ∑ j, |M.coef lam s j| ≤ l1 lam + |s| := by
  rw [Fintype.sum_option, add_comm]
  have h1 : |M.coef lam s none| ≤ |s| := by
    have hk : (1 : ℝ) ≤ M.kA := by exact_mod_cast M.kA_pos
    simp only [RootModel.coef]
    rw [abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg s) hk
  have h2 : ∑ r : Ψ × Fin N, |M.coef lam s (some r)| = l1 lam := by
    simp [RootModel.coef, l1, Fintype.sum_prod_type]
  linarith

def lineDefect (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    ((Σ k, joinIdx M.ι R.ι k) → ℂ) → ℝ := fun Z =>
  Real.log ((M.line t j).h fun p => Z (joinInl M.ι R.ι p)) -
    Real.log ((R.line 1 j).h fun p => Z (joinInr M.ι R.ι p))

lemma lineHt_sub (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) (L : Type) [Field L] [NumberField L]
    (z : (Σ k, joinIdx M.ι R.ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
        lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p)) =
      ptHt (fun k => (joinDeg M R j k : ℝ)) (lineDefect M R t j) L z := by
  unfold lineHt
  rw [ptHt_sub_join _ _ _ _ L z hz]
  have e : (Sum.elim (fun k => ((M.line t j).a k : ℝ)) (-fun k => ((R.line 1 j).a k : ℝ))) =
      fun k => (joinDeg M R j k : ℝ) := by
    funext k
    cases k with
    | inl k => simp [joinDeg, line_a M t j]
    | inr k => simp [joinDeg]
  rw [e]
  rfl

theorem close_ht (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω)
    (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N) (hC : Close M R i u c)
    (hA : ArchBetween M R i u t lam s lo hi) (L : Type) [Field L] [NumberField L]
    (z) (hz : z ∈ ptsOver L (mCoordIdeal (joinOf M R i))) :
    rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈
      Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  obtain ⟨harith, hbir, -, -⟩ := GlobalTheory.T.join_model_points_project Ψ N M R i
  choose val hval0 hval using fun j => hC.unit j L z hz
  have hc : 0 ≤ c := by
    obtain ⟨-, q, m, hq, -, hlog, -, -⟩ := hC.vert none
    have h0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    exact (mul_nonneg_iff_of_pos_left hq').1 (h0.trans hlog)

  let E : Option (Ψ × Fin N) → ℝ := fun j => (Module.finrank ℚ L : ℝ)⁻¹ *
    ∑ σ : L →+* ℂ, (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖)
  let D : Option (Ψ × Fin N) → ℝ := fun j => lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
    lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p))
  have hD : ∀ j, |D j - E j| ≤ c := by
    intro j
    have := GlobalTheory.T.vertical_bound_height_compare (M.K ⊕ R.K) (joinIdx M.ι R.ι) M.Ω (joinOf M R i) (dimFl Ψ N + 1) harith hbir
      (joinDeg M R j) (u j) c (hC.vert j) (lineDefect M R t j) L z hz (val j) (hval0 j) (hval j)
    simp only [D, E]
    rw [lineHt_sub M R t j L z hz.1]
    exact this
  have hE : ∑ j, M.coef lam s j * E j ∈ Set.Icc lo hi := by
    have e : ∑ j, M.coef lam s j * E j = (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, ∑ j, M.coef lam s j *
        (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖) := by
      simp only [E]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e]
    refine avg_mem _ fun σ => ?_
    exact hA _ (ptsOver_emb σ hz) (fun j => σ (val j)) fun j => hasVal_emb σ (hval j)
  have hsplit : rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) -
      rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) =
      ∑ j, M.coef lam s j * E j + ∑ j, M.coef lam s j * (D j - E j) := by
    unfold rootHt
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← coef_eq hC.kA lam s j]
    simp only [D]
    ring
  have hb : |∑ j, M.coef lam s j * (D j - E j)| ≤ (l1 lam + |s|) * c := by
    calc |∑ j, M.coef lam s j * (D j - E j)| ≤ ∑ j, |M.coef lam s j * (D j - E j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M.coef lam s j| * c := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hD j) (abs_nonneg _)
      _ = (∑ j, |M.coef lam s j|) * c := by rw [Finset.sum_mul]
      _ ≤ (l1 lam + |s|) * c := mul_le_mul_of_nonneg_right (sum_abs_coef M lam s) hc
  rw [hsplit]
  have := abs_le.1 hb
  exact ⟨by linarith [hE.1, this.1], by linarith [hE.2, this.2]⟩

end GlobalTheory.CompanionTheory.Ar.Ht.CloseHt
