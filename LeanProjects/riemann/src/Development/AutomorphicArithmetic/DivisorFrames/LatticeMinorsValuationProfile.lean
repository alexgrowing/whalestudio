import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem UpperTheory.mulVec_of_trailing_zeros {K : Type} [Field K] {n r : ℕ} (P : Matrix (Fin n) (Fin r) K) (i : Fin r)
    (cf : Fin r → K) (h : ∀ k, i < k → cf k = 0) (ρ : Fin n) :
    (P *ᵥ cf) ρ = ∑ j : Fin ((i : ℕ) + 1), P ρ (Fin.castLE i.2 j) * cf (Fin.castLE i.2 j) := by
  symm
  rw [Matrix.mulVec, dotProduct]
  refine Fintype.sum_of_injective (Fin.castLE i.2) (Fin.castLE_injective _) _ _ ?_ fun _ => rfl
  intro l hl
  rw [h l, mul_zero]
  by_contra hc
  have : (l : ℕ) ≤ i := not_lt.1 hc
  exact hl ⟨⟨l, by omega⟩, rfl⟩

private theorem UpperTheory.exists_vector_of_minor_cofactors {K : Type} [Field K] {n r : ℕ} (P : Matrix (Fin n) (Fin r) K) (i : Fin r)
    (σ : Fin (i : ℕ) → Fin n) : ∃ c : Fin r → K, c i = colMinor P i i.2.le σ ∧ (∀ k, i < k → c k = 0) ∧
      ∀ ρ, (P *ᵥ c) ρ = colMinor P (i + 1) i.2 (Fin.snoc (α := fun _ => Fin n) σ ρ) := by
  have hz : ∀ k : Fin r, i < k → (if hl : (k : ℕ) < (i : ℕ) + 1 then (-1) ^ ((i : ℕ) + (k : ℕ)) *
      (Matrix.of fun a b : Fin (i : ℕ) => P (σ a) (Fin.castLE i.2 ((⟨k, hl⟩ : Fin ((i : ℕ) + 1)).succAbove b))).det
        else (0 : K)) = 0 := by
    intro k hk
    have : (i : ℕ) < k := hk
    rw [dif_neg (by omega)]
  refine ⟨fun l => if hl : (l : ℕ) < (i : ℕ) + 1 then (-1) ^ ((i : ℕ) + (l : ℕ)) *
      (Matrix.of fun a b : Fin (i : ℕ) => P (σ a) (Fin.castLE i.2 ((⟨l, hl⟩ : Fin ((i : ℕ) + 1)).succAbove b))).det
        else 0, ?_, hz, ?_⟩
  · simp only [Nat.lt_succ_self, dif_pos]
    rw [Even.neg_one_pow (Even.add_self _), _root_.one_mul]
    unfold colMinor
    congr 1
    ext a l
    have : (⟨i, Nat.lt_succ_self _⟩ : Fin ((i : ℕ) + 1)) = Fin.last _ := rfl
    simp only [Matrix.of_apply, this, Fin.succAbove_last]
    rfl
  · intro ρ
    rw [UpperTheory.mulVec_of_trailing_zeros P i _ hz]
    unfold colMinor
    rw [Matrix.det_succ_row _ (Fin.last (i : ℕ))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : ((Fin.castLE i.2 j : Fin r) : ℕ) < (i : ℕ) + 1 := j.2
    have h : (Matrix.of fun a l : Fin ((i : ℕ) + 1) =>
        P (Fin.snoc (α := fun _ => Fin n) σ ρ a) (Fin.castLE i.2 l)).submatrix
          (Fin.last (i : ℕ)).succAbove j.succAbove =
        Matrix.of fun a l : Fin (i : ℕ) => P (σ a) (Fin.castLE i.2 (j.succAbove l)) := by
      ext a l
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.snoc_castSucc]
    rw [h, dif_pos hj]
    simp only [Matrix.of_apply, Fin.val_last, Fin.snoc_last, Fin.val_castLE, Fin.eta]
    ring

private theorem UpperTheory.colMinor_cramer_expansion {K : Type} [Field K] {n r : ℕ} (P : Matrix (Fin n) (Fin r) K) (i : Fin r)
    (cf : Fin r → K) (h : ∀ k, i < k → cf k = 0) (σ : Fin ((i : ℕ) + 1) → Fin n) :
    colMinor P (i + 1) i.2 σ * cf i = ∑ a : Fin ((i : ℕ) + 1), (-1) ^ ((a : ℕ) + (i : ℕ)) *
      colMinor P i i.2.le (fun b => σ (a.succAbove b)) * (P *ᵥ cf) (σ a) := by
  set M : Matrix (Fin ((i : ℕ) + 1)) (Fin ((i : ℕ) + 1)) K := Matrix.of fun a l => P (σ a) (Fin.castLE i.2 l) with hM
  have h1 : M *ᵥ (fun j => cf (Fin.castLE i.2 j)) = fun a => (P *ᵥ cf) (σ a) := by
    funext a
    rw [UpperTheory.mulVec_of_trailing_zeros P i cf h]
    rfl
  have h2 : (M.adjugate *ᵥ (M *ᵥ (fun j => cf (Fin.castLE i.2 j)))) (Fin.last _) = M.det * cf i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  change M.det * cf i = _
  rw [← h2, h1, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  congr 2
  unfold colMinor
  congr 1
  ext b l
  simp only [hM, Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last]
  rfl

private theorem UpperTheory.exists_nonzero_colMinor_of_injective {K : Type} [Field K] {n r : ℕ} (P : Matrix (Fin n) (Fin r) K)
    (hP : ∀ cf, P *ᵥ cf = 0 → cf = 0) : ∀ k (hk : k ≤ r), ∃ σ, colMinor P k hk σ ≠ 0 := by
  intro k
  induction k with
  | zero => intro hk; exact ⟨Fin.elim0, by simp [colMinor]⟩
  | succ k ih =>
    intro hk
    obtain ⟨σ, hσ⟩ := ih (by omega)
    obtain ⟨c, h1, -, h3⟩ := UpperTheory.exists_vector_of_minor_cofactors P ⟨k, hk⟩ σ
    by_contra hc
    push Not at hc
    have : c = 0 := hP c (funext fun ρ => (h3 ρ).trans (hc _))
    exact hσ (by rw [← h1, this]; rfl)

theorem UpperTheory.lattice_minors_valuation_profile :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X) (n r : ℕ) (u : Fin r → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (P : Matrix (Fin n) (Fin r) ℂ_[p]) (δ : ℂ_[p]), δ ≠ 0 → (∀ cf, P *ᵥ cf = 0 → cf = 0) → (∀ cf, cf ∈ latCo t p x u ↔ ∀ k, ‖(P *ᵥ cf) k‖ ≤ ‖δ‖) → ∃ ν : ℕ → ℝ, (∀ k, k ≤ r → 0 < ν k) ∧ (∀ i : Fin r, Real.log (GlobalTheory.ShFam.Pad.grNorm t x (latHT t p x) u i) = Real.log (ν ((i : ℕ) + 1)) - Real.log (ν (i : ℕ)) - Real.log ‖δ‖) ∧ (∀ k (hk : k ≤ r) σ, ‖colMinor P k hk σ‖ ≤ ν k) ∧ ∀ k (hk : k ≤ r), ∃ σ, ‖colMinor P k hk σ‖ = ν k := by
  intro E _ _ _ H X t p _ x n r u P δ hδ hP hL
  have hex : ∀ k, ∃ ν : ℝ, ∀ hk : k ≤ r, 0 < ν ∧ (∀ σ, ‖colMinor P k hk σ‖ ≤ ν) ∧ ∃ σ, ‖colMinor P k hk σ‖ = ν := by
    intro k
    by_cases hk : k ≤ r
    · obtain ⟨σ₀, h₀⟩ := UpperTheory.exists_nonzero_colMinor_of_injective P hP k hk
      obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image Finset.univ (fun σ => ‖colMinor P k hk σ‖) ⟨σ₀, Finset.mem_univ _⟩
      exact ⟨_, fun _ => ⟨(norm_pos_iff.2 h₀).trans_le (hσ _ (Finset.mem_univ _)),
        fun σ' => hσ _ (Finset.mem_univ _), σ, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose ν hν using hex
  refine ⟨ν, fun k hk => (hν k hk).1, fun i => ?_, fun k hk => (hν k hk).2.1, fun k hk => (hν k hk).2.2⟩
  obtain ⟨h0, hle0, σ0, he0⟩ := hν i i.2.le
  obtain ⟨h1, hle1, σ1, he1⟩ := hν (i + 1) i.2
  have hd : 0 < ‖δ‖ := norm_pos_iff.2 hδ
  have key : GlobalTheory.ShFam.Pad.grNorm t x (latHT t p x) u i = ν (i + 1) / (ν i * ‖δ‖) := by
    unfold GlobalTheory.ShFam.Pad.grNorm
    apply IsLeast.csInf_eq
    constructor
    · obtain ⟨c, c1, c2, c3⟩ := UpperTheory.exists_vector_of_minor_cofactors P i σ0
      have hn : ‖((δ / colMinor P (i + 1) i.2 σ1) • c) i‖ = ‖δ‖ / ν (i + 1) * ν i := by
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_div, he1, c1, he0]
      refine ⟨(δ / colMinor P (i + 1) i.2 σ1) • c, ?_, fun k hk => ?_, (hL _).2 fun ρ => ?_, ?_⟩
      · rw [← norm_pos_iff, hn]
        positivity
      · rw [Pi.smul_apply, c2 k hk, smul_zero]
      · rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_div, he1, c3]
        calc _ ≤ ‖δ‖ / ν (i + 1) * ν (i + 1) := by gcongr; exact hle1 _
          _ = ‖δ‖ := div_mul_cancel₀ _ h1.ne'
      · rw [hn]
        field_simp
    · rintro _ ⟨cf, c1, c2, c3, rfl⟩
      have c4 := (hL cf).1 c3
      have c5 : ν (i + 1) * ‖cf i‖ ≤ ν i * ‖δ‖ := by
        rw [← he1, ← norm_mul, UpperTheory.colMinor_cramer_expansion P i cf c2 σ1]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun a _ => ?_
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, _root_.one_mul]
        exact mul_le_mul (hle0 _) (c4 _) (norm_nonneg _) h0.le
      have c6 : 0 < ‖cf i‖ := norm_pos_iff.2 c1
      rw [div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ c6]
      exact c5
  rw [key, Real.log_div h1.ne' (by positivity), Real.log_mul h0.ne' hd.ne']
  ring
