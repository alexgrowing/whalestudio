import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CommuteOmTensRho

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section

variable {ε : Fin n → Bool} {X : GMod n}

theorem stepRho_bdd (A : KAct ε X) (z : ℂ) :
    ∃ C : ℝ, ∀ k x, ‖stepEmb A z (stepRho A z k x)‖ ≤ C * ‖stepEmb A z x‖ := by
  obtain ⟨C, hC⟩ := A.bdd
  refine ⟨n * |C|, fun k x => ?_⟩
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun b => ?_
  rw [stepEmb_apply, stepRho_coe, tensRho_apply, map_sum]
  calc ‖∑ i, A.emb (S7.toMK k b i • A.ρ k ((sv x) i))‖
      ≤ ∑ i, ‖A.emb (S7.toMK k b i • A.ρ k ((sv x) i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, |C| * ‖stepEmb A z x‖ := by
        refine sum_le_sum fun i _ => ?_
        rw [map_smul, norm_smul]
        have h1 := hC k ((sv x) i)
        have h2 : ‖A.emb ((sv x) i)‖ ≤ ‖stepEmb A z x‖ := norm_le_pi_norm (stepEmb A z x) i
        have h3 := kr_entry k b i
        have h4 : C * ‖A.emb ((sv x) i)‖ ≤ |C| * ‖stepEmb A z x‖ :=
          (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg C))
        calc ‖S7.toMK k b i‖ * ‖A.emb (A.ρ k ((sv x) i))‖
            ≤ 1 * ‖A.emb (A.ρ k ((sv x) i))‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ ≤ |C| * ‖stepEmb A z x‖ := by rw [one_mul]; exact h1.trans h4
    _ = n * |C| * ‖stepEmb A z x‖ := by simp [mul_assoc]

theorem stepRho_fin (A : KAct ε X) (z : ℂ) (x : (step X z).V) :
    ∃ W : Submodule ℂ (step X z).V, FiniteDimensional ℂ W ∧ ∀ k, stepRho A z k x ∈ W := by
  choose Wi hWi hmem using fun i => A.fin ((sv x) i)
  let Wt : Submodule ℂ X.V := ⨆ i, Wi i
  let W : Submodule ℂ (step X z).V :=
    Submodule.comap (stepSub X z).subtype (Submodule.pi Set.univ fun _ => Wt)
  refine ⟨W, ?_, fun k => ?_⟩
  · let f : W →ₗ[ℂ] (Fin n → Wt) :=
      { toFun := fun w i => ⟨sv (w : (step X z).V) i, w.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective f fun w w' h => ?_
    apply Subtype.ext; apply sv_inj; funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro b _
    show tensRho A k (sv x) b ∈ Wt
    rw [tensRho_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i (hmem i k))

def stepAct (A : KAct ε X) (z : ℂ) : KAct ε (step X z) where
  N := Fin n → A.N
  emb := stepEmb A z
  inj := stepEmb_inj A z
  ρ := stepRho A z
  compat := stepRho_compat A z
  bdd := stepRho_bdd A z
  fin := stepRho_fin A z

theorem stepCoef_apply' (z : ℂ) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n) (u : (step X z).V)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    stepCoef X z c j u g = ∑ i, g j i * c ((sv u) i) g := rfl

theorem rightEq_step (A : KAct ε X) {I : Type} {c : CoefFam X I} (hc : RightEq A c) (z : ℂ) :
    RightEq (stepAct A z) (X := step X z) (fun p : I × Fin n => stepCoef X z (c p.1) p.2) := by
  intro p u g k
  have hc' : ∀ i v, c i v (S7.toM g * S7.toMK k) = c i (A.ρ k v) (S7.toM g) := fun i v => hc i v g k
  simp only [stepCoef_apply']
  show ∑ i, (S7.toM g * S7.toMK k) p.2 i * c p.1 ((sv u) i) (S7.toM g * S7.toMK k) =
    ∑ l, S7.toM g p.2 l * c p.1 (tensRho A k (sv u) l) (S7.toM g)
  simp only [hc', Matrix.mul_apply, tensRho_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun i _ => by ring

def pathAct : {X : GMod n} → KAct ε X → (χ : Fin n → ℂ) → (ss : List (Fin n)) → KAct ε (path X χ ss)
  | _, A, _, [] => A
  | _, A, χ, s :: ss => pathAct (stepAct A (χ s)) (χ + Pi.single s 1) ss

theorem rightEq_path : ∀ {X : GMod n} (A : KAct ε X) {I : Type} {c : CoefFam X I}, RightEq A c →
    ∀ (χ : Fin n → ℂ) (ss : List (Fin n)),
      RightEq (pathAct A χ ss) (X := path X χ ss) (fun p : I × List (Fin n) => pathCoef X (c p.1) χ ss p.2)
  | _, A, _, c, hc, χ, [] => fun p v g k => hc p.1 v g k
  | X, A, I, c, hc, χ, s :: ss => by
    have h := rightEq_path (stepAct A (χ s)) (rightEq_step A hc (χ s)) (χ + Pi.single s 1) ss
    intro p v g k
    exact h ((p.1, p.2.headD s), p.2.tail) v g k

end

end CompanionTheory.RgExh.Dec.L.WyKR
