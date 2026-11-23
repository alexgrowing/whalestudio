import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Growth

theorem pow_words {A Γ J : Type} [Ring A] [Algebra ℂ A] [Fintype J] (g : Γ → A) (c : J → ℂ)
    (w : J → List Γ) (k : ℕ) :
    (∑ j, c j • ((w j).map g).prod) ^ k =
      ∑ f : Fin k → J, (∏ i, c (f i)) • (((List.ofFn fun i => w (f i)).flatten).map g).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum, ← (Fin.consEquiv fun _ => J).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, List.flatten_cons, List.map_append, List.prod_append, smul_mul_smul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]

theorem trM_add (Φ Ψ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) :
    trM (Φ + Ψ) M = trM Φ M + trM Ψ M := by
  funext y
  simp only [trM, Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem trM_smul (c : ℂ) (Φ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) :
    trM (c • Φ) M = c • trM Φ M := by
  funext y
  simp only [trM, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem trM_zero (M : Matrix ι ι ℂ) : trM (0 : Matrix ι ι (H E a b → ℂ)) M = 0 := by
  funext y
  simp [trM]

theorem trM_sum {J : Type} (s : Finset J) (c : J → ℂ) (Φ : J → Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) :
    trM (∑ j ∈ s, c j • Φ j) M = ∑ j ∈ s, c j • trM (Φ j) M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact trM_zero M
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, trM_add, trM_smul, ih]

end Growth

theorem blkGrowth (h1 : BlockOperatorsProductAdjoint) (h2 : BlockWordOperators) (h3 : BlockLinearCombinations) (h4 : EllLin) : BlockEllipticGrowth := by
  intro E _ _ _ _ B _ _ _ _ μ₁ _ μ₂ _ hG M t₁ t₂ J _ c w c₀ hc₀ ht₁ ht₂ hw
  obtain ⟨R, hR0, hRs⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ s : PT B, (s = t₁ ∨ ∃ j, Sum.inr s ∈ w j) → s.T ≤ R ∧ s.r + B.c ≤ R := by
    let gB : BGen B → ℝ := Sum.elim (fun _ => 0) fun s => |s.T| + |s.r + B.c|
    have gB0 : ∀ g, 0 ≤ gB g := by
      rintro (x | s)
      · exact le_refl 0
      · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hl0 : ∀ j, ∀ x ∈ (w j).map gB, 0 ≤ x := fun j x hx => by
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      exact gB0 g
    have hs0 : 0 ≤ ∑ j, ((w j).map gB).sum := Finset.sum_nonneg fun j _ => List.sum_nonneg (hl0 j)
    refine ⟨gB (Sum.inr t₁) + ∑ j, ((w j).map gB).sum, add_nonneg (gB0 _) hs0, fun s hs => ?_⟩
    have key : gB (Sum.inr s) ≤ gB (Sum.inr t₁) + ∑ j, ((w j).map gB).sum := by
      rcases hs with rfl | ⟨j, hj⟩
      · linarith
      · have e1 : gB (Sum.inr s) ≤ ((w j).map gB).sum := List.single_le_sum (hl0 j) _ (List.mem_map.2 ⟨_, hj, rfl⟩)
        have e2 : ((w j).map gB).sum ≤ ∑ j, ((w j).map gB).sum :=
          Finset.single_le_sum (f := fun j => ((w j).map gB).sum) (fun j _ => List.sum_nonneg (hl0 j)) (Finset.mem_univ j)
        linarith [gB0 (Sum.inr t₁)]
    have e : gB (Sum.inr s) = |s.T| + |s.r + B.c| := rfl
    constructor <;> linarith [le_abs_self s.T, le_abs_self (s.r + B.c), abs_nonneg s.T, abs_nonneg (s.r + B.c)]
  obtain ⟨L, hL⟩ : ∃ L : ℕ, ∀ j, (w j).length ≤ L :=
    ⟨Finset.univ.sup fun j => (w j).length, fun j => Finset.le_sup (f := fun j => (w j).length) (Finset.mem_univ j)⟩
  have hr₀ : 0 ≤ c₀ * (1 + t₂.T + R) + t₂.r + R := by
    have := mul_nonneg hc₀ (by linarith [ht₂.T] : 0 ≤ 1 + t₂.T + R)
    linarith [ht₂.r]
  have hr₁ : 0 ≤ (c₀ + 1) * L * R := mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hR0
  obtain ⟨C, N, hCN⟩ := hG t₁.Φ t₂.Φ t₁.op t₂.op M _ _ (h1 E B t₁ t₁ ht₁ ht₁).1 (h1 E B t₂ t₂ ht₂ ht₂).1
    (h1 E B t₁ t₁ ht₁ ht₁).2.1 (h1 E B t₂ t₂ ht₂ ht₂).2.1 hr₀ hr₁
  refine ⟨C, N, fun k hk => ?_⟩
  have hf : ∀ f : Fin k → J,
      IsTestM (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ ∧
      IsROp B.D (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ
        (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op ∧
      BGen.sc (List.ofFn fun i => w (f i)).flatten • (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op =
        t₁.op * (((List.ofFn fun i => w (f i)).flatten).map BGen.op).prod * t₂.op ∧
      D4.IsTest2J (trM (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ M)
        (c₀ * (1 + t₂.T + R) + t₂.r + R + k * ((c₀ + 1) * L * R)) := by
    intro f
    have hmem : ∀ g ∈ (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten), BGen.Ok g := by
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ht₁
      · obtain ⟨l, hl, hgl⟩ := List.mem_flatten.1 hg
        rw [List.mem_ofFn] at hl
        obtain ⟨i, rfl⟩ := hl
        exact hw (f i) g hgl
    have hRw : ∀ s, Sum.inr s ∈ (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) → s.T ≤ R ∧ s.r + B.c ≤ R := by
      intro s hs
      apply hRs s
      rcases List.mem_cons.1 hs with h | h
      · exact Or.inl (Sum.inr_injective h)
      · obtain ⟨l, hl, hgl⟩ := List.mem_flatten.1 h
        rw [List.mem_ofFn] at hl
        obtain ⟨i, rfl⟩ := hl
        exact Or.inr ⟨f i, hgl⟩
    obtain ⟨ok, hop, hT, hr, -, -⟩ := h2 E B _ t₂ R hmem ht₂ hR0 hRw
    have hlenN : ((List.ofFn fun i => w (f i)).flatten).length ≤ k * L := by
      rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
      refine (Finset.sum_le_sum fun i _ => ?_).trans (le_of_eq (by simp : ∑ _i : Fin k, L = k * L))
      exact hL (f i)
    have hlen : ((Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten).length : ℝ) ≤ 1 + k * L := by
      have := (Nat.cast_le (α := ℝ)).2 hlenN
      push_cast at this
      simp only [List.length_cons]
      push_cast
      linarith
    refine ⟨(h1 E B _ _ ok ok).1, (h1 E B _ _ ok ok).2.1, ?_, ?_⟩
    · have e := Word.sc_inr t₁ (List.ofFn fun i => w (f i)).flatten
      rw [← e, ← hop, List.map_cons, List.prod_cons]
      rfl
    · apply CG.isTest2J_mono (hk f _ rfl)
      have a1 := mul_le_mul_of_nonneg_right hlen hR0
      have a2 := mul_le_mul_of_nonneg_left
        (hT.trans (by linarith : t₂.T + _ * R ≤ t₂.T + (1 + k * L) * R)) hc₀
      linarith
  have hsum := h3 E B.a B.b B.D B.I (Fin k → J) Finset.univ
    (fun f => (∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten)
    (fun f => (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ)
    (fun f => (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op) (fun f _ => ⟨(hf f).1, (hf f).2.1⟩)
  have hopEq : ∑ f : Fin k → J, ((∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten) •
      (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op =
      t₁.op * (∑ j, c j • ((w j).map BGen.op).prod) ^ k * t₂.op := by
    rw [Growth.pow_words, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [mul_smul, (hf f).2.2.1, mul_smul_comm, smul_mul_assoc]
  have hrop : IsROp B.D (∑ f : Fin k → J, ((∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten) •
      (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ) (t₁.op * (∑ j, c j • ((w j).map BGen.op).prod) ^ k * t₂.op) := by
    rw [← hopEq]
    exact hsum.2
  have htest := CG.isTest2J_sum (Finset.univ : Finset (Fin k → J)) fun f _ =>
    CG.isTest2J_smul ((∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten) (hf f).2.2.2
  rw [← Growth.trM_sum] at htest
  have hb := hCN k _ _ hsum.1 hrop htest
  have hnn : 0 ≤ c₀ * (1 + t₂.T + R) + t₂.r + R + k * ((c₀ + 1) * L * R) :=
    add_nonneg hr₀ (mul_nonneg (Nat.cast_nonneg _) hr₁)
  rw [Growth.trM_sum, h4 E B.a B.b μ₁ μ₂ (Fin k → J) Finset.univ _ _ _ hnn fun f _ => (hf f).2.2.2] at hb
  exact hb

end PositivityTheory.Rg.BcB.F

end
