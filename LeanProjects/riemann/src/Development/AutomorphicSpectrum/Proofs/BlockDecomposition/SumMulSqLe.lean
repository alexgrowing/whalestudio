import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf

open MeasureTheory
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.DualVectorFamily

theorem sum_mul_sq_le {κ : Type} (s : Finset κ) (p q : κ → ℝ≥0∞) (t : ℝ≥0∞) (h : ∀ l ∈ s, q l ^ 2 ≤ t) :
    (∑ l ∈ s, p l * q l) ^ 2 ≤ (∑ l ∈ s, p l) ^ 2 * t := by
  have hs : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hq : ∀ l ∈ s, q l ≤ t ^ (1 / 2 : ℝ) := by
    intro l hl
    have := h l hl
    rw [← hs] at this
    exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 this
  calc (∑ l ∈ s, p l * q l) ^ 2 ≤ ((∑ l ∈ s, p l) * t ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun l hl => by gcongr; exact hq l hl
    _ = (∑ l ∈ s, p l) ^ 2 * t := by rw [mul_pow, hs]

theorem abs_vecs (hKB : KerBasic) (hKL : KerLin) (hCB : CntBasic) (hVE : VecEx) (hVN : VecNorm)
    (hVI : VecInner) (hPt : PtEq) (X : Ctx) (th : X.G → X.G) (hth : Continuous th)
    (hcnt : ∀ (Ω : Set X.G) x, cnt X.Γ Ω (th x) = cnt X.Γ (th '' Ω) x)
    {ι : Type} [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ : X.Hs ι →L[ℂ] X.Hs ι)
    (M : Matrix ι ι ℂ) (t₁ : ∀ i j, Tst (Φ₁ i j)) (t₂ : ∀ i j, Tst (Φ₂ i j))
    (o₁ : X.IsOp Φ₁ T₁) (o₂ : X.IsOp Φ₂ T₂) :
    ∃ k₁ k₂ : X.G → ι → X.Hs ι,
      (∀ i, Continuous (fun x => k₁ x i) ∧ Continuous fun x => k₂ x i) ∧
      (∀ x i (u : X.Hs ι), inner ℂ (k₁ x i) u = ∑ j, ∫ y, ker X.Γ (Φ₁ i j) x y * (u j : X.G → ℂ) y ∂X.ν) ∧
      (∀ x i (u : X.Hs ι), inner ℂ u (k₂ x i) =
        ∑ j, ∑ l, ∫ y, starRingEnd ℂ ((u j : X.G → ℂ) y) * ker X.Γ (Φ₂ j l) y (th x) * M l i ∂X.ν) ∧
      (∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ x i,
        ‖k₁ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x ∧ ‖k₂ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x) ∧
      (∀ (U : X.Hs ι →L[ℂ] X.Hs ι) (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
        X.IsOp Φ (T₁ * U * T₂) → ∀ x,
          ker X.Γ (fun y => ∑ i, ∑ j, Φ i j y * M j i) x (th x) =
            ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))) := by
  have tA : ∀ i j, Tst ((fun i j => adj (Φ₁ j i) : Matrix ι ι (X.G → ℂ)) i j) :=
    fun i j => (hKB X _ (t₁ j i)).2.2.2.1
  obtain ⟨k₁, c₁, v₁⟩ := hVE X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨k, c, v⟩ := hVE X ι Φ₂ t₂
  obtain ⟨C₁, Ω₁, C₁t, Ω₁c, n₁⟩ := hVN X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨C₂, Ω₂, C₂t, Ω₂c, n₂⟩ := hVN X ι Φ₂ t₂
  refine ⟨k₁, fun x i => ∑ l, M l i • k (th x) l, fun i => ⟨c₁ i, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact continuous_finset_sum _ fun l _ => ((c l).comp hth).const_smul (M l i)
  · intro x i u
    exact (hVI X ι Φ₁ x i (k₁ x i) u t₁).2 (v₁ x i)
  · intro x i u
    rw [inner_sum]
    simp only [inner_smul_right, (hVI X ι Φ₂ (th x) _ (k (th x) _) u t₂).1 (v _ _), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, mul_comm]
  · set P : ℝ≥0∞ := ∑ i, (∑ l, ‖M l i‖ₑ) ^ 2 with hP
    have Pt : P ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.pow_ne_top (ENNReal.sum_ne_top.2 fun l _ => enorm_ne_top)
    refine ⟨C₁ + P * C₂, Ω₁ ∪ th '' Ω₂, ENNReal.add_ne_top.2 ⟨C₁t, ENNReal.mul_ne_top Pt C₂t⟩,
      Ω₁c.union (Ω₂c.image hth), fun x i => ⟨?_, ?_⟩⟩
    · calc ‖k₁ x i‖ₑ ^ 2 ≤ C₁ * cnt X.Γ Ω₁ x := n₁ x i _ (v₁ x i)
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          · exact le_self_add
          · exact (hCB X).2.2.1 _ _ Set.subset_union_left x
    · have hb : ∀ l ∈ (Finset.univ : Finset ι), ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
        intro l _
        calc ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ Ω₂ (th x) := n₂ _ l _ (v _ l)
          _ = C₂ * cnt X.Γ (th '' Ω₂) x := by rw [hcnt]
          _ ≤ _ := by
            gcongr
            exact (hCB X).2.2.1 _ _ Set.subset_union_right x
      have hsum : ‖∑ l, M l i • k (th x) l‖ₑ ≤ ∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ := by
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [enorm_smul]
      calc ‖∑ l, M l i • k (th x) l‖ₑ ^ 2 ≤ (∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ) ^ 2 := by gcongr
        _ ≤ (∑ l, ‖M l i‖ₑ) ^ 2 * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := sum_mul_sq_le _ _ _ _ hb
        _ ≤ P * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := by
          gcongr
          exact Finset.single_le_sum (f := fun i => (∑ l, ‖M l i‖ₑ) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ i)
        _ = P * C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by rw [mul_assoc]
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          exact le_add_self
  · intro U Φ tΦ oΦ x
    have hfun : (fun y => ∑ i, ∑ j, Φ i j y * M j i) =
        fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
      funext y
      rw [Fintype.sum_prod_type]
    rw [hfun, (hKL X (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) fun p => tΦ _ _).2,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, inner_smul_right,
      hPt X ι Φ₁ Φ₂ Φ T₁ T₂ U t₁ t₂ tΦ o₁ o₂ oΦ x (th x) i l (k₁ x i) (k (th x) l) (v₁ x i) (v _ l),
      mul_comm]

theorem vecsEx_of : RatProper → KerBasic → KerLin → CntBasic → CntPair → VecEx → VecNorm → VecInner → PtEq →
    VecsEx := by
  intro hR hKB hKL hCB hCP hVE hVN hVI hPt E _ _ _ a b D ι _ Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  obtain ⟨k₁, k₂, c, r₁, r₂, n, d⟩ := abs_vecs hKB hKL hCB hVE hVN hVI hPt (ctx hR D) th
    (hCP E a b).2.1 (hCP E a b).1 Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  refine ⟨k₁, k₂, ⟨c, r₁, r₂, n, ?_⟩⟩
  intro U Φ hΦ hop x
  rw [(hCP E a b).2.2]
  exact d U Φ hΦ hop x

end GlobalTheory.CompanionTheory.DualVectorFamily

end
