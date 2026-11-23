import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltedPointsCoveredByRepresentativeCellsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem biInv_eq_of_cells {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]
    {R K : ∀ i, Subgroup (H i)} {q : (∀ i, H i) → ℂ} :
    ∀ (l : List ι), BiInv R K l q → ∀ h h' : (∀ i, H i), (∀ i, i ∉ l → h i = h' i) →
      (∀ i ∈ l, ∃ r ∈ R i, ∃ k ∈ K i, h i = r * h' i * k) → q h = q h'
  | [], _, h, h', h1, _ => by
      have : h = h' := funext fun i => h1 i List.not_mem_nil
      rw [this]
  | i :: l, hq, h, h', h1, h2 => by
      obtain ⟨r, hr, k, hk, e⟩ := h2 i List.mem_cons_self
      have hq' : BiInv R K l q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
      set h₁ := Function.update h i (h' i) with hh₁
      have hi₁ : h₁ i = h' i := by simp [hh₁]
      have step1 : q h = q h₁ := by
        have a1 := (hq i List.mem_cons_self (Function.update h₁ i (h' i * k))).1 r hr
        have a2 := (hq i List.mem_cons_self h₁).2 k hk
        simp only [Function.update_self, Function.update_idem] at a1
        rw [hi₁] at a2
        have hh : h = Function.update h₁ i (r * (h' i * k)) := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [e, mul_assoc]
          · simp [hh₁, Function.update_of_ne hj]
        rw [hh, a1, a2]
      rw [step1]
      refine biInv_eq_of_cells l hq' h₁ h' (fun j hj => ?_) (fun j hj => ?_)
      · by_cases hji : j = i
        · subst hji; exact hi₁
        · rw [hh₁, Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · by_cases hji : j = i
        · subst hji; exact ⟨1, one_mem _, 1, one_mem _, by simp [hi₁]⟩
        · rw [hh₁, Function.update_of_ne hji]
          exact h2 j (List.mem_cons_of_mem _ hj)

theorem zero_not_mem_idx (D : D7) : 0 ∉ idx D := by simp [idx, List.mem_range']; intro x _; omega

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem evT_eq_zero_of (C : BiFam ch.G) (j : ℕ) (hj : Even j) (hjm : j < D.R.m) (hC : C j = 0) (f : SchRow ch.G)
    (u : ColPt ch.G) (y : RowPt ch.G) : evT C f u y = 0 := by
  obtain ⟨k, rfl⟩ := hj
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold evT
  rw [Finset.prod_eq_zero (i := k) (by simp [Finset.mem_range]; omega) (by rw [two_mul, hC]; rfl), zero_mul]

end
end GlobalTheory.RowVal

namespace GlobalTheory.RowVal
section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem suppOn_of_cover (s : ℤˣ) (hC : CoverAt ch s) (hF : FlatAt ch s) (hO : OffAt ch) (hI : InvAt ch) (hT : TensAt ch)
    (hB : BasicAt ch) : SuppOn ch s := by
  intro t a τ hτ M hM P y b hb h h1 hne
  obtain ⟨hφ, hFt, hHaar, -, hGood, -, -⟩ := hB
  have hsum : ∀ h' : Pts ch.G, tot ch.W hM P τ (colFn ch a) (formTop ch t y) h' = ∑ d ∈ τ.support,
      τ d * per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h') d.1 P.1 (colFn ch a) (formTop ch t y) := fun _ => rfl
  have hne' := hne
  rw [hsum] at hne'
  obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hper := right_ne_zero_of_mul hdne
  have hnz : ∀ j, Even j → j < D.R.m → conAt ch.W hM (fockD ch.W t d.2 P.2) h j ≠ 0 := by
    intro j hj hjm h0
    apply hper
    have := hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) Unit {()} (fun _ => 1)
      (fun _ => conAt ch.W hM (fockD ch.W t d.2 P.2) h) (fun _ => d.1)
      (fun _ _ => hGood t _ τ hτ M hM d hd P.2 h)
      (fun u y' => by simp [evT_eq_zero_of ch _ j hj hjm h0]) P.1
    simpa using this
  have h0 : h 0 = 1 := h1 0 (zero_not_mem_idx D)
  obtain ⟨β, hβ⟩ := hC t b hb h (hO t _ τ hτ M hM d hd P.2 h h0 hnz)
  refine ⟨β, ?_, hβ⟩
  by_contra hns
  apply hne
  classical

  choose! r hr a' ha' k hk e using hβ
  let p : Pts ch.G := fun j => if j ∈ idx D then a' j else 1
  have hp : IsRealPt p := by
    refine ⟨fun j => ?_, fun j hj => by simp [p, hj]⟩
    by_cases hj : j ∈ idx D
    · simp only [p, if_pos hj]; exact ha' j hj
    · simp only [p, if_neg hj]; exact one_mem _
  have hmove : tot ch.W hM P τ (colFn ch a) (formTop ch t y) h = tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b β) := by
    refine biInv_eq_of_cells (idx D) (hI t a τ hτ M hM P y) h (p * b β) (fun j hj => ?_) (fun j hj => ?_)
    · simp [p, hj, h1 j hj, (hb β).1 j hj]
    · refine ⟨r j, hr j hj, k j, hk j hj, ?_⟩
      simp only [Pi.mul_apply, p, if_pos hj, e j hj, mul_assoc]
  rw [hmove]

  have hexp : ch.S.IsExpansion t (ch.Phi a) β 0 := by
    obtain ⟨e₀, he₀, -⟩ := hτ
    refine ⟨e₀, he₀, by simp, fun x y' _ _ => ?_⟩
    rw [Finsupp.sum_zero_index]
    simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall] at hns
    obtain ⟨w, hw⟩ := hns
    have hz : (ch.S.term t (ch.Phi a) β w).datum = 0 := by
      simpa [unfSupport, GridChoice.term] using hw
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hz]; rfl)
  obtain ⟨z, -, hFl⟩ := hF
  obtain ⟨Cr, -, hCr⟩ := hFl P.2 p hp
  obtain ⟨ζ, -, hz⟩ := hCr t (ch.Phi a) τ hτ M hM β (b β) (hb β) 0 (fun _ => 0) hexp (by intro d hd; simp at hd)
  rw [hsum]
  exact hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) _ τ.support (fun d => τ d)
    (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b β)) (fun d => d.1)
    (fun d hd => hGood t _ τ hτ M hM d hd P.2 _)
    (fun u y' => by simpa [Finsupp.sum] using hz u y') P.1

end

theorem big_suppOn_of_flat :
    Big fun ch => ∀ s, FlatAt ch s → OffAt ch → InvAt ch → TensAt ch → BasicAt ch → SuppOn ch s :=
  big_mono (fun ch hC s hF hO hI hT hB => suppOn_of_cover ch s (hC s) hF hO hI hT hB) GlobalTheory.T.tiltedPoints_covered_by_representativeCells

end GlobalTheory.RowVal
