import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.NontrivInf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExistsBis

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.BcB.F.FBL

namespace LpowMulPf

open PositivityTheory.Rg.BcB.F.FinConv (cv cv_hecke)

theorem out_smul {H : Type} [Group H] (L : Subgroup H) (h : H) (z : H ⧸ L) :
    ∃ c ∈ L, (h • z : H ⧸ L).out = h * z.out * c := by
  refine ⟨(h * z.out)⁻¹ * (h • z).out, ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  conv_rhs => rw [← QuotientGroup.out_eq' z]
  rfl

section Gen

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K K' : Subgroup H)

def one : H → ℂ := (K' : Set H).indicator fun _ => ((K'.relIndex K : ℕ) : ℂ)

variable {K K'}

theorem conv_eq (hKK : K' ≤ K) (hN : K'.relIndex K ≠ 0) (f₁ f₂ : H → ℂ) (h₁ : ∀ x, ∀ k ∈ K', f₁ (x * k) = f₁ x)
    (h₂ : ∀ k ∈ K', ∀ x, f₂ (k * x) = f₂ x) (y : H) :
    cv K f₁ f₂ y = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ K', f₁ q.out * f₂ (q.out⁻¹ * y) := by
  unfold cv
  refine GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ K K' _ hKK (fun k hk x => ?_) hN
  show f₁ (x * k) * f₂ ((x * k)⁻¹ * y) = f₁ x * f₂ (x⁻¹ * y)
  rw [h₁ x k hk, mul_inv_rev, mul_assoc, h₂ _ (K'.inv_mem hk)]

theorem one_left (hKK : K' ≤ K) (hN : K'.relIndex K ≠ 0) (f : H → ℂ) (h : ∀ k ∈ K', ∀ x, f (k * x) = f x) :
    cv K (one K K') f = f := by
  funext y
  have hr : ∀ x, ∀ k ∈ K', one K K' (x * k) = one K K' x := by
    intro x k hk
    simp only [one, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_right hk]
  rw [conv_eq hKK hN _ _ hr h, finsum_eq_single _ (((1 : H)) : H ⧸ K')]
  · have h1 : (((1 : H)) : H ⧸ K').out ∈ K' := (PositivityTheory.Rg.BcB.F.Hint.out_mem K' _).2 rfl
    rw [one, Set.indicator_of_mem (show _ ∈ (K' : Set H) from h1), h _ (K'.inv_mem h1), ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN), one_mul]
  · intro q hq
    have : q.out ∉ (K' : Set H) := fun hm => hq ((PositivityTheory.Rg.BcB.F.Hint.out_mem K' q).1 hm)
    rw [one, Set.indicator_of_notMem this, zero_mul]

theorem conv_assoc (hKK : K' ≤ K) (hN : K'.relIndex K ≠ 0) (hO : IsOpen (K' : Set H)) (f₁ f₂ f₃ : H → ℂ)
    (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) (h₃ : IsHecke K' f₃) :
    cv K (cv K f₁ f₂) f₃ = cv K f₁ (cv K f₂ f₃) := by
  have h12 : IsHecke K' (cv K f₁ f₂) := by
    have := cv_hecke K K' K' f₁ f₂ h₁ h₂
    rwa [inf_idem] at this
  have h23 : IsHecke K' (cv K f₂ f₃) := by
    have := cv_hecke K K' K' f₂ f₃ h₂ h₃
    rwa [inf_idem] at this
  funext y
  have hc : HasCompactSupport (fun x : H => f₃ (x⁻¹ * y)) :=
    h₃.1.comp_homeomorph ((Homeomorph.inv H).trans (Homeomorph.mulRight y))
  set S := (PositivityTheory.Rg.BcB.F.Hint.fin_supp K' hO f₁ h₁.1).toFinset with hS
  set T := (PositivityTheory.Rg.BcB.F.Hint.fin_supp K' hO _ hc).toFinset with hT
  have hSz : ∀ q : H ⧸ K', q ∉ S → f₁ q.out = 0 := by
    intro q hq
    by_contra h
    exact hq (by simpa [hS] using h)
  have hTz : ∀ r : H ⧸ K', r ∉ T → f₃ (r.out⁻¹ * y) = 0 := by
    intro r hr
    by_contra h
    exact hr (by simpa [hT] using h)
  set N : ℂ := ((K'.relIndex K : ℕ) : ℂ)
  have L : cv K (cv K f₁ f₂) f₃ y =
      N⁻¹ * ∑ r ∈ T, (N⁻¹ * ∑ q ∈ S, f₁ q.out * f₂ (q.out⁻¹ * r.out)) * f₃ (r.out⁻¹ * y) := by
    rw [conv_eq hKK hN _ _ (fun x k hk => (h12.2 k hk x).2) (fun k hk x => (h₃.2 k hk x).1)]
    congr 1
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [conv_eq hKK hN _ _ (fun x k hk => (h₁.2 k hk x).2) (fun k hk x => (h₂.2 k hk x).1)]
      congr 2
      rw [finsum_eq_sum_of_support_subset (s := S)]
      intro q hq
      by_contra h
      exact hq (by simp [hSz q h])
    · intro r hr
      by_contra h
      exact hr (by simp [hTz r h])
  have R : cv K f₁ (cv K f₂ f₃) y =
      N⁻¹ * ∑ q ∈ S, f₁ q.out * (N⁻¹ * ∑ r ∈ T, f₂ (q.out⁻¹ * r.out) * f₃ (r.out⁻¹ * y)) := by
    rw [conv_eq hKK hN _ _ (fun x k hk => (h₁.2 k hk x).2) (fun k hk x => (h23.2 k hk x).1)]
    congr 1
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [conv_eq hKK hN _ _ (fun x k hk => (h₂.2 k hk x).2) (fun k hk x => (h₃.2 k hk x).1)]
      congr 2
      rw [finsum_eq_of_bijective (fun z : H ⧸ K' => q.out • z) (MulAction.bijective q.out)
        (g := fun r : H ⧸ K' => f₂ (q.out⁻¹ * r.out) * f₃ (r.out⁻¹ * y))]
      · rw [finsum_eq_sum_of_support_subset (s := T)]
        intro r hr
        by_contra h
        exact hr (by simp [hTz r h])
      · intro z
        obtain ⟨c, hc, e⟩ := out_smul K' q.out z
        show _ = f₂ (q.out⁻¹ * (q.out • z).out) * f₃ ((q.out • z).out⁻¹ * y)
        rw [e, show q.out⁻¹ * (q.out * z.out * c) = z.out * c by group, (h₂.2 c hc _).2,
          show (q.out * z.out * c)⁻¹ * y = c⁻¹ * (z.out⁻¹ * (q.out⁻¹ * y)) by group, (h₃.2 _ (K'.inv_mem hc) _).1]
    · intro q hq
      by_contra h
      exact hq (by simp [hSz q h])
  rw [L, R]
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Gen

end LpowMulPf

theorem lpowMul : LpowMul := by
  intro E _ _ _ n w K' g hO hKK hg m k
  have hK : IsCompact (KL n w : Set (UL n w)) := by
    rw [KL, Subgroup.coe_subgroupOf]
    exact (GlobalTheory.CompanionTheory.LevelU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage
      (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  have hN : K'.relIndex (KL n w) ≠ 0 := PositivityTheory.Rg.BcB.F.Hint.relIndex_ne_zero hO hK
  have hC : IsClosed (K' : Set (UL n w)) := K'.isClosed_of_isOpen hO
  have hK'c : IsCompact (K' : Set (UL n w)) := hK.of_isClosed_subset hC hKK
  have hone : IsHecke K' (U.lone K') := by
    refine ⟨HasCompactSupport.intro' hK'c hC fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
    · simp only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_left hk]
    · simp only [U.lone, Set.indicator_apply, SetLike.mem_coe, K'.mul_mem_cancel_right hk]
  have hconv : ∀ f₁ f₂, IsHecke K' f₁ → IsHecke K' f₂ → IsHecke K' (lconv f₁ f₂) := by
    intro f₁ f₂ h₁ h₂
    have := PositivityTheory.Rg.BcB.F.FinConv.cv_hecke (KL n w) K' K' f₁ f₂ h₁ h₂
    rwa [inf_idem] at this
  have hpow : ∀ j, IsHecke K' (U.lpow K' g j) := by
    intro j
    induction j with
    | zero => exact hone
    | succ j ih => exact hconv _ _ hg ih
  have hadd : ∀ a b, U.lpow K' g (a + b) = lconv (U.lpow K' g a) (U.lpow K' g b) := by
    intro a b
    induction a with
    | zero =>
      rw [zero_add]
      exact (LpowMulPf.one_left hKK hN _ fun k hk x => ((hpow b).2 k hk x).1).symm
    | succ a ih =>
      rw [Nat.add_right_comm]
      show lconv g (U.lpow K' g (a + b)) = lconv (lconv g (U.lpow K' g a)) (U.lpow K' g b)
      rw [ih]
      exact (LpowMulPf.conv_assoc hKK hN hO g _ _ hg (hpow a) (hpow b)).symm
  induction k with
  | zero =>
    show U.lone K' = U.lpow K' g (m * 0)
    rw [Nat.mul_zero]
    rfl
  | succ k ih =>
    show lconv (U.lpow K' g m) (U.lpow K' (U.lpow K' g m) k) = _
    rw [ih, Nat.mul_succ, Nat.add_comm, hadd]

end PositivityTheory.Rg.BcB.F.FBL

end
