import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MB

open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open PositivityTheory.Rg.BcB.F.MT (MatchLin)

section SlopeTestRemainingChoices

theorem mb_finsum_mul {α : Type*} (c : ℂ) (g : α → ℂ) : ∑ᶠ i, c * g i = c * ∑ᶠ i, g i := by
  exact (mul_finsum g c).symm

theorem mb_mem_rStab {H : Type} [Group H] (u : H → ℂ) (k : H) : k ∈ rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

theorem mb_avg_mul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun x => c * u x) = c * avg u := by
  by_cases hc : c = 0
  · subst hc
    simp [avg]
  have hS : rStab (fun x => c * u x) = rStab u := by
    ext k
    simp only [mb_mem_rStab, mul_right_inj' hc]
  unfold avg
  rw [hS]
  beta_reduce
  rw [mb_finsum_mul]
  ring

theorem mb_twOrb_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (c : ℂ)
    (f : G → ℂ) : twOrb θ K δ (fun x => c * f x) = c * twOrb θ K δ f := by
  unfold twOrb
  rw [← mb_finsum_mul]
  refine finsum_congr fun q => ?_
  simp only [mb_avg_mul]
  ring

theorem mb_clSum_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt : G → ℂ)
    (c : ℂ) (f : G → ℂ) : clSum θ K S wt (fun x => c * f x) = c * clSum θ K S wt f := by
  unfold clSum
  rw [← mb_finsum_mul]
  refine finsum_congr fun x => ?_
  by_cases h : x.rep ∈ S
  · rw [if_pos h, if_pos h, mb_twOrb_mul]
    ring
  · rw [if_neg h, if_neg h, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mb_match_smul {n a b : ℕ} {w : Pl E} {μ : (w.adicCompletion E)ˣ →* ℂˣ} {f : UL n w → ℂ}
    {φ : GLw a w × GLw b w → ℂ} (c : ℂ) (h : Match n a b w μ f φ) :
    Match n a b w μ (fun γ => c * f γ) (fun y => c * φ y) := by
  intro Q₁ Q₂ h1 h2 h3 h4 h5 h6 h7
  have e := h Q₁ Q₂ h1 h2 h3 h4 h5 h6 h7
  unfold stTw2 kapOrb at *
  rw [mb_clSum_mul, mb_clSum_mul, e]
  ring

theorem mb_hint_coset {H : Type} [Group H] (K L : Subgroup H) (hLK : L ≤ K) (g : H) (c : ℂ) :
    hint K (fun x => if g⁻¹ * x ∈ L then c else 0) = ((L.relIndex K : ℕ) : ℂ)⁻¹ * c := by
  by_cases hc : c = 0
  · subst hc
    simp [hint]
  have hR : rStab (fun x : H => if g⁻¹ * x ∈ L then c else 0) = L := by
    ext k
    rw [mb_mem_rStab]
    constructor
    · intro hk
      by_contra hkL
      have h1 := hk g
      simp only [inv_mul_cancel_left, inv_mul_cancel, L.one_mem, if_true, if_neg hkL] at h1
      exact hc h1.symm
    · intro hk x
      simp only [← mul_assoc, Subgroup.mul_mem_cancel_right _ hk]
  have hS : rStab (fun x : H => if g⁻¹ * x ∈ L then c else 0) ⊓ K = L := by
    rw [hR]
    exact inf_eq_left.2 hLK
  unfold hint
  rw [hS]
  congr 1
  rw [finsum_eq_single _ (QuotientGroup.mk g : H ⧸ L)]
  · have hm : g⁻¹ * (QuotientGroup.mk g : H ⧸ L).out ∈ L :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk g : H ⧸ L)).symm
    exact if_pos hm
  · intro q hq
    have hm : g⁻¹ * q.out ∉ L := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 ?_
      have := L.inv_mem hm
      rwa [_root_.mul_inv_rev, inv_inv] at this
    exact if_neg hm

theorem mb_relIndex_ne_zero {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K L : Subgroup H) (hL : IsOpen (L : Set H)) (hK : IsCompact (K : Set H)) : L.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hop : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hL.preimage continuous_subtype_val
  have : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  exact Subgroup.index_ne_zero_of_finite

theorem mb_lone_apply {n : ℕ} {w : Pl E} (K' : Subgroup (UL n w)) (x : UL n w) :
    lone K' x = if x ∈ K' then ((K'.relIndex (KL n w) : ℕ) : ℂ) else 0 := by
  simp [lone, Set.indicator_apply]

theorem mb_lconv_lone {n : ℕ} {w : Pl E} (K' : Subgroup (UL n w)) (hK : K' ≤ KL n w) :
    lconv (lone K') (lone K') = lone K' := by
  funext y
  unfold lconv
  by_cases hy : y ∈ K'
  · have hu : (fun z => lone K' z * lone K' (z⁻¹ * y)) = fun z => if (1 : UL n w)⁻¹ * z ∈ K' then
        ((K'.relIndex (KL n w) : ℕ) : ℂ) * ((K'.relIndex (KL n w) : ℕ) : ℂ) else 0 := by
      funext z
      simp only [mb_lone_apply, inv_one, one_mul]
      by_cases hz : z ∈ K'
      · have h2 : z⁻¹ * y ∈ K' := K'.mul_mem (K'.inv_mem hz) hy
        rw [if_pos hz, if_pos h2, if_pos hz]
      · rw [if_neg hz, if_neg hz, zero_mul]
    rw [hu, mb_hint_coset _ _ hK, mb_lone_apply, if_pos hy]
    by_cases hN : ((K'.relIndex (KL n w) : ℕ) : ℂ) = 0
    · rw [hN, mul_zero, mul_zero]
    · rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · have hu : (fun z => lone K' z * lone K' (z⁻¹ * y)) = fun z => if (1 : UL n w)⁻¹ * z ∈ K' then (0 : ℂ) else 0 := by
      funext z
      simp only [mb_lone_apply, inv_one, one_mul, ite_self]
      by_cases hz : z ∈ K'
      · have h2 : z⁻¹ * y ∉ K' := fun h => hy (by simpa using K'.mul_mem hz h)
        rw [if_neg h2, mul_zero]
      · rw [if_neg hz, zero_mul]
    rw [hu, mb_hint_coset _ _ hK, mb_lone_apply, if_neg hy, mul_zero]

theorem mb_isCompact_KL_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) : IsCompact (KL n w : Set (UL n w)) := by
  have hcl : IsClosed (UL n w : Set (GLw n w)) := by
    have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact isClosed_univ
  have hKL : (KL n w : Set (UL n w)) = Subtype.val ⁻¹' (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
    ext x
    exact Subgroup.mem_subgroupOf
  rw [hKL]
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2

theorem mb_isHecke_lone {n : ℕ} {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    (hc : IsCompact (KL n w : Set (UL n w))) : IsHecke K' (lone K') := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · have hcl : IsClosed (K' : Set (UL n w)) := Subgroup.isClosed_of_isOpen K' hK.1
    have hsupp : Function.support (lone K') ⊆ (K' : Set (UL n w)) := by
      intro x hx
      by_contra h
      exact hx (by rw [mb_lone_apply, if_neg (show x ∉ K' from h)])
    exact hc.of_isClosed_subset (isClosed_tsupport _)
      ((closure_minimal hsupp hcl).trans fun x hx => hK.2.1 hx)
  · simp only [mb_lone_apply, Subgroup.mul_mem_cancel_left K' hk]
  · simp only [mb_lone_apply, Subgroup.mul_mem_cancel_right K' hk]

end SlopeTestRemainingChoices

theorem lponeIdem : LponeIdem := by
  intro E _ _ _ n w K' hK m
  induction m with
  | zero => rfl
  | succ m ih =>
    show lconv (lone K') (lpow K' (lone K') m) = lone K'
    rw [ih]
    exact mb_lconv_lone K' hK.2.1

theorem fixIdem : FixIdem := by
  intro E _ _ _ a b w L hLo hLK φ hφ
  have hK2c : IsCompact (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  have hN : ((L.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (mb_relIndex_ne_zero _ _ hLo hK2c)
  have hidem : ∀ y, idem L y = if y ∈ L then ((L.relIndex (K2 a b w) : ℕ) : ℂ) else 0 := fun y => by
    simp [idem, Set.indicator_apply]
  refine ⟨funext fun m => ?_, funext fun m => ?_⟩
  · have hu : (fun m' => φ m' * idem L (m'⁻¹ * m)) =
        fun m' => if m⁻¹ * m' ∈ L then ((L.relIndex (K2 a b w) : ℕ) : ℂ) * φ m else 0 := by
      funext m'
      rw [hidem]
      by_cases hk : m⁻¹ * m' ∈ L
      · have h1 : m'⁻¹ * m ∈ L := by
          have := L.inv_mem hk
          rwa [_root_.mul_inv_rev, inv_inv] at this
        have h2 : φ m' = φ m := by
          have := (hφ.2 _ hk m).2
          rwa [mul_inv_cancel_left] at this
        rw [if_pos h1, if_pos hk, h2, mul_comm]
      · have h1 : m'⁻¹ * m ∉ L := fun h => hk (by
          have := L.inv_mem h
          rwa [_root_.mul_inv_rev, inv_inv] at this)
        rw [if_neg h1, if_neg hk, mul_zero]
    rw [mconv, hu, mb_hint_coset _ _ hLK, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · have hu : (fun m' => idem L m' * φ (m'⁻¹ * m)) =
        fun m' => if (1 : GLw a w × GLw b w)⁻¹ * m' ∈ L then ((L.relIndex (K2 a b w) : ℕ) : ℂ) * φ m else 0 := by
      funext m'
      rw [hidem, inv_one, one_mul]
      by_cases hk : m' ∈ L
      · rw [if_pos hk, if_pos hk, (hφ.2 _ (L.inv_mem hk) m).1]
      · rw [if_neg hk, if_neg hk, zero_mul]
    rw [mconv, hu, mb_hint_coset _ _ hLK, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

theorem matchBadSOf : MatchBadSOf := by
  intro h3 hI E _ _ _ n a ha w hw μ K' hK m
  rw [hI E n w K' hK m]
  exact h3 E n a ha w hw μ K' hK (lone K') (mb_isHecke_lone hK (mb_isCompact_KL_split hw))

theorem matchUnitIOf : MatchUnitIOf := by
  intro h1 E _ _ _ hU w hw n a ha
  have hM := h1 E hU w hw n a (n - a) (Nat.add_sub_cancel' ha)
  have he : idem (K2 a (n - a) w) =
      ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)) : Subgroup _) : Set (GLw a w × GLw (n - a) w)).indicator 1) := by
    funext y
    simp [idem, Set.indicator_apply, Subgroup.relIndex_self]
  rw [he]
  exact hM

end PositivityTheory.Rg.BcB.F.MB

end
