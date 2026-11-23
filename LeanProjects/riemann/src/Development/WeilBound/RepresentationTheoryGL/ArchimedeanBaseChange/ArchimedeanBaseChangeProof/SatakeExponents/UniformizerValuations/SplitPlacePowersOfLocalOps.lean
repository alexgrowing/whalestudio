import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchS

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MS

section SlopeTestRemainingChoices

variable {H : Type} [Group H]

theorem ms_mem_rStab {u : H → ℂ} {r : H} : r ∈ rStab u ↔ ∀ x, u (x * r) = u x := Iff.rfl

theorem ms_rStab_left (u : H → ℂ) (k : H) : rStab (fun z => u (k * z)) = rStab u := by
  ext r
  rw [ms_mem_rStab, ms_mem_rStab]
  constructor
  · intro h x
    simpa [mul_assoc] using h (k⁻¹ * x)
  · intro h x
    simpa [mul_assoc] using h (k * x)

theorem ms_hint_left (K : Subgroup H) (u : H → ℂ) (k : H) :
    hint K (fun z => u (k * z)) = hint K u := by
  unfold hint
  rw [ms_rStab_left]
  congr 1
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)))
  refine finsum_congr fun q => ?_
  have hq : (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)) q =
      ((k * q.out : H) : H ⧸ (rStab u ⊓ K)) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab u ⊓ K) (k * q.out)
  rw [hh]
  exact (h.2.1 _).symm

theorem ms_exists_of_hint_ne_zero (K : Subgroup H) (u : H → ℂ) (h : hint K u ≠ 0) : ∃ z, u z ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold hint
  simp [hc]

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isHk_gconv {w : Pl E} (K' : Subgroup (GLw n w)) (f₁ f₂ : GLw n w → ℂ)
    (h₁ : IsHk K' f₁) (h₂ : IsHk K' f₂) : IsHk K' (gconv f₁ f₂) := by
  refine ⟨h₁.1, h₁.2.1, ?_, ?_⟩
  · refine HasCompactSupport.intro (h₁.2.2.1.isCompact.mul h₂.2.2.1.isCompact) fun y hy => ?_
    by_contra hne
    unfold gconv at hne
    obtain ⟨z, hz⟩ := ms_exists_of_hint_ne_zero _ _ hne
    apply hy
    have hz1 : f₁ z ≠ 0 := left_ne_zero_of_mul hz
    have hz2 : f₂ (z⁻¹ * y) ≠ 0 := right_ne_zero_of_mul hz
    have hm := Set.mul_mem_mul (subset_tsupport _ hz1) (subset_tsupport _ hz2)
    simpa using hm
  · intro k₁ hk₁ k₂ hk₂ g
    unfold gconv
    set u : GLw n w → ℂ := fun z => f₁ z * f₂ (z⁻¹ * g) with hu
    have e1 : (fun z => f₁ z * f₂ (z⁻¹ * (k₁ * g * k₂))) = fun z => u (k₁⁻¹ * z) := by
      funext z
      have a1 : f₂ (z⁻¹ * (k₁ * g * k₂)) = f₂ (z⁻¹ * k₁ * g) := by
        rw [show z⁻¹ * (k₁ * g * k₂) = 1 * (z⁻¹ * k₁ * g) * k₂ by group]
        exact h₂.2.2.2 1 (one_mem _) k₂ hk₂ _
      have a2 : f₁ (k₁⁻¹ * z) = f₁ z := by
        have := h₁.2.2.2 k₁⁻¹ (inv_mem hk₁) 1 (one_mem _) z
        rwa [mul_one] at this
      show _ = f₁ (k₁⁻¹ * z) * f₂ ((k₁⁻¹ * z)⁻¹ * g)
      rw [a1, a2, show (k₁⁻¹ * z)⁻¹ * g = z⁻¹ * k₁ * g by group]
    rw [e1]
    exact ms_hint_left _ u k₁⁻¹

theorem isHk_gpow {w : Pl E} (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ) (hf : IsHk K' f) :
    ∀ N, IsHk K' (gpow f N)
  | 0 => hf
  | N + 1 => isHk_gconv K' f (gpow f N) hf (isHk_gpow K' f hf N)

end SlopeTestRemainingChoices

theorem split_place_powers_of_local_ops (hL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) : SplitPlaceConstantTermPowers := by
  intro E _ _ _ n a b h w K' hKo hKK hnorm X hX hXu f hf N m
  obtain ⟨-, hct, hprod, -⟩ := hL E n a b h w K' hKo hKK hnorm X hX hXu
  have hpow := isHk_gpow K' f hf
  have key : ∀ N, ∀ x ∈ X, ∀ z ∈ X, phi3 h w (gpow f N) x z = mpow X (phi3 h w f) N x z := by
    intro N
    induction N with
    | zero => intro x _ z _; rfl
    | succ N ih =>
      intro x hx z hz
      funext m
      rw [show gpow f (N + 1) = gconv f (gpow f N) from rfl, hprod f (gpow f N) hf (hpow N) x hx z hz m]
      show _ = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f x y) (mpow X (phi3 h w f) N y z) m
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [ih y hy z hz]
  rw [hct _ (hpow N) m]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [key N x hx x hx]

theorem match_split_place_of_powers (h3 : PositivityTheory.Rg.Bc.ArchbcB.B.M3) (hP : SplitPlaceConstantTermPowers) : MatchSplitPlace := by
  intro E _ _ _ _ n a w hw hUL μ K' hKo hKK hnorm hlev X hX hXu f hf ha N
  have hpow := isHk_gpow K' f hf N
  have hULt : UL n w = ⊤ := eq_top_iff.2 fun g _ => hUL g
  have hcl : IsClosed (UL n w : Set (GLw n w)) := by
    rw [hULt]
    exact isClosed_univ
  have hH : IsHecke (K'.subgroupOf (UL n w)) (fun u : UL n w => gpow f N (u : GLw n w)) := by
    refine ⟨hpow.2.2.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal, fun k hk x => ⟨?_, ?_⟩⟩
    · have := hpow.2.2.2 (k : GLw n w) (Subgroup.mem_subgroupOf.1 hk) 1 (one_mem _) (x : GLw n w)
      simpa using this
    · have := hpow.2.2.2 1 (one_mem _) (k : GLw n w) (Subgroup.mem_subgroupOf.1 hk) (x : GLw n w)
      simpa using this
  have hM := h3 E n a ha w hw μ (K'.subgroupOf (UL n w)) hlev _ hH
  have hφ : ctMu (Nat.add_sub_cancel' ha) w μ (fun u : UL n w => gpow f N (u : GLw n w)) =
      splitPlaceMackeyTraceTwist (Nat.add_sub_cancel' ha) w μ X f N := by
    funext m
    unfold ctMu splitPlaceMackeyTraceTwist
    rw [← hP E n a (n - a) (Nat.add_sub_cancel' ha) w K' hKo hKK hnorm X hX hXu f hf N m]
    simp [toSub, hUL]
  rw [← hφ]
  exact hM

end PositivityTheory.Rg.BcB.F.MS

end
