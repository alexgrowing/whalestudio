import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPowerStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowEqTorus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionZerosTwistLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.PureZero

theorem lt_of_big {g N N' : ℕ} (h : Big g N N') (hg : 1 ≤ g) : N ^ g * g.factorial < N' := by
  have hs := h.sep
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast h.four
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ g := one_le_pow₀ (by norm_num)
  have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((g : ℝ) / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at this
    linarith
  have h3 : (1 / 2 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
    have : (1 : ℝ) ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g := one_le_mul_of_one_le_of_one_le hg' h1
    nlinarith
  set C := (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)
  have hM : (0 : ℝ) ≤ ((N ^ g * g.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have h5 : (1 : ℝ) ≤ 2 * C * N := by nlinarith
  have : ((N ^ g * g.factorial : ℕ) : ℝ) < N' := by nlinarith
  exact_mod_cast this

theorem sec_eq_zero_of_dim_zero {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0)
    {M : LB (Out.baseOver (Sp K) ⊗ P.A).left} (s : M.Sec)
    (hs : ¬ ⊤ ≤ (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left ⁻¹ᵁ Out.nonzeroLocus s) (j : M.ι) :
    s.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  have : IsDominant e := ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩
  have : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  let z : Sp K ⟶ (Out.baseOver (Sp K) ⊗ P.A).left := (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left
  have hz : z = e ≫ inv (snd (Out.baseOver (Sp K)) P.A).left := by
    rw [IsIso.eq_comp_inv]
    exact congrArg (·.left) (lift_snd (𝟙 _) (1 : Out.baseOver (Sp K) ⟶ P.A))
  have hd : IsDominant z := by rw [hz]; infer_instance
  have : IsReduced (Out.baseOver (Sp K) ⊗ P.A).left :=
    isReduced_of_isOpenImmersion (snd (Out.baseOver (Sp K)) P.A).left
  by_contra hne
  have hb : ((Out.baseOver (Sp K) ⊗ P.A).left.basicOpen (s.f j) : Set (Out.baseOver (Sp K) ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
  obtain ⟨y, hy⟩ := hd.denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) hb
  refine hs fun y' _ => ?_
  have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
  subst this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

theorem twist_eq_zero (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) {g N N' d : ℕ} (hB : Big g N N') (hN' : (N' : K) ≠ 0) (hg : P.g ≤ g) (hd : 1 ≤ d)
    (hd' : d ≤ N ^ g * g.factorial) (c : Out.baseOver (Sp K) ⟶ P.A)
    (s : LB.Sec (Out.twistLB P.A P.L (N * d) c))
    (hs : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ N' = 1 → ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) :
    ∀ j, s.f j = 0 := by
  rcases Nat.eq_zero_or_pos P.g with h0 | h0
  · exact sec_eq_zero_of_dim_zero P h0 s (hs 1 (one_pow _))
  by_contra hne
  push Not at hne
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  have hcard := (h.mulN (Sp K) P N' hM1).2.2.2.2 K (𝟙 _) hN'
  have h₄ := card_torsion_zeros_twist_le h h₂ K P N d N' c h0 hB.four hd hN' s hne
  have e : N' ^ (2 * P.g) = N' ^ 2 * N' ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (hs x)), hcard, e] at h₄
  have h₅ := Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)
  have h₆ := lt_of_big hB (h0.trans_le hg)
  have h₇ : N ^ P.g * P.g.factorial ≤ N ^ g * g.factorial :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by have := hB.four; omega) hg) (Nat.factorial_le hg)
  have h₈ := Nat.mul_le_mul h₇ hd'
  nlinarith

theorem pure_eq_zero_of_vanishing_on_torsion :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' d : ℕ) (π : Φ.Pol N), Big g N N' → (N' : k) ≠ 0 → π.PB.g ≤ g → 1 ≤ d → d ≤ N ^ g * g.factorial → ∀ (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → (∀ x : Φ.Pt, x ^ N' = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ l, φ.f l = 0) := by
  intro h h₂ k _ _ Φ g N N' d π hB hN' hg hd hd' α φ hφ hx
  have hM1 : 1 ≤ N' := Nat.pos_of_ne_zero fun e => hN' (by rw [e, Nat.cast_zero])
  obtain ⟨s, hs0, hs⟩ := (GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower k Φ N d π α (by have := hB.four; omega) hd).1 φ hφ
  refine hs0 (twist_eq_zero h h₂ π.PB hB hN' hg hd hd' _ s fun b hb => ?_)
  have := π.hom
  have hb' : (b ≫ π.β.inv) ^ N' = 1 := by
    rw [← cancel_mono π.β.hom, MonObj.pow_comp, MonObj.one_comp, Category.assoc, π.β.inv_hom_id,
      Category.comp_id, hb]
  obtain ⟨x, hx1, hxq⟩ := (TorsLift.points_lift k Φ.E Φ.G Φ.D N' hM1).2.1 _ hb'
  have e : x ≫ Φ.D.q ≫ π.β.hom = b := by
    rw [← Category.assoc, hxq, Category.assoc, π.β.inv_hom_id, Category.comp_id]
  rw [← e]
  exact fun hh => hx x hx1 ((hs x).2 hh)

end GlobalTheory.PureZero
