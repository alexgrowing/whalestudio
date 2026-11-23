import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotExtend

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_quotient_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      IsRegularLocalRing (R ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (R ⧸ Ideal.span (Set.range x)) + (Fintype.card κ : ℕ) = ringKrullDim R ∧
      (Ideal.span (Set.range x)).IsPrime := by
  intro R _ _ κ _ x hx
  classical
  obtain ⟨s, y, -, hs, hc⟩ := cotInd_extend R κ x hx
  rw [Set.Sum.elim_range] at hs
  have hd : ringKrullDim R = ((Fintype.card κ + s : ℕ) : WithBot ℕ∞) := by
    rw [hc, IsRegularLocalRing.spanFinrank_maximalIdeal]
  set I := Ideal.span (Set.range x) with hI
  have hle : I ≤ maximalIdeal R := by
    rw [← hs]
    exact Ideal.span_mono Set.subset_union_left
  have hne : I ≠ ⊤ := fun h => Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (y i)) = maximalIdeal (R ⧸ I) := by
    rw [← hmax, ← hs, Ideal.span_union, Ideal.map_sup, ← hI, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hfin : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (s : ℕ) := by
    rw [← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (y i))
    have h2 : (Set.range fun i => Ideal.Quotient.mk I (y i)).ncard ≤ s := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hdim : ((s : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard (Set.range x)
      (by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        rintro _ ⟨k, rfl⟩
        exact hx.mem k)
    rw [hd] at h1
    have h2 : (Set.range x).encard ≤ (Fintype.card κ : ℕ∞) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    have hnb : ringKrullDim (R ⧸ I) ≠ ⊥ := ringKrullDim_ne_bot
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hnb
    rw [← hn] at h1 ⊢
    have h3 : (Fintype.card κ : ℕ∞) + (s : ℕ∞) ≤ n + (Set.range x).encard := by
      exact_mod_cast h1
    have h4 : (s : ℕ∞) + (Fintype.card κ : ℕ∞) ≤ n + (Fintype.card κ : ℕ∞) := by
      rw [add_comm]
      exact h3.trans (by gcongr)
    have h5 : (s : ℕ∞) ≤ n := (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h4
    exact_mod_cast h5
  have hreg : IsRegularLocalRing (R ⧸ I) := .of_spanFinrank_maximalIdeal_le _ (hfin.trans hdim)
  have heq : ringKrullDim (R ⧸ I) = (s : ℕ) :=
    le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hfin) hdim
  refine ⟨hreg, ?_, ?_⟩
  · rw [heq, hd, add_comm]
    push_cast
    rfl
  · exact (Ideal.Quotient.isDomain_iff_prime I).1 (GlobalTheory.isDomain_of_isRegularLocalRing _)
