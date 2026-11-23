import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroCoind
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

section Index

theorem index_gsOpenSubgroup :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index = Module.finrank K.1 L.1 := by
  rw [coe_gsOpenSubgroup]
  change (gsEmbedding (S := S) hL).fieldRange.fixingSubgroup.index = _
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact (gsEmbedding (S := S) hL).equivFieldRange.toLinearEquiv.finrank_eq.symm

theorem finiteIndex_gsOpenSubgroup :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).FiniteIndex :=
  ⟨by rw [index_gsOpenSubgroup]; exact Module.finrank_pos.ne'⟩

theorem card_coind_gsOpenSubgroup
    (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :
    Nat.card (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B) =
      Nat.card B ^ Module.finrank K.1 L.1 := by
  have := finiteIndex_gsOpenSubgroup S hL
  rw [card_coind_eq, index_gsOpenSubgroup]

end Index

section Count

variable (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

theorem finrank_eq_sum_index_mackeySubgroup (v : {v : InfinitePlace K.1 // v.IsReal}) :
    Module.finrank K.1 L.1 =
      ∑ d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom,
        (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom d.out).index := by
  let N : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) :=
    zmodRep.{0} _ 2
  have h2 : Nat.card N = 2 := by
    change Nat.card (ULift.{0} (ZMod 2)) = 2
    simp
  have hC := card_coind_gsOpenSubgroup S hL N
  have hM := Nat.card_congr (mackeyEquiv (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (gsRealFamily S ιr v).toMonoidHom N).toEquiv
  rw [Nat.card_pi, hC, h2] at hM
  have hs : ∀ d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom,
      Nat.card (mackeySummand (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom N d.out) =
        2 ^ (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom d.out).index := fun d => by
    rw [card_coind_eq]
    exact congrArg (· ^ _) h2
  rw [Finset.prod_congr rfl fun d _ => hs d, Finset.prod_pow_eq_pow_sum] at hM
  exact Nat.pow_right_injective le_rfl hM

open scoped Classical in

theorem index_mackeySubgroup_realFamily (v : {v : InfinitePlace K.1 // v.IsReal})
    (d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom) :
    (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom d.out).index =
      if mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom d.out = ⊤ then 1 else 2 := by
  split_ifs with h
  · rw [h, Subgroup.index_top]
  · rw [eq_bot_of_ne_top_realGal v _ h, Subgroup.index_bot, Nat.card_eq_fintype_card,
      card_realGal_eq_two v.1 v.2]

open scoped Classical in

theorem finrank_mul_card_real_eq_sum_index :
    Module.finrank K.1 L.1 * Nat.card {v : InfinitePlace K.1 // v.IsReal} =
      ∑ p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
          MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr v).toMonoidHom,
        (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1).toMonoidHom p.2.out).index := by
  rw [Fintype.sum_sigma, Finset.sum_congr rfl fun v _ => (finrank_eq_sum_index_mackeySubgroup S hL ιr v).symm,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

open scoped Classical in

theorem sum_index_eq_card_top_add :
    ∑ p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom,
      (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out).index =
      Nat.card (MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) +
        2 * Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} := by
  have htop : ∀ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom //
      mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
      (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out).index = 1 := fun p =>
    (index_mackeySubgroup_realFamily S hL ιr p.1.1 p.1.2).trans (if_pos p.2)
  have hlow : ∀ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom //
      ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
      (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out).index = 2 := fun p =>
    (index_mackeySubgroup_realFamily S hL ιr p.1.1 p.1.2).trans (if_neg p.2)
  have h := Fintype.sum_subtype_add_sum_subtype (fun p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
    MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom =>
      mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤)
    (fun p => (mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1).toMonoidHom p.2.out).index)
  simp only [htop, hlow, Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_eq_nat_card,
    mul_one] at h
  exact h.symm.trans (congrArg₂ (· + ·) rfl (Nat.mul_comm _ _))

theorem count_places_arith {n a a₁ a₂ c₁ c₂ b dK dL NK NL : ℕ} (hK : NK = a₁ + a₂) (hL : NL = c₁ + c₂)
    (h₀ : a = c₁) (h₁ : n * a₁ = a + 2 * b) (h₂ : a₁ + 2 * a₂ = dK) (h₃ : c₁ + 2 * c₂ = dL)
    (h₄ : dK * n = dL) : NL + b = n * NK := by
  subst hK hL h₂ h₃
  rw [h₀] at h₁
  have e : c₁ + 2 * c₂ = n * a₁ + 2 * (n * a₂) := by rw [← h₄]; ring
  rw [mul_add]
  generalize n * a₁ = X at *
  generalize n * a₂ = Y at *
  omega

theorem card_infinitePlace_eq_real_add_complex (F : FiniteSubfield) :
    Nat.card (InfinitePlace F.1) =
        Nat.card {w : InfinitePlace F.1 // w.IsReal} + Nat.card {w : InfinitePlace F.1 // w.IsComplex} ∧
      Nat.card {w : InfinitePlace F.1 // w.IsReal} + 2 * Nat.card {w : InfinitePlace F.1 // w.IsComplex} =
        Module.finrank ℚ F.1 := by
  have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F.1
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank F.1
  simp only [InfinitePlace.nrRealPlaces, InfinitePlace.nrComplexPlaces, Fintype.card_eq_nat_card] at h1 h2
  exact ⟨h1, h2⟩

theorem card_infinitePlace_add_card :
    Nat.card (InfinitePlace L.1) +
        Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} =
      Module.finrank K.1 L.1 * Nat.card (InfinitePlace K.1) := by
  have htop : Nat.card (MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) =
      Nat.card {w : InfinitePlace L.1 // w.IsReal} :=
    Nat.card_eq_of_bijective (realMemberPlace S ιr hL)
      ⟨realMemberPlace_injective S ιr hL, realMemberPlace_surjective S ιr hL⟩
  have hsum := (finrank_mul_card_real_eq_sum_index S hL ιr).trans (sum_index_eq_card_top_add S hL ιr)
  exact count_places_arith (card_infinitePlace_eq_real_add_complex K).1
    (card_infinitePlace_eq_real_add_complex L).1 htop hsum (card_infinitePlace_eq_real_add_complex K).2
    (card_infinitePlace_eq_real_add_complex L).2 (Module.finrank_mul_finrank ℚ K.1 L.1)

end Count

end

end GroundTheory.ProfCoh
