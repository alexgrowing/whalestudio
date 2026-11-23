import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.CardCohomologyZeroMackeyRepOfNeTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
  [IsDiscreteRep B]

open scoped Classical in

theorem prod_gsRealH0Card_coind
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (mem : {w : InfinitePlace L.1 // w.IsReal} → MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL))
    (hmem : ∀ w, realMemberPlace S ιr hL (mem w) = w)
    (e : ∀ w, Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ w (g : Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion))
      (hg : (mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨(mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e w g)) :
    ∏ v : {v : InfinitePlace K.1 // v.IsReal},
        gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
          ιr v =
      (∏ w : {w : InfinitePlace L.1 // w.IsReal},
          gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w) *
        Nat.card B ^ Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} := by
  have hbij : Function.Bijective mem :=
    ⟨fun w w' h => (hmem w).symm.trans ((congrArg (realMemberPlace S ιr hL) h).trans (hmem w')),
      fun p => ⟨realMemberPlace S ιr hL p, realMemberPlace_injective S ιr hL (hmem _)⟩⟩
  have hlow : ∀ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
        MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom //
      ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
      Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out) 0) = Nat.card B := fun p =>
    card_cohomology_zero_mackeyRep_of_ne_top S hL ιr B p.1.1 p.1.2 p.2
  have htop : ∏ w : {w : InfinitePlace L.1 // w.IsReal},
        gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w =
      ∏ p : {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
          MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr v).toMonoidHom //
        mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤},
        Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out) 0) :=
    Fintype.prod_equiv (Equiv.ofBijective mem hbij : {w : InfinitePlace L.1 // w.IsReal} ≃
        {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
          MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr v).toMonoidHom //
        mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤}) _ _ fun w =>
      (card_cohomology_zero_mackeyRep_top S hL ιr B ιrL (mem w) w (e w) (he w)).symm
  have hsplit := Fintype.prod_subtype_mul_prod_subtype
    (fun p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
      MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom =>
      mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤)
    (fun p => Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1).toMonoidHom B p.2.out) 0))
  simp only [hlow, Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card] at hsplit
  exact (Finset.prod_congr rfl fun v _ => gsRealH0Card_coind S hL ιr B v).trans <|
    (Fintype.prod_sigma (fun p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
      MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom =>
      Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr p.1).toMonoidHom B p.2.out) 0))).symm.trans <|
    hsplit.symm.trans (congrArg (· * _) htop.symm)

theorem ratio_coind_arith {χ χ' PK PL nC nB : ℚ} {cK cL b n : ℕ} (hχ : χ = χ') (hC : nC = nB ^ n)
    (hP : PK = PL * nB ^ b) (hN : cL + b = n * cK) (hB : nB ≠ 0) :
    χ * nC ^ cK / PK = χ' * nB ^ cL / PL := by
  subst hχ hC hP
  rw [← pow_mul, ← hN, pow_add, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero _ hB)]

open scoped Classical in

theorem gsEulerRatio_coind_eq_of [Finite B]
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (mem : {w : InfinitePlace L.1 // w.IsReal} → MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL))
    (hmem : ∀ w, realMemberPlace S ιr hL (mem w) = w)
    (e : ∀ w, Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ w (g : Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion))
      (hg : (mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨(mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e w g)) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B) ιr =
      gsEulerRatio (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL := by
  have hχ := (eulerChar_coind (gsOpenSubgroup S hL) B).trans
    (eulerChar_res_continuousMulEquiv (gsBaseChange S hL).symm B).symm
  have hC : ((Nat.card (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B) :
      ℕ) : ℚ) = (Nat.card B : ℚ) ^ Module.finrank K.1 L.1 := by
    exact_mod_cast card_coind_gsOpenSubgroup S hL B
  have hP := prod_gsRealH0Card_coind S hL ιr B ιrL mem hmem e he
  have hPq : (∏ v : {v : InfinitePlace K.1 // v.IsReal},
        (gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
          ιr v : ℚ)) =
      (∏ w : {w : InfinitePlace L.1 // w.IsReal},
          (gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w : ℚ)) *
        (Nat.card B : ℚ) ^ Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} := by
    exact_mod_cast hP
  have hN := card_infinitePlace_add_card S hL ιr
  simp only [Nat.card_eq_fintype_card (α := InfinitePlace K.1), Nat.card_eq_fintype_card (α := InfinitePlace L.1)]
    at hN
  have hB : (Nat.card B : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  exact ratio_coind_arith hχ hC hPq hN hB

end

end GroundTheory.ProfCoh
