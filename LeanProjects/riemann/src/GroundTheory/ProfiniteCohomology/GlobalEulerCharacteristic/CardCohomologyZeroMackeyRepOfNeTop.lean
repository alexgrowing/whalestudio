import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroReal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

instance isDiscreteRep_res_gsBaseChange_symm
    (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    [IsDiscreteRep B] : IsDiscreteRep (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) :=
  IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom _) B

variable (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
  [IsDiscreteRep B]

theorem gsRealH0Card_coind (v : {v : InfinitePlace K.1 // v.IsReal}) :
    gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
        ιr v =
      ∏ d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom,
        Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr v).toMonoidHom B d.out) 0) :=
  (Nat.card_congr (mackeyCohomologyEquiv (gsOpenSubgroup S hL) (gsRealFamily S ιr v) B 0).toEquiv).trans
    Nat.card_pi

theorem card_cohomology_zero_mackeyRep_of_ne_top (v : {v : InfinitePlace K.1 // v.IsReal})
    (d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom)
    (hd : ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom d.out = ⊤) :
    Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom B d.out) 0) = Nat.card B :=
  card_cohomology_zero_of_forall_eq_one _ fun g => by
    have hb := eq_bot_of_ne_top_realGal v _ hd
    have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 (hb ▸ g.2))
    subst hg
    exact map_one _

theorem card_cohomology_zero_mackeyRep_top
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (p : MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) (w : {w : InfinitePlace L.1 // w.IsReal})
    (e : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ (g : Gal(AlgebraicClosure p.1.1.1.Completion / p.1.1.1.Completion))
      (hg : p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨p.1.2.out * gsRealFamily S ιr p.1.1 g * p.1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e g)) :
    Nat.card (cohomology (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out) 0) =
      gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w := by
  have key : ∀ h : mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out,
      (gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w (e h)) =
        mackeyConj (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out h := fun h =>
    (ContinuousMulEquiv.symm_apply_eq _).2 (he h h.2).symm
  have hiff : ∀ b : B,
      (∀ h : mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out,
        B.ρ (mackeyConj (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out h) b = b) ↔
      (∀ g' : Gal(AlgebraicClosure w.1.Completion / w.1.Completion),
        B.ρ ((gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w g')) b = b) := by
    intro b
    constructor
    · intro hb g'
      have hm : e.symm g' ∈ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out := (Subgroup.eq_top_iff' _).1 p.2 (e.symm g')
      have h4 : (gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w g') =
          mackeyConj (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1.1).toMonoidHom p.1.2.out ⟨e.symm g', hm⟩ :=
        (congrArg (fun t => (gsBaseChange S hL).symm (gsRealFamily (placesOver S) ιrL w t))
          (e.apply_symm_apply g').symm).trans (key ⟨e.symm g', hm⟩)
      exact (congrArg (fun t => B.ρ t b) h4).trans (hb ⟨e.symm g', hm⟩)
    · intro hb h
      exact (congrArg (fun t => B.ρ t b) (key h)).symm.trans (hb (e h))
  exact (Nat.card_congr (H0Iso (mackeyRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr p.1.1).toMonoidHom B p.1.2.out)).toLinearEquiv.toEquiv).trans <|
    (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans
      (Nat.card_congr (H0Iso (Rep.res (gsRealFamily (placesOver S) ιrL w).toMonoidHom
        (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B))).toLinearEquiv.toEquiv).symm

end

end GroundTheory.ProfCoh
