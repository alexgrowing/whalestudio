import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Bridge

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GeoNum

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]

abbrev red : MRing ι ℤ →+* MRing ι (ZMod p) := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ ZMod.intCast_surjective

theorem ker_red : RingHom.ker (red (ι := ι) p) = Ideal.span {C (p : ℤ)} := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton]

theorem ker_le_comap (J' : Ideal (MRing ι (ZMod p))) :
    RingHom.ker (red (ι := ι) p) ≤ J'.comap (red p) := by
  rw [RingHom.ker_eq_comap_bot]
  exact Ideal.comap_mono bot_le

theorem comap_map_eq {J : Ideal (MRing ι ℤ)} (hJ : RingHom.ker (red (ι := ι) p) ≤ J) :
    (J.map (red p)).comap (red p) = J := by
  rw [Ideal.comap_map_of_surjective _ (red_surjective p), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hJ]

theorem comap_sup_span (Q : Ideal (MRing ι (ZMod p))) (T : Set (MRing ι ℤ)) :
    Q.comap (red p) ⊔ Ideal.span T = (Q ⊔ Ideal.span (red p '' T)).comap (red p) := by
  have h : Q ⊔ Ideal.span (red p '' T) = (Q.comap (red p) ⊔ Ideal.span T).map (red p) := by
    rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ (red_surjective p), Ideal.map_span]
  rw [h, comap_map_eq p ((ker_le_comap p Q).trans le_sup_left)]

theorem isRelevant_comap_iff (Q : Ideal (MRing ι (ZMod p))) :
    Geo.IsRelevant (R := ℤ) (Q.comap (red p)) ↔ IsRelevant Q := by
  simp only [Geo.IsRelevant, IsRelevant, Ideal.mem_comap, red, map_X]

def quotEquiv (J' : Ideal (MRing ι (ZMod p))) :
    (MRing ι ℤ ⧸ J'.comap (red p)) ≃+* (MRing ι (ZMod p) ⧸ J') :=
  (Ideal.quotEquivOfEq (by rw [← RingHom.comap_ker, Ideal.mk_ker])).trans
    (RingHom.quotientKerEquivOfSurjective (f := (Ideal.Quotient.mk J').comp (red p))
      (Ideal.Quotient.mk_surjective.comp (red_surjective p)))

theorem quotEquiv_mk (J' : Ideal (MRing ι (ZMod p))) (x : MRing ι ℤ) :
    quotEquiv p J' (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk J' (red p x) :=
  rfl

theorem multAt_comap (J' W' : Ideal (MRing ι (ZMod p))) [W'.IsPrime] :
    NumbersDVR.multAt (J'.comap (red p)) (W'.comap (red p)) = NumbersDVR.multAt J' W' := by
  unfold NumbersDVR.multAt
  refine length_localizedModule_eq_of_surjective (red p) (red_surjective p) W' _ rfl _ _
    (quotEquiv p J').toAddEquiv fun s x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotEquiv p J' (Ideal.Quotient.mk _ (s * y)) =
    Ideal.Quotient.mk J' (red p s) * quotEquiv p J' (Ideal.Quotient.mk _ y)
  rw [quotEquiv_mk, quotEquiv_mk, map_mul, map_mul]

theorem length_toNat_comap (J' : Ideal (MRing ι (ZMod p))) :
    (Module.length ℤ (MRing ι ℤ ⧸ J'.comap (red p))).toNat =
      Module.finrank (ZMod p) (MRing ι (ZMod p) ⧸ J') := by
  have e1 : Module.length ℤ (MRing ι ℤ ⧸ J'.comap (red p)) =
      Module.length ℤ (MRing ι (ZMod p) ⧸ J') := by
    convert ((quotEquiv p J').toAddEquiv.toIntLinearEquiv).length_eq
  have e2 : Module.length ℤ (MRing ι (ZMod p) ⧸ J') =
      Module.length (ZMod p) (MRing ι (ZMod p) ⧸ J') := by
    convert Module.length_eq_of_surjective (R := ZMod p) (S := ℤ)
      (M := MRing ι (ZMod p) ⧸ J') ZMod.intCast_surjective
  rw [e1, e2, Module.length_eq_rank]
  rfl

theorem cycEval_divCycle_eq (Q : Ideal (MRing ι (ZMod p))) (s : MRing ι ℤ)
    (N : Ideal (MRing ι (ZMod p)) → ℤ) (g : Ideal (MRing ι ℤ) → ℤ)
    (h : ∀ W', divCycle Q (red p s) W' ≠ 0 → N W' = g (W'.comap (red p))) :
    cycEval N (divCycle Q (red p s)) =
      ∑ᶠ W ∈ Geo.divSupp (Q.comap (red p)) s,
        (Geo.multAt (Q.comap (red p) ⊔ Ideal.span {s}) W : ℤ) * g W := by
  classical
  have hJ : Q.comap (red p) ⊔ Ideal.span {s} = (Q ⊔ Ideal.span {red p s}).comap (red p) := by
    rw [comap_sup_span p Q {s}, Set.image_singleton]
  have hS : Geo.divSupp (Q.comap (red p)) s = Ideal.comap (red p) ''
      {W' | W' ∈ (Q ⊔ Ideal.span {red p s}).minimalPrimes ∧ IsRelevant W'} := by
    ext W
    simp only [Geo.divSupp, Set.mem_ofPred_eq, hJ,
      Ideal.comap_minimalPrimes_eq_of_surjective (red_surjective p), Set.mem_image]
    constructor
    · rintro ⟨⟨W', hW', rfl⟩, hr⟩
      exact ⟨W', ⟨hW', (isRelevant_comap_iff p W').mp hr⟩, rfl⟩
    · rintro ⟨W', ⟨hW', hr⟩, rfl⟩
      exact ⟨⟨W', hW', rfl⟩, (isRelevant_comap_iff p W').mpr hr⟩
  have hsupp : ∀ (f : Ideal (MRing ι (ZMod p)) → ℤ) (T : Set (Ideal (MRing ι (ZMod p)))),
      Function.support f ⊆ T → ∑ᶠ W ∈ T, f W = ∑ᶠ W, f W := by
    intro f T hT
    rw [← finsum_mem_inter_support f T, Set.inter_eq_right.mpr hT, ← finsum_mem_univ f,
      ← finsum_mem_inter_support f Set.univ, Set.univ_inter]
  rw [hS, finsum_mem_image (Ideal.comap_injective_of_surjective _ (red_surjective p)).injOn, hJ]
  unfold cycEval
  rw [← hsupp _ {W' | W' ∈ (Q ⊔ Ideal.span {red p s}).minimalPrimes ∧ IsRelevant W'}]
  · refine finsum_mem_congr rfl fun W' hW' => ?_
    have : W'.IsPrime := hW'.1.1.1
    have hd : divCycle Q (red p s) W' =
        ((NumbersDVR.multAt (Q ⊔ Ideal.span {red p s}) W').toNat : ℤ) := by
      unfold divCycle
      exact dif_pos hW'
    rw [multAt_eq_toNat, multAt_comap, ← hd]
    by_cases h0 : divCycle Q (red p s) W' = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [h W' h0]
  · intro W' hW'
    by_contra hT
    apply hW'
    show divCycle Q (red p s) W' * N W' = 0
    unfold divCycle
    rw [dif_neg (show ¬ (_ ∧ _) from hT), zero_mul]

theorem intNum_eq_geoNum_comap (n : ℕ) : ∀ Q : Ideal (MRing ι (ZMod p)), IsMultiProjPrime Q →
    relDim Q = ((n : ℕ) : WithBot (WithTop ℤ)) → ∀ a : Fin n → K → ℤ,
      intNum (ZMod p) Q a = Geo.geoNum n (Q.comap (red p)) a := by
  induction n with
  | zero =>
    intro Q hQ hdim a
    have hrel : Geo.IsRelevant (R := ℤ) (Q.comap (red p)) :=
      (isRelevant_comap_iff p Q).mpr hQ.relevant
    have hi : ∀ k, (X ⟨k, (hrel k).choose⟩ : MRing ι (ZMod p)) ∉ Q := fun k => by
      have := (hrel k).choose_spec
      rwa [Ideal.mem_comap, map_X] at this
    have hd : ringKrullDim (MRing ι (ZMod p) ⧸ Q) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      (CutRegular.relDim_eq_natCast_iff Q 0).mp hdim
    obtain rfl : a = ![] := Subsingleton.elim _ _
    rw [IntNumPoint.proof IntNumBase.full (ZMod p) K ι Q _ hQ hd hi]
    simp only [Geo.geoNum]
    rw [dif_pos hrel, ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg, ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal,
      comap_sup_span, ← Set.range_comp]
    have hf : (red p ∘ fun k => (X ⟨k, (hrel k).choose⟩ : MRing ι ℤ) - 1) =
        fun k => (X ⟨k, (hrel k).choose⟩ : MRing ι (ZMod p)) - 1 := by
      funext k
      simp [red]
    rw [hf, length_toNat_comap]
  | succ n ih =>
    intro Q hQ hdim a
    have hrel : Geo.IsRelevant (R := ℤ) (Q.comap (red p)) :=
      (isRelevant_comap_iff p Q).mpr hQ.relevant
    have hi : ∀ k, (X ⟨k, (hrel k).choose⟩ : MRing ι (ZMod p)) ∉ Q := fun k => by
      have := (hrel k).choose_spec
      rwa [Ideal.mem_comap, map_X] at this

    have hadd : ∀ c c' : K → ℤ,
        intNum (ZMod p) Q (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) (c + c')) =
          intNum (ZMod p) Q (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) c) +
            intNum (ZMod p) Q (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) c') := by
      intro c c'
      have := IntNumAdd.full (ZMod p) K ι Q hQ.multiHomog hQ.relevant (n + 1) hdim
        (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) 0) (Fin.last n) c c'
      simpa only [Fin.update_snoc_last] using this
    let f : (K → ℤ) →+ ℤ :=
      AddMonoidHom.mk' (fun c => intNum (ZMod p) Q (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) c))
        hadd
    have hlin : ∀ c : K → ℤ,
        intNum (ZMod p) Q (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) c) =
          ∑ k, c k * intNum (ZMod p) Q
            (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) (Pi.single k 1)) := by
      intro c
      have hc : c = ∑ k, c k • (Pi.single k 1 : K → ℤ) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      have : f c = ∑ k, c k • f (Pi.single k 1) := by
        conv_lhs => rw [hc]
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => map_zsmul f (c k) _
      simpa [f, smul_eq_mul] using this

    have hcut : ∀ k, intNum (ZMod p) Q
        (Fin.snoc (α := fun _ => K → ℤ) (Fin.init a) (Pi.single k 1)) =
          ∑ᶠ W ∈ Geo.divSupp (Q.comap (red p)) (X ⟨k, (hrel k).choose⟩),
            (Geo.multAt (Q.comap (red p) ⊔ Ideal.span {X ⟨k, (hrel k).choose⟩}) W : ℤ) *
              Geo.geoNum n W (Fin.init a) := by
      intro k
      have hX : IsMultiHomog (X ⟨k, (hrel k).choose⟩ : MRing ι (ZMod p)) (Pi.single k 1) :=
        isWeightedHomogeneous_X (ZMod p) (blockWeight ι) _
      have e : (fun j => (((Pi.single k 1 : K → ℕ) j : ℕ) : ℤ)) = Pi.single k 1 := by
        funext j
        by_cases hj : j = k
        · subst hj; simp
        · simp [hj]
      have hc := CutRegular.full (ZMod p) K ι Q hQ n hdim (Pi.single k 1) _ hX (hi k) (Fin.init a)
      rw [e] at hc
      rw [hc]
      have hXr : red p (X ⟨k, (hrel k).choose⟩ : MRing ι ℤ) = X ⟨k, (hrel k).choose⟩ := map_X _ _
      have := cycEval_divCycle_eq p Q (X ⟨k, (hrel k).choose⟩)
        (fun W => intNum (ZMod p) W (Fin.init a)) (fun W => Geo.geoNum n W (Fin.init a))
        (fun W' hW' => by
          rw [hXr] at hW'
          obtain ⟨hW'm, hW'd⟩ := DivCycleSupport.full (ZMod p) K ι Q hQ n hdim (Pi.single k 1) _
            hX (hi k) W' hW'
          exact ih W' hW'm hW'd (Fin.init a))
      rwa [hXr] at this
    conv_lhs => rw [← Fin.snoc_init_self a]
    rw [hlin]
    simp only [Geo.geoNum]
    rw [dif_pos hrel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcut k]

end GeoNum

open GeoNum in

theorem intNum_map_eq_geoNum {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Ideal (Geo.MRing ι))
    (hV : Geo.IsMultiProjPrime V) (hpV : (C (p : ℤ) : Geo.MRing ι) ∈ V)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞))
    (a : Fin n → K → ℤ) :
    intNum (ZMod p) (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a = Geo.geoNum n V a := by
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have : V.IsPrime := hV.1
  have hQ : IsMultiProjPrime (V.map (red p)) := by
    refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩
    · rw [isMultiHomogIdeal_iff]
      obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [← isRelevant_comap_iff p, hcm]
      exact hV.2.2
  have hd : relDim (V.map (red p)) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
    rw [CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this.symm
  have := intNum_eq_geoNum_comap p n _ hQ hd a
  rwa [hcm] at this

open GeoNum in

theorem intNum_map_eq_geoNum_hyps (p : ℕ) [Fact p.Prime] (D : ℕ) :
    Geo.IsMultiProjPrime (RingHom.ker (red (ι := fun _ : Unit => Fin (D + 1)) p)) ∧
      (C (p : ℤ) : Geo.MRing (fun _ : Unit => Fin (D + 1))) ∈
        RingHom.ker (red (ι := fun _ : Unit => Fin (D + 1)) p) ∧
      ringKrullDim (Geo.MRing (fun _ : Unit => Fin (D + 1)) ⧸
          RingHom.ker (red (ι := fun _ : Unit => Fin (D + 1)) p)) =
        ((D + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  refine ⟨⟨RingHom.ker_isPrime _, ⟨{C (p : ℤ)}, ?_, ker_red p⟩, fun k => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rintro _ rfl
    refine ⟨0, fun m hm k => ?_⟩
    have : m = 0 := by
      have h1 := MvPolynomial.mem_support_iff.mp hm
      rw [coeff_C] at h1
      by_contra hne
      exact h1 (if_neg (Ne.symm hne))
    subst this
    simp
  · rw [RingHom.mem_ker, map_X]
    exact X_ne_zero _
  · rw [RingHom.mem_ker, map_C]
    simp
  · rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (red_surjective p)),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
    have hc : Nat.card ((_ : Unit) × Fin (D + 1)) = D + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]

end

end GroundTheory.Heights₂.Heights.Bridge
