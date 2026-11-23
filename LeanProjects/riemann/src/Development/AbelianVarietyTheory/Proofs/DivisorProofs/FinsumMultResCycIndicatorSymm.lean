import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthSumHeightOneDisjointDivisorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDimStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.CycLoc

theorem length_quot_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {e a}) := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  rw [← Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e a}) e.surjective]
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) f (by
    rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq

theorem finite_height_one (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (a : R) (ha : a ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) fun _ _ _ _ h => PrimeSpectrum.ext h).subset ?_
  rintro p ⟨hp, hap⟩
  refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q hq hqp => ?_⟩
  by_contra hn
  have := hq.1
  have h1 : q < p.asIdeal := lt_of_le_not_ge hqp hn
  have h0 : (⊥ : Ideal R) < q := bot_lt_iff_ne_bot.2 fun h =>
    ha (by simpa [h] using (Ideal.span_singleton_le_iff_mem _).1 hq.2)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  rw [hp] at e1
  have : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := (add_le_add_left e0 1).trans e1
  rw [Ideal.height_bot] at this
  exact absurd this (by decide)

theorem stalk_equiv (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x p ∈ U) (hx : x ∈ U) (s : Γ(X, U)),
        e (X.presheaf.germ U _ hq s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) (X.presheaf.germ U x hx s) := by
  let y : Spec (X.presheaf.stalk x) := p
  have := GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  refine Eq.trans ?_ h2
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

theorem specializes_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨p, rfl⟩

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨e, -⟩ := stalk_equiv X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

theorem mem_nonzeroLocus_iff_notMem {X : Scheme.{0}} {A : LB X} (s : A.Sec) {i : A.ι} {x : X} (hi : x ∈ A.U i)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ nonzeroLocus s ↔ X.presheaf.germ _ x hi (s.f i) ∉ p.asIdeal := by
  have hzi : X.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk X x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv X x p
  rw [Cartier.mem_nonzeroLocus_iff s i hzi, Scheme.mem_basicOpen _ _ _ hzi, ← MulEquiv.isUnit_map e, he _ hzi hi,
    IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal, Ideal.mem_primeCompl_iff]

theorem ker_stalkMap_clo (X : Scheme.{0}) (z : X) (w : clo z) (p : PrimeSpectrum (X.presheaf.stalk (cloι z w)))
    (hp : X.fromSpecStalk (cloι z w) p = z) : RingHom.ker ((cloι z).stalkMap w).hom = p.asIdeal := by
  let g : PrimeSpectrum ((clo z).presheaf.stalk w) := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : (clo z).fromSpecStalk w g = genericPoint (clo z) := by
    have h := coheight_fromSpecStalk (clo z) w g
    rw [show g.asIdeal.height = 0 from Ideal.height_bot, Order.coheight_eq_zero] at h
    exact ((genericPoint_specializes _).antisymm (h (show _ ≤ genericPoint (clo z) from genericPoint_specializes _))).eq.symm
  have h : X.fromSpecStalk (cloι z w) (Spec.map ((cloι z).stalkMap w) g) = cloι z ((clo z).fromSpecStalk w g) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f => f g)
      (Scheme.SpecMap_stalkMap_fromSpecStalk (cloι z) (x := w))).trans (Scheme.Hom.comp_apply _ _ _))
  rw [hg, cloι_genericPoint] at h
  have h' := (X.fromSpecStalk (cloι z w)).isEmbedding.injective (h.trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal h'

theorem germ_secPull {X V : Scheme.{0}} {L : LB X} (s : L.Sec) (b : V ⟶ X) (v : V) (i : L.ι) (hi : b v ∈ L.U i)
    (hv : v ∈ (L.pull b).U fun _ => i) :
    V.presheaf.germ _ v hv ((GlobalTheory.secPull s b).f fun _ => i) = b.stalkMap v (X.presheaf.germ _ _ hi (s.f i)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem coheight_one_iff (hq : IsAmb q) {z : Y} (w : clo z) (hz : Order.coheight z = 1) :
    Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2 := by
  have hB := GlobalTheory.MixHt.hasDim_basic k Y q hq
  obtain ⟨m, hm⟩ := hB.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint Y)
  have hY : topologicalKrullDim Y = d := (hB.2.2.2.2.2 Y d).1 hd
  cases d with
  | zero =>
    obtain ⟨d', -, hd'⟩ := hm z
    have := GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq 0 hY z d' hd'
    rw [hz] at this
    simp at this
  | succ e => exact ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hY).2 z w hz).2

theorem germ_ne_zero {A : LB Y} {s : A.Sec} (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y} (hi : x ∈ A.U i) :
    Y.presheaf.germ _ x hi (s.f i) ≠ 0 := fun h0 =>
  fnOf_sec_ne_zero hs (gen_mem hi) ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))

variable [IsLocallyNoetherian Y]

theorem mult_eq {A : LB Y} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y}
    (hi : x ∈ A.U i) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1) :
    (divOfSec hA s hs).mult (Y.fromSpecStalk x p) = (Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
        (Y.presheaf.germ _ x hi (s.f i))})).toNat := by
  have hzi : Y.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk Y x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv Y x p
  rw [mult_divOfSec ((coheight_fromSpecStalk Y x p).trans hp) hzi, length_quot_equiv _ _ e, he _ hzi hi]

theorem resCyc_eq (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) {j : B.ι} {x : Y} (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1)
    (ht : Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) {z : Y} (hz : Y.fromSpecStalk x p = z) :
    resCyc hB t (Set.indicator {x} 1) z = (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
      ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat := by
  have hzx : z ⤳ x := hz ▸ specializes_fromSpecStalk Y x p
  have hz1 : Order.coheight z = 1 := hz ▸ (coheight_fromSpecStalk Y x p).trans hp
  have hzt : z ∈ nonzeroLocus t := hz ▸ (mem_nonzeroLocus_iff_notMem t hj p).2 ht
  obtain ⟨w, rfl⟩ : x ∈ Set.range (cloι z) :=
    hzx.mem_closed (cloι z).isClosedEmbedding.isClosed_range ⟨_, cloι_genericPoint z⟩
  have h : genericPoint (clo z) ∈ nonzeroLocus (GlobalTheory.secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rwa [cloι_genericPoint]
  have hw : w ∈ (B.pull (cloι z)).U fun _ => j := Set.mem_iInter.2 fun _ => hj
  have hk := ker_stalkMap_clo Y z w p hz
  let e : (Y.presheaf.stalk (cloι z w) ⧸ p.asIdeal) ≃+* (clo z).presheaf.stalk w :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective ((cloι z).stalkMap_surjective w))
  rw [resCyc, dif_pos h, finsum_eq_single _ w fun w' hw' => by
    rw [Set.indicator_of_notMem (s := {cloι z w}) (a := cloι z w')
      (fun e => hw' ((cloι z).isClosedEmbedding.injective (Set.mem_singleton_iff.1 e))), mul_zero],
    Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one,
    mult_divOfSec ((coheight_one_iff hq w hz1).2 hx) hw, germ_secPull t _ w j hj, length_quot_equiv _ _ e, Int.cast_natCast]
  rfl

theorem of_term_ne_zero (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x z : Y}
    (h : ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z ≠ 0) :
    Order.coheight x = 2 ∧ Order.coheight z = 1 ∧ z ∉ nonzeroLocus s ∧ z ⤳ x := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have h1' : (divOfSec hA s hs).mult z ≠ 0 := by exact_mod_cast h1
  have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h1'
  rw [resCyc] at h2
  split_ifs at h2 with h3
  · obtain ⟨w, hw⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero h2)
    obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 hw
    have h6 : cloι z w = x := Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero h5)
    have h7 := CartierDiv.coheight_eq_one_of_mult_ne_zero (Int.cast_ne_zero.1 h4)
    refine ⟨h6 ▸ (coheight_one_iff hq w hz).1 h7, hz,
      fun h => notMem_supp_divOfSec.2 h (CartierDiv.mem_supp_of_mult_ne_zero h1'), ?_⟩
    have := (genericPoint_specializes w).map (cloι z).continuous
    rwa [cloι_genericPoint, h6] at this
  · exact absurd rfl h2

theorem finsum_eq (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x : Y} {i : A.ι} {j : B.ι} (hi : x ∈ A.U i) (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (P : Finset (PrimeSpectrum (Y.presheaf.stalk x)))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal)
    (hb : ∀ p ∈ P, Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) :
    ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z =
      ((∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ Ideal.span {algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
          (Y.presheaf.germ _ x hi (s.f i))})).toNat * (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
        ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat : ℕ) : ℝ) := by
  classical
  let ι : PrimeSpectrum (Y.presheaf.stalk x) → Y := fun p => Y.fromSpecStalk x p
  have hι : Function.Injective ι := (Y.fromSpecStalk x).isEmbedding.injective
  rw [finsum_eq_sum_of_support_subset (s := P.image ι), Finset.sum_image fun _ _ _ _ h => hι h, Nat.cast_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [resCyc_eq hq hB t hj hx p ((hP p).1 hp).1 (hb p hp) rfl, mult_eq hA s hs hi p ((hP p).1 hp).1,
      Int.cast_natCast, Nat.cast_mul]
  · intro z hz
    obtain ⟨-, h1, h2, h3⟩ := of_term_ne_zero hq hA hB s t hs hz
    obtain ⟨p, rfl⟩ := (Scheme.range_fromSpecStalk (x := x)).ge h3
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hP p).2 ⟨(coheight_fromSpecStalk Y x p).symm.trans h1,
      not_not.1 (mt (mem_nonzeroLocus_iff_notMem s hi p).2 h2)⟩, rfl⟩)

end GlobalTheory.MixHt.CycLoc

namespace GlobalTheory.MixHt

open CycLoc in

theorem finsum_mult_resCyc_indicator_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ x : Y, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst x
  by_cases hx : Order.coheight x = 2
  swap
  · rw [finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hA hB s t hs h).1,
      finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hB hA t s ht h).1]
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hA x
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB x
  have ha := germ_ne_zero hs hi
  have hb := germ_ne_zero ht hj
  have hP := fun p => (finite_height_one _ _ ha).mem_toFinset (a := p)
  have hQ := fun p => (finite_height_one _ _ hb).mem_toFinset (a := p)
  have key (p : PrimeSpectrum (Y.presheaf.stalk x)) (h1 : p.asIdeal.height = 1)
      (h2 : Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal) (h3 : Y.presheaf.germ _ x hj (t.f j) ∈ p.asIdeal) : False :=
    (hst _ ((coheight_fromSpecStalk Y x p).trans h1)).elim
      (fun h => (mem_nonzeroLocus_iff_notMem s hi p).1 h h2) fun h => (mem_nonzeroLocus_iff_notMem t hj p).1 h h3
  rw [finsum_eq hq hA hB s t hs hi hj hx _ hP fun p hp => key p ((hP p).1 hp).1 ((hP p).1 hp).2,
    finsum_eq hq hB hA t s ht hj hi hx _ hQ fun p hp h => key p ((hQ p).1 hp).1 h ((hQ p).1 hp).2]
  refine congrArg _ (GlobalTheory.T.length_sum_height_one_disjoint_divisors _ ?_ _ _ ha hb _ _ hP hQ (Finset.disjoint_left.2 fun p hp hp' =>
    key p ((hP p).1 hp).1 ((hP p).1 hp).2 ((hQ p).1 hp').2))
  rw [ringKrullDim_stalk_eq_coheight, hx]
  rfl

end GlobalTheory.MixHt
