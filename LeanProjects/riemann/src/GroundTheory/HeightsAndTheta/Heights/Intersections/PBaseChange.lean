import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomogIdeal IsMultiProjPrime)

noncomputable section

namespace BaseChange

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem comps_finite {R : Type} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) : (comps P f).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset fun _ h => h.1

theorem mem_comps_of_divCycle_ne_zero {R : Type} [CommRing R] {P W : Ideal (MRing ι R)}
    {f : MRing ι R} (h : NumbersDVR.divCycle P f W ≠ 0) : W ∈ comps P f := by
  unfold NumbersDVR.divCycle at h
  split_ifs at h with hh
  · exact hh
  · exact absurd rfl h

theorem comap_extC {P0 : Ideal (MRing ι ℚ)} [P0.IsPrime] {Z : Ideal (MRing ι ℂ)}
    (hZ : Z ∈ (extC P0).minimalPrimes) : Z.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = P0 :=
  ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC P0 Z hZ

theorem isRelevant_of_comap {P0 : Ideal (MRing ι ℚ)} {Z : Ideal (MRing ι ℂ)} (hP : NumbersDVR.IsRelevant P0)
    (h : Z.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = P0) : NumbersDVR.IsRelevant Z := by
  intro k
  obtain ⟨i, hi⟩ := hP k
  refine ⟨i, fun hX => hi ?_⟩
  rw [← h, Ideal.mem_comap, MvPolynomial.map_X]
  exact hX

theorem sC_not_mem {P0 : Ideal (MRing ι ℚ)} {Z : Ideal (MRing ι ℂ)}
    (h : Z.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = P0) {s : MRing ι ℚ} (hs : s ∉ P0) :
    sC s ∉ Z := fun hZ => hs (h ▸ Ideal.mem_comap.mpr hZ)

theorem isMultiHomog_sC {s : MRing ι ℚ} {a : K → ℕ} (hs : NumbersDVR.IsMultiHomog s a) :
    NumbersDVR.IsMultiHomog (sC s) a := by
  intro d hd
  apply hs
  intro h0
  apply hd
  simp [sC, coeff_map, h0]

theorem isMultiHomogIdeal_extC {P0 : Ideal (MRing ι ℚ)} (h : IsMultiHomogIdeal P0) :
    IsMultiHomogIdeal (extC P0) :=
  FieldNumbers.isMultiHomogIdeal_map (F' := ℂ) h

theorem isProjVar_of_mem_minimalPrimes {P0 : Ideal (MRing ι ℚ)} {e : ℕ} (hP : IsProjVarQ P0 e)
    {Z : Ideal (MRing ι ℂ)} (hZ : Z ∈ (extC P0).minimalPrimes) : IsProjVar Z e := by
  have := hP.1.isPrime
  refine ⟨⟨hZ.1.1, FieldNumbers.PFContracted.isMultiHomogIdeal_of_mem_minimalPrimes
    (isMultiHomogIdeal_extC hP.1.multiHomog) hZ, isRelevant_of_comap hP.1.relevant (comap_extC hZ)⟩, ?_⟩
  rw [← hP.2]
  exact ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC P0 Z hZ

theorem zPts_anti {P Q : Ideal (MRing ι ℂ)} (h : P ≤ Q) : zPts Q ⊆ zPts P :=
  fun _ hz => ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem isLocSmooth_anti {P Q : Ideal (MRing ι ℂ)} (h : P ≤ Q) {g : MCone ι → ℝ}
    (hg : IsLocSmooth P g) : IsLocSmooth Q g := by
  intro z hz
  obtain ⟨U, hU, G, hG, hgG⟩ := hg z (zPts_anti h hz)
  exact ⟨U, hU, G, hG, fun w hw => hgG w ⟨hw.1, zPts_anti h hw.2⟩⟩

theorem isSmoothFn_anti {P Q : Ideal (MRing ι ℂ)} (h : P ≤ Q) {g : MCone ι → ℝ}
    (hg : IsSmoothFn P g) : IsSmoothFn Q g :=
  ⟨fun c hc z hz => hg.1 c hc z (zPts_anti h hz), isLocSmooth_anti h hg.2⟩

theorem multAt_extC_toNat {P0 : Ideal (MRing ι ℚ)} [P0.IsPrime] {Z : Ideal (MRing ι ℂ)}
    [Z.IsPrime] (hZ : Z ∈ (extC P0).minimalPrimes) : (NumbersDVR.multAt (extC P0) Z).toNat = 1 := by
  have h1 := localMult_eq_one_of_isRadical (ReciprocityTheory.AnForm.R.extC_isRadical P0) hZ
  unfold localMult at h1
  rw [dif_pos ‹Z.IsPrime›] at h1
  unfold NumbersDVR.multAt
  rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient]
  exact h1

theorem cast_finsum_mem {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℤ) :
    ((∑ᶠ i ∈ s, f i : ℤ) : ℝ) = ∑ᶠ i ∈ s, (f i : ℝ) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  push_cast
  rfl

end BaseChange

open BaseChange

theorem BCDeg.intersectionNumber_baseChange : BCDeg.Statement := by
  intro K _ _ ι _ P0 e bs hP
  have := hP.1.isPrime
  have hmin : ∀ Z ∈ (extC P0).minimalPrimes, IsProjVar Z e :=
    fun Z hZ => isProjVar_of_mem_minimalPrimes hP hZ
  have hdim : ringKrullDim (MRing ι ℂ ⧸ extC P0) < ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine lt_of_le_of_lt (ringKrullDim_quotient_le_of_minimalPrimes _
      (N := ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) fun Z hZ => (hmin Z hZ).2.le) ?_
    exact_mod_cast (show e + Fintype.card K < e + 1 + Fintype.card K by omega)
  have h1 := (FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ ℂ K ι P0).2 e bs
  rw [← h1]
  change NumbersDVR.intNum ℂ (extC P0) bs = _
  rw [NumbersDVR.IntNumAssoc.full ℂ K ι e (extC P0) (isMultiHomogIdeal_extC hP.1.multiHomog) hdim bs]
  unfold NumbersDVR.cycEval
  rw [finsum_mem_def]
  refine finsum_congr fun W => ?_
  unfold NumbersDVR.idealCycle
  by_cases hW : W ∈ (extC P0).minimalPrimes
  · have : W.IsPrime := hW.1.1
    rw [dif_pos ⟨hW, (hmin W hW).1.relevant⟩, Set.indicator_of_mem hW, multAt_extC_toNat hW]
    simp
  · rw [dif_neg (fun h => hW h.1), Set.indicator_of_notMem hW]
    simp

namespace BaseChange

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem comps_descend {P0 : Ideal (MRing ι ℚ)} {e : ℕ} (hP : IsProjVarQ P0 (e + 1))
    {s : MRing ι ℚ} (hsP : s ∉ P0) {Z Wa : Ideal (MRing ι ℂ)}
    (hZ : Z ∈ (extC P0).minimalPrimes) (hWa : Wa ∈ comps Z (sC s)) :
    Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) ∈ comps P0 s ∧
      Wa ∈ (extC (Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)))).minimalPrimes := by
  have := hP.1.isPrime
  have hZv := isProjVar_of_mem_minimalPrimes hP hZ
  have : Z.IsPrime := hZ.1.1
  have : Wa.IsPrime := hWa.1.1.1
  have hZc := comap_extC hZ
  have hdWa : ringKrullDim (MRing ι ℂ ⧸ Wa) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    FieldNumbers.CutRegular.ringKrullDim_minimalPrime (sC_not_mem hZc hsP) hWa.1
      (by rw [hZv.2, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega])
  have hPsW : P0 ⊔ Ideal.span {s} ≤ Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    refine sup_le ?_ ?_
    · rw [← hZc]
      exact Ideal.comap_mono (le_sup_left.trans hWa.1.1.2)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (le_sup_right.trans hWa.1.1.2) (Ideal.mem_span_singleton_self _)
  obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le hPsW
  have : W'.IsPrime := hW'.1.1
  have hdW' : ringKrullDim (MRing ι ℚ ⧸ W') = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    FieldNumbers.CutRegular.ringKrullDim_minimalPrime hsP hW'
      (by rw [hP.2, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega])
  have hext : extC W' ≤ Wa := Ideal.map_le_iff_le_comap.mpr hW'W
  obtain ⟨Wa', hWa', hWa'Wa⟩ := Ideal.exists_minimalPrimes_le hext
  have : Wa'.IsPrime := hWa'.1.1
  have hdWa' : ringKrullDim (MRing ι ℂ ⧸ Wa') = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hdW']
    exact ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC W' Wa' hWa'
  have heq : Wa' = Wa := by
    by_contra hne
    have h := NumbersDVR.DimStrictDrop.full (MRing ι ℂ) Wa' Wa (lt_of_le_of_ne hWa'Wa hne)
    rw [hdWa, hdWa'] at h
    have h' : ((e + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast h
    have := WithBot.coe_le_coe.mp (show ((((e + Fintype.card K + 1 : ℕ) : ℕ∞)) : WithBot ℕ∞) ≤
      (((e + Fintype.card K : ℕ) : ℕ∞) : WithBot ℕ∞) from h')
    norm_cast at this
    omega
  have hcW : Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = W' := by
    rw [← heq]
    exact ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC W' Wa' hWa'
  refine ⟨⟨hcW ▸ hW', ?_⟩, ?_⟩
  · intro k
    obtain ⟨i, hi⟩ := hWa.2 k
    refine ⟨i, fun h => hi ?_⟩
    rw [Ideal.mem_comap, MvPolynomial.map_X] at h
    exact h
  · rw [hcW, ← heq]
    exact hWa'

theorem sum_components {P0 : Ideal (MRing ι ℚ)} {e : ℕ} (hP : IsProjVarQ P0 (e + 1))
    {s : MRing ι ℚ} (hsP : s ∉ P0)
    (hm : ∀ W ∈ comps P0 s, ∀ Wa ∈ (extC W).minimalPrimes,
      NumbersDVR.divCycle P0 s W = ∑ᶠ Z ∈ (extC P0).minimalPrimes, NumbersDVR.divCycle Z (sC s) Wa)
    (F : Ideal (MRing ι ℂ) → ℝ) :
    ∑ᶠ Z ∈ (extC P0).minimalPrimes, ∑ᶠ Wa ∈ comps Z (sC s),
        (NumbersDVR.divCycle Z (sC s) Wa : ℝ) * F Wa =
      ∑ᶠ W ∈ comps P0 s, (NumbersDVR.divCycle P0 s W : ℝ) * ∑ᶠ Wa ∈ (extC W).minimalPrimes, F Wa := by
  set M := (extC P0).minimalPrimes with hMdef
  set V := ⋃ Z ∈ M, comps Z (sC s) with hVdef
  have hM : M.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hV : V.Finite := hM.biUnion fun Z _ => comps_finite Z (sC s)
  have hL : ∀ Z ∈ M, ∑ᶠ Wa ∈ comps Z (sC s), (NumbersDVR.divCycle Z (sC s) Wa : ℝ) * F Wa =
      ∑ᶠ Wa ∈ V, (NumbersDVR.divCycle Z (sC s) Wa : ℝ) * F Wa := by
    intro Z hZ
    refine finsum_mem_inter_support_eq' _ _ _ fun Wa hWa => ⟨fun h => Set.mem_biUnion hZ h, fun _ => ?_⟩
    refine mem_comps_of_divCycle_ne_zero fun h0 => ?_
    apply Function.mem_support.mp hWa
    simp [h0]
  rw [finsum_mem_congr rfl hL, finsum_mem_comm _ hM hV]
  have hR : ∀ W ∈ comps P0 s, (NumbersDVR.divCycle P0 s W : ℝ) * ∑ᶠ Wa ∈ (extC W).minimalPrimes, F Wa =
      ∑ᶠ Wa ∈ (extC W).minimalPrimes, ∑ᶠ Z ∈ M, (NumbersDVR.divCycle Z (sC s) Wa : ℝ) * F Wa := by
    intro W hW
    rw [mul_finsum_mem' _ _ (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun Wa hWa => ?_
    rw [hm W hW Wa hWa, cast_finsum_mem hM, finsum_mem_mul' _ _ hM]
  have hdisj : (comps P0 s).PairwiseDisjoint fun W => (extC W).minimalPrimes := by
    intro W1 h1 W2 h2 hne
    refine Set.disjoint_left.mpr fun Wa ha hb => hne ?_
    have : W1.IsPrime := h1.1.1.1
    have : W2.IsPrime := h2.1.1.1
    rw [← ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC W1 Wa ha,
      ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC W2 Wa hb]
  rw [finsum_mem_congr rfl hR, ← finsum_mem_biUnion
    (f := fun Wa => ∑ᶠ Z ∈ M, (NumbersDVR.divCycle Z (sC s) Wa : ℝ) * F Wa) hdisj
    (comps_finite P0 s) fun W _ => Ideal.finite_minimalPrimes_of_isNoetherianRing _ _]
  refine finsum_mem_inter_support_eq' _ _ _ fun Wa hWa => ?_
  obtain ⟨Z, hZ, hZW⟩ := exists_ne_zero_of_finsum_mem_ne_zero (Function.mem_support.mp hWa)
  have hWaZ : Wa ∈ comps Z (sC s) := mem_comps_of_divCycle_ne_zero fun h0 => hZW (by simp [h0])
  obtain ⟨h1, h2⟩ := comps_descend hP hsP hZ hWaZ
  exact ⟨fun _ => Set.mem_biUnion h1 h2, fun _ => Set.mem_biUnion hZ hWaZ⟩

end BaseChange

theorem BCCommon.intersectionNumber_baseChange : BCCommon.Statement := by
  intro K _ _ ι _ P0 e s s' a a' Z Wa hP _ hsP _ hs'P hZ h1 h2
  exact ⟨(comps_descend hP hsP hZ h1).1, (comps_descend hP hs'P hZ h2).1⟩

theorem DegreesQ.proof (hDeg : Degrees.Statement) : DegreesQ.Statement := by
  intro K _ _ ι _ P0 e L hP hRes hL
  have hM : (extC P0).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  unfold zIntQ
  rw [BCDeg.intersectionNumber_baseChange K ι P0 e _ hP, cast_finsum_mem hM]
  exact finsum_mem_congr rfl fun Z hZ => hDeg K ι Z e L (isProjVar_of_mem_minimalPrimes hP hZ)
    (hRes Z hZ) fun j => isLocSmooth_anti hZ.1.2 (hL j)

theorem ProjectiveLineOverRationals.proof (hPL1 : PoincareLelongAlt.Statement) (hBCM : BCMult.Statement) : ProjectiveLineOverRationals.Statement := by
  intro K _ _ ι _ P0 e L A s v hP hResZ hResW hL hA hAs hv
  obtain ⟨a, hAa, hs, hsP⟩ := hAs
  have := hP.1.isPrime
  have hM : (extC P0).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hZ : ∀ Z ∈ (extC P0).minimalPrimes,
      zInt Z (e + 1) (Fin.cons v fun j => logH (L j)) (secNorm A (sC s)) =
        (∑ᶠ Wa ∈ comps Z (sC s), (NumbersDVR.divCycle Z (sC s) Wa : ℝ) *
          zInt Wa e (fun j => logH (L j)) v) -
          zInt Z (e + 1) (Fin.cons (logH A) fun j => logH (L j)) v := by
    intro Z hZ
    exact hPL1 K ι Z e L A (sC s) v (isProjVar_of_mem_minimalPrimes hP hZ) (hResZ Z hZ)
      (fun Wa hWa => hResW _ (comps_descend hP hsP hZ hWa).1 Wa (comps_descend hP hsP hZ hWa).2)
      (fun j => isLocSmooth_anti hZ.1.2 (hL j)) (isLocSmooth_anti hZ.1.2 hA)
      ⟨a, hAa, isMultiHomog_sC hs, sC_not_mem (comap_extC hZ) hsP⟩ (isSmoothFn_anti hZ.1.2 hv)
  unfold zIntQ
  rw [finsum_mem_congr rfl hZ, finsum_mem_sub_distrib _ _ hM,
    sum_components hP hsP (fun W hW Wa hWa => hBCM K ι P0 e s a W Wa hP hs hsP hW hWa)
      (fun Wa => zInt Wa e (fun j => logH (L j)) v)]

theorem ProjectivePlaneOverRationals.proof (hPL2 : ProjectiveLineTwo.Statement) (hBCM : BCMult.Statement) : ProjectivePlaneOverRationals.Statement := by
  intro K _ _ ι _ P0 e L A A' s s' hP hResZ hResW hResW' hL hA hA' hAs hAs' hnc
  obtain ⟨a, hAa, hs, hsP⟩ := hAs
  obtain ⟨a', hAa', hs', hs'P⟩ := hAs'
  have := hP.1.isPrime
  have hM : (extC P0).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have key : ∑ᶠ Z ∈ (extC P0).minimalPrimes,
      ((∑ᶠ Wa ∈ comps Z (sC s), (NumbersDVR.divCycle Z (sC s) Wa : ℝ) *
          zInt Wa e (fun j => logH (L j)) (secNorm A' (sC s'))) +
        zInt Z (e + 1) (Fin.cons (logH A') fun j => logH (L j)) (secNorm A (sC s))) =
      ∑ᶠ Z ∈ (extC P0).minimalPrimes,
      ((∑ᶠ Wa ∈ comps Z (sC s'), (NumbersDVR.divCycle Z (sC s') Wa : ℝ) *
          zInt Wa e (fun j => logH (L j)) (secNorm A (sC s))) +
        zInt Z (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (secNorm A' (sC s'))) := by
    refine finsum_mem_congr rfl fun Z hZ => ?_
    exact hPL2 K ι Z e L A A' (sC s) (sC s') (isProjVar_of_mem_minimalPrimes hP hZ) (hResZ Z hZ)
      (fun Wa hWa => hResW _ (comps_descend hP hsP hZ hWa).1 Wa (comps_descend hP hsP hZ hWa).2)
      (fun Wa hWa => hResW' _ (comps_descend hP hs'P hZ hWa).1 Wa (comps_descend hP hs'P hZ hWa).2)
      (fun j => isLocSmooth_anti hZ.1.2 (hL j)) (isLocSmooth_anti hZ.1.2 hA)
      (isLocSmooth_anti hZ.1.2 hA')
      ⟨a, hAa, isMultiHomog_sC hs, sC_not_mem (comap_extC hZ) hsP⟩
      ⟨a', hAa', isMultiHomog_sC hs', sC_not_mem (comap_extC hZ) hs'P⟩
      fun Wa h1 h2 => hnc _ (comps_descend hP hsP hZ h1).1 (comps_descend hP hs'P hZ h2).1
  rw [finsum_mem_add_distrib hM, finsum_mem_add_distrib hM,
    sum_components hP hsP (fun W hW Wa hWa => hBCM K ι P0 e s a W Wa hP hs hsP hW hWa)
      (fun Wa => zInt Wa e (fun j => logH (L j)) (secNorm A' (sC s'))),
    sum_components hP hs'P (fun W hW Wa hWa => hBCM K ι P0 e s' a' W Wa hP hs' hs'P hW hWa)
      (fun Wa => zInt Wa e (fun j => logH (L j)) (secNorm A (sC s)))] at key
  unfold zIntQ
  exact key

theorem BaseChange.proof (hPL1 : PoincareLelongAlt.Statement) (hPL2 : ProjectiveLineTwo.Statement) (hDeg : Degrees.Statement)
    (hBCM : BCMult.Statement) : ProjectiveLineOverRationals.Statement ∧ ProjectivePlaneOverRationals.Statement ∧ DegreesQ.Statement :=
  ⟨ProjectiveLineOverRationals.proof hPL1 hBCM, ProjectivePlaneOverRationals.proof hPL2 hBCM, DegreesQ.proof hDeg⟩

end

end GroundTheory.Heights₂.Heights.Inter
