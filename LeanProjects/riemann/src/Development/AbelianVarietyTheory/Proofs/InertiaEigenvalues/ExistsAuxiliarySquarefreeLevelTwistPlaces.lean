import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallCoeffFieldEmbeddingCompHostMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfOfAuxiliarySplitLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPosition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFibreIdempotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CurveOverOfRayIn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedFieldFibres
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverLevelOneOverSmallField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DictionaryCharacterRightInvariantCoreLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsOfReadingBoundedCuspidalHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
  Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.UnivRat

theorem exists_field_adjoin_root (k : Subfield ℂ) (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [Normal ℚ L]
    (hL : L.toSubfield ≤ k) {z : ℂ} (hz : z ∈ k) (ho : IsOfFinOrder z) :
    ∃ L' : IntermediateField ℚ ℂ, FiniteDimensional ℚ L' ∧ Normal ℚ L' ∧ L ≤ L' ∧ L'.toSubfield ≤ k ∧ z ∈ L' := by
  have hn : 0 < orderOf z := ho.orderOf_pos
  haveI : NeZero (orderOf z) := ⟨hn.ne'⟩
  have hζ : IsPrimitiveRoot z (orderOf z) := IsPrimitiveRoot.orderOf z
  let p : Polynomial ℚ := Polynomial.X ^ (orderOf z) - 1
  have hp0 : p ≠ 0 := by simpa [p] using Polynomial.X_pow_sub_C_ne_zero hn (1 : ℚ)
  have hroots : ∀ y : ℂ, y ∈ p.rootSet ℂ ↔ y ^ (orderOf z) = 1 := fun y => by
    rw [Polynomial.mem_rootSet, and_iff_right hp0]
    simp [p, sub_eq_zero]
  let C : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  haveI hCs : Polynomial.IsSplittingField ℚ C p :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional ℚ C := Polynomial.IsSplittingField.finiteDimensional C p
  haveI : Normal ℚ C := Normal.of_isSplittingField p
  refine ⟨L ⊔ C, inferInstance, @IntermediateField.normal_sup ℚ ℂ _ _ _ L C (by convert ‹Normal ℚ L› <;> exact Subsingleton.elim _ _) (by convert ‹Normal ℚ C› <;> exact Subsingleton.elim _ _), le_sup_left, fun x hx => ?_,
    (le_sup_right : C ≤ L ⊔ C) (IntermediateField.subset_adjoin ℚ _ ((hroots z).2 (pow_orderOf_eq_one z)))⟩
  let S : IntermediateField ℚ ℂ := Subfield.toIntermediateField k fun r => by
    simpa using SubfieldClass.ratCast_mem k r
  have hS : L ⊔ C ≤ S := by
    refine sup_le (fun x hx => hL hx) ?_
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    obtain ⟨t, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((hroots y).1 hy)
    exact pow_mem hz t
  exact hS hx

theorem exists_field_adjoin_roots (k : Subfield ℂ) {Z : Set ℂ} (hZ : Z.Finite) (hz : ∀ z ∈ Z, z ∈ k ∧ IsOfFinOrder z)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [Normal ℚ L] (hL : L.toSubfield ≤ k) :
    ∃ L' : IntermediateField ℚ ℂ, FiniteDimensional ℚ L' ∧ Normal ℚ L' ∧ L ≤ L' ∧ L'.toSubfield ≤ k ∧ ∀ z ∈ Z, z ∈ L' := by
  induction Z, hZ using Set.Finite.induction_on with
  | empty => exact ⟨L, inferInstance, inferInstance, le_rfl, hL, fun _ h => h.elim⟩
  | @insert a s _ _ ih =>
    obtain ⟨L₁, _, _, h1, h2, h3⟩ := ih fun z h => hz z (Set.mem_insert_of_mem _ h)
    obtain ⟨L₂, i1, i2, h4, h5, h6⟩ := exists_field_adjoin_root k L₁ h2 (hz a (Set.mem_insert _ _)).1
      (hz a (Set.mem_insert _ _)).2
    refine ⟨L₂, i1, i2, h1.trans h4, h5, ?_⟩
    rintro z (rfl | h)
    exacts [h6, h4 (h3 z h)]

variable {D : D7}

open scoped Pointwise in

theorem absNorm_ccK_not_mem {P : Pl D.host.E} (h : FractionalIdeal.count D.host.E P D.host.AA = 0)
    (h' : FractionalIdeal.count D.host.E (Formalism.L2.DIV.conjPl P) D.host.AA = 0) :
    ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro hm
  have h1 := ((GlobalTheory.HalfCompare.primeToAA_iff P).1 h).1
  have h2 := ((GlobalTheory.HalfCompare.primeToAA_iff _).1 h').1
  have e : D.host.ccE * (D.host.conj • D.host.ccE) = Ideal.span {((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E)} := by
    apply FractionalIdeal.coeIdeal_injective (K := D.host.E)
    beta_reduce
    rw [FractionalIdeal.coeIdeal_mul, Formalism.IndefR.Fin.ccNorm D.R D.host, FractionalIdeal.coeIdeal_span_singleton, map_natCast]
  have hd : P.asIdeal ∣ D.host.ccE * (D.host.conj • D.host.ccE) := by rw [e, Ideal.dvd_span_singleton]; exact hm
  rcases P.prime.dvd_or_dvd hd with h3 | h3
  · exact h1 h3
  · refine h2 (Ideal.dvd_iff_le.2 fun x hx => ?_)
    have e2 : Formalism.L2.DIV.starOHom x = D.host.conj • x := RingOfIntegers.ext (by
      change star (x : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
      rw [Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul, Formalism.BasicNotions.Examples₂.star_eq_conj])
    change Formalism.L2.DIV.starOHom x ∈ P.asIdeal
    rw [e2]
    exact Ideal.le_of_dvd h3 (Ideal.smul_mem_pointwise_smul _ _ _ hx)

theorem cls_splitK {p : ℕ} (h : D.host.cls p = .splitK) :
    p ∉ D.host.small ∧ p ≠ D.host.q ∧ jacobiSym (-(D.host.d : ℤ)) p = 1 := by
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4
  exact ⟨h1, h2, h4⟩

theorem prod_split_primes_isAuxiliarySplitSquarefreeLevel (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ D.host.cls p = .splitK ∧ (∀ k, p ≠ D.host.g k) ∧
    Nat.Coprime p (Ideal.absNorm D.host.ccK)) : IsAuxiliarySplitSquarefreeLevel D (D.host.g 0 * D.host.g 1) (∏ p ∈ s, p) := by
  refine ⟨Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one fun p hp =>
    (hs p hp).1.odd_of_ne_two (UpperTheory.Small.ne_two D.host (cls_splitK (hs p hp).2.1).1), ?_, fun p hp hd => ?_,
    Nat.Coprime.prod_left fun p hp => Nat.Coprime.mul_right
      ((Nat.coprime_primes (hs p hp).1 (D.host.g_prime 0)).2 ((hs p hp).2.2.1 0))
      ((Nat.coprime_primes (hs p hp).1 (D.host.g_prime 1)).2 ((hs p hp).2.2.1 1)),
    Nat.Coprime.prod_left fun p hp => Nat.Coprime.mul_right
      (UpperTheory.Ram.coprime_QSq D.host (hs p hp).1 (cls_splitK (hs p hp).2.1).1 (cls_splitK (hs p hp).2.1).2.1).symm (hs p hp).2.2.2⟩
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_) fun p hp => (hs p hp).1.squarefree
    exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hs a ha).1 (hs b hb).1).2 hab)
  · obtain ⟨a, ha, h⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
    rw [(Nat.prime_dvd_prime_iff_eq hp (hs a ha).1).1 h]
    exact (cls_splitK (hs a ha).2.1).2.2

def pDel (D : D7) (l : ℕ) : ℕ := if l = D.host.pde then D.host.pde' else D.host.pde

theorem pDel_cases (l : ℕ) : pDel D l = D.host.pde ∨ pDel D l = D.host.pde' := by
  unfold pDel
  split_ifs
  exacts [Or.inr rfl, Or.inl rfl]

theorem isDelta_delAt (C : Formalism.L2.Host.CharFrame D) (l : ℕ) : Formalism.L2.Host.IsDelta (pDel D l) (C.delAt l) := by
  unfold pDel Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [C.isDel', C.isDel]

theorem valuesIn_delAt {C : Formalism.L2.Host.CharFrame D} (h : Formalism.L2.Host.ValLL0 D C) (l : ℕ) :
    (C.delAt l).ValuesIn 0 (embLL0 D) := by
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [h.del', h.del]

theorem mem_pD_iff (i : D.ntw.Tw) (P : Pl D.host.E) :
    P ∈ D.ntw.pD i ↔ ((pDel D (D.ntw.l i) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Finset.mem_coe, D.ntw.pD_eq i]
  rfl

theorem exists_auxiliary_squarefree_level_twistPlaces {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) (i : D.ntw.Tw) (Q : Finset (Pl D.host.E))
    (hcls : Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q) (hS : Disjoint Q (D.ntw.S0 i)) :
    ∃ N : ℕ, N ≠ 0 ∧ N.Coprime (D.ntw.l i) ∧ IsAuxiliarySplitSquarefreeLevel D (D.host.g 0 * D.host.g 1) (pDel D (D.ntw.l i) * N) ∧
      ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ P.asIdeal := by
  classical
  choose q hq using hcls
  let s : Finset ℕ := Q.attach.image fun P => q P.1 P.2
  have key : ∀ p ∈ s, p.Prime ∧ D.host.cls p = .splitK ∧ (∀ n : ℕ, placesOver D.host.E n ⊆ ↑(D.ntw.S0 i) → p ≠ n) ∧
      Nat.Coprime p (Ideal.absNorm D.host.ccK) := by
    intro p hp
    obtain ⟨⟨P, hP⟩, -, rfl⟩ := Finset.mem_image.1 hp
    have h0 : P ∉ D.ntw.S0 i := Finset.disjoint_left.1 hS hP
    obtain ⟨h1, -, h3, h4⟩ := hq P hP
    refine ⟨h1, h3, fun n hn e => h0 (hn ?_), (Nat.Prime.coprime_iff_not_dvd h1).2 fun hd => ?_⟩
    · change ((n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
      exact e ▸ h4
    · have hc : Formalism.BasicNotions.IsConjPl D.host (Formalism.L2.DIV.conjPl P) P := by
        intro x y hxy
        have e2 : Formalism.L2.DIV.starOHom x = y := RingOfIntegers.ext (by
          change star (x : D.host.E) = (y : D.host.E)
          rw [hxy, Formalism.BasicNotions.Examples₂.star_eq_conj])
        change Formalism.L2.DIV.starOHom x ∈ P.asIdeal ↔ _
        rw [e2]
      exact absNorm_ccK_not_mem (hρ.goodSetup_count_eq_zero_off_badPlaces i P h0) (hρ.goodSetup_count_eq_zero_off_badPlaces i _ fun h => h0 (hρ.goodSetup_badPlaces_conj i _ h _ hc))
        (GlobalTheory.HalfCompare.mem_of_dvd h4 hd)
  have hpD : placesOver D.host.E (pDel D (D.ntw.l i)) ⊆ ↑(D.ntw.S0 i) := fun P hP =>
    D.ntw.primes_subset_exceptional i ((mem_pD_iff i P).2 hP)
  have hns : pDel D (D.ntw.l i) ∉ s := fun h => (key _ h).2.2.1 _ hpD rfl
  refine ⟨∏ p ∈ s, p, Finset.prod_ne_zero_iff.2 fun p hp => (key p hp).1.ne_zero,
    Nat.Coprime.prod_left fun p hp => (Nat.coprime_primes (key p hp).1 (D.ntw.lPrime i).out).2
      ((key p hp).2.2.1 _ (D.ntw.twistExcludedPlaces_contains_residueChar i)), ?_, fun P hP => GlobalTheory.HalfCompare.mem_of_dvd (hq P hP).2.2.2
      (Finset.dvd_prod_of_mem _ (Finset.mem_image.2 ⟨⟨P, hP⟩, Finset.mem_attach _ _, rfl⟩))⟩
  rw [← Finset.prod_insert (f := fun p => p) hns]
  refine prod_split_primes_isAuxiliarySplitSquarefreeLevel _ fun p hp => ?_
  rcases Finset.mem_insert.1 hp with rfl | hp
  · rcases pDel_cases (D := D) (D.ntw.l i) with e | e <;> rw [e]
    · exact ⟨D.host.pde_prime, hde.1, fun k => (D.host.pde_ne_g k).1,
        (D.host.ccK_coprime _ (by simp [D.host.pde_level.1])).symm⟩
    · exact ⟨D.host.pde'_prime, hde.2, fun k => (D.host.pde_ne_g k).2,
        (D.host.ccK_coprime _ (by simp [D.host.pde_level.2])).symm⟩
  · exact ⟨(key p hp).1, (key p hp).2.1, fun k => (key p hp).2.2.1 _ (D.ntw.placesOver_subset_exceptional i k), (key p hp).2.2.2⟩

section Datum

variable {S T : HSp D}

open Classical in

theorem isIdemSum_halfIdem {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    IsIdemSum (halfIdem Pg Q) (Pg.image Formalism.L2.DIV.conjPl ∪ Q) := by
  obtain ⟨R, h1, h2, hR⟩ := h.split
  have hc := GlobalTheory.RefDatumLev.isIdemSum_conjPl (hR.mono h1).isIdemSum
  have hA : ∀ P ∈ Pg.image Formalism.L2.DIV.conjPl, Formalism.L2.NTheta.IsIdemAt (idemAt P) P := fun P hP =>
    SplitSet.isIdemAt ⟨_, hc⟩ hP
  have hd : Disjoint (Pg.image Formalism.L2.DIV.conjPl) Q := Finset.disjoint_left.2 fun P hP hQ => by
    obtain ⟨P₀, h0, rfl⟩ := Finset.mem_image.1 hP
    have a1 : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P₀)) (Formalism.L2.DIV.conjPl P₀) :=
      GlobalTheory.MovedIdem.isIdemAt_conj (hR.isIdemAt (h1 h0)) fun x => Iff.rfl
    have a2 := hR.mul_conj (h2 hQ) (h1 h0)
    rw [idemAt_eq a1, a1.1.1] at a2
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Formalism.L2.DIV.conjPl P₀).ne_bot
    refine (a1.2 x hx0).1 hx ?_
    rw [a2, zero_mul, map_zero]
    exact zero_mem _
  refine ⟨⟨idemAt, fun P hP => ?_, ?_⟩, h.isOrthSum.2⟩
  · rcases Finset.mem_union.1 hP with hP | hP
    exacts [hA P hP, hR.isIdemAt (h2 hP)]
  · rw [Finset.sum_union hd, halfIdem, ← idem_eq hc]
    rfl

theorem frMapO_add_nsmul (F : Frame S T) (k : ℕ) (x u : WO S T) :
    frMapO S T F.βS F.βT (x + k • u) = frMapO S T F.βS F.βT x + k • frMapO S T F.βS F.βT u := by
  ext a c
  rw [GlobalTheory.PlaceDatum.frMapO_add, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]

open Classical in

theorem isLevDatum_vecAt {B : Base S T} (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (hbad : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ Q →
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (N : ℕ) (hN : ∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q ∪ Q → (N : 𝓞 D.host.E) ∈ PP.asIdeal) (k : Subfield ℂ)
    (h1 : ∀ u, ((B.G.P.chi u : ℂˣ) : ℂ) ∈ k) (h2 : ∀ PP ∈ B.G.Pg, ∀ x, ((B.G.muC PP x : ℂˣ) : ℂ) ∈ k)
    (h3 : ∀ PP ∈ B.de.Q, ∀ x, ((B.de.resC PP x : ℂˣ) : ℂ) ∈ k)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h4 : ∀ PP y, φ PP y ∈ k) :
    IsLevDatum B.F.ψ S T B.F.ΛS B.F.ΛT N k B.F.f₀ (B.vecAt Q φ) := by
  have hlat := fun x => @GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem D S T B.F hB.frame _ _ hQ.1 hbad x
  refine ⟨_, _, _, isIdemSum_halfIdem hQ.1, fun PP hPP => ?_, fun t ht => ?_, fun u hu hue t => ?_, fun t => ?_,
    Base.isThetaAt_vecAt hB hQ φ⟩
  · rcases Finset.mem_union.1 hPP with h | h
    · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 h
      show Formalism.L2.DIV.starOHom ((N : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
      rw [map_natCast]
      exact hN P0 (Or.inl hP0)
    · exact hN PP (Or.inr h)
  · unfold Frame.datumFn at ht
    have c1 := left_ne_zero_of_mul ht
    have c2 := right_ne_zero_of_mul ht
    have d1 := (ite_ne_right_iff.1 c1).1
    have d2 := (ite_ne_right_iff.1 c2).1
    exact ⟨(hlat t d1.1).2 ⟨d1.2, d2.2⟩, d1.1⟩
  · obtain ⟨i1, i2⟩ := (hlat u hue).1 hu
    have e1 : frMapAdj S T B.F.βS B.F.βT (t + N • u) = frMapAdj S T B.F.βS B.F.βT t + N • frMapAdj S T B.F.βS B.F.βT u := by
      rw [GlobalTheory.RefDatumLev.frMapAdj_add', GlobalTheory.RefDatumLev.frMapAdj_nsmul']
    have hKu : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) (N • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hh : IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) (t + N • u) ↔ IsHalf (halfIdem B.G.Pg (B.de.Q ∪ Q)) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    unfold Frame.datumFn
    rw [e1, frMapO_add_nsmul]
    simp only [hh, GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i1, GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i2]
    congr 1
    · refine ite_congr rfl (fun hc => ?_) fun _ => rfl
      exact GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP =>
        GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i1 _ (hN PP (Or.inl hPP))
    · refine ite_congr rfl (fun hc => ?_) fun _ => rfl
      unfold Base.locFn
      congr 1
      · exact Finset.prod_congr rfl fun PP hPP => by
          beta_reduce
          rw [GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i2 _ (hN PP (Or.inr (Finset.mem_union_left _ hPP)))]
      · exact Finset.prod_congr rfl fun PP _ => by
          beta_reduce
          rw [GlobalTheory.RefDatumLev.redM_add_nsmul PP.1 hc.2 i2 _ (hN PP.1 (Or.inr (Finset.mem_union_right _ PP.2)))]
  · unfold Frame.datumFn
    refine mul_mem ?_ ?_
    · split_ifs
      · unfold omegaG
        split_ifs
        · refine mul_mem (mul_mem (h1 _) (prod_mem fun PP _ => prod_mem fun c hc => absurd hc (Finset.notMem_empty _))) ?_
          exact prod_mem fun PP _ => inv_mem (h2 PP.1 PP.2 _)
        · exact zero_mem _
      · exact zero_mem _
    · split_ifs
      · unfold Base.locFn
        refine mul_mem (prod_mem fun PP hPP => ?_) (prod_mem fun PP _ => h4 PP _)
        unfold GlobalTheory.ExportSeries.flat
        split_ifs
        · exact h3 PP hPP _
        · exact zero_mem _
      · exact zero_mem _

end Datum

section Det

variable {C : Type} [AddCommGroup C] {u : UnivTwist D C} {Q : Finset (Pl D.host.E)}

theorem delQ_det_eq_one (hu : u.Good Q) (V : HSp D) {N : ℕ} (hN : Odd N) (hQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    (w : GA D V) (hw : ∃ z ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V w) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • z) : detChar V (u.delQ Q) w = 1 := by
  ext PP
  have hg := hu.2 PP.1 PP.2
  exact congrArg Multiplicative.toAdd (GlobalTheory.FibreIdem.char_root_eq_one' V (u.del PP.1) N hN hg.real
    (GlobalTheory.FibreIdem.chi_eq_one_of_finPart D _ hg.isOpen)
    (GlobalTheory.FibreIdem.chi_eq_one_of_cong D PP.1 (u.del PP.1) u.kap hg N (hQ PP.1 PP.2)) w _ (isDetRoot_detRoot V w) hw)

theorem delQ_det_laws (hu : u.Good Q) (V : HSp D) {N : ℕ} (hN : Odd N) (hQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) :
    (∀ h h' : GA D V, finHom V h = finHom V h' → detChar V (u.delQ Q) h = detChar V (u.delQ Q) h') ∧
    (∀ γ ∈ GQ V, ∀ h, detChar V (u.delQ Q) (γ * h) = detChar V (u.delQ Q) h) ∧
    ∀ k : GA D V, GlobalTheory.Member.FinCong V N k → ∀ h, detChar V (u.delQ Q) (h * k) = detChar V (u.delQ Q) h := by
  have hF := hu.delQ_real
  refine ⟨fun h h' e => ?_, fun γ hγ h => ?_, fun k hk h => ?_⟩
  · have e1 : h' = h * (h⁻¹ * h') := by group
    rw [e1, detChar_mul hF, delQ_det_eq_one hu V hN hQ (h⁻¹ * h') ⟨0, zero_mem _, by
      rw [map_mul, map_inv, e, inv_mul_cancel]; simp⟩, mul_one]
  · rw [detChar_mul hF, detChar_rat hF (fun x => by
      ext PP
      exact congrArg Multiplicative.toAdd ((hu.2 PP.1 PP.2).rat x)) hγ, one_mul]
  · obtain ⟨w, hw, hwe⟩ := GlobalTheory.DetFibre.det_cong_of_finCong V N (by rintro rfl; exact Nat.not_odd_zero hN) k hk
    rw [detChar_mul hF, delQ_det_eq_one hu V hN hQ k ⟨w, by rwa [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers], hwe⟩, mul_one]

end Det

section Cover

variable {T : CoreJ D} {j : Fin D.R.m} {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} {C : Cover T ((j : ℕ) + 1) T.σ₀}
  {κ : WeightFamilies.Wt D ((j : ℕ) + 1)}

theorem castDict_sum {V W : HSp D} (e : V = W) {ι : Type} (s : Finset ι) (ψ : ι → GA D V → ℂ) :
    castDict e (∑ a ∈ s, ψ a) = ∑ a ∈ s, castDict e (ψ a) := by
  subst e
  rfl

variable [Algebra T.Q.c.F D.what₂.LL]

theorem isRat_sum {ι : Type} [Fintype ι] {φ : ι → GA D (Wc D j) → ℂ} (h : ∀ a, IsRat T j hV C κ (φ a)) :
    IsRat T j hV C κ (∑ a, φ a) := by
  choose ψ h1 h2 using h
  refine ⟨∑ a, ψ a, Finset.sum_induction _ (· ∈ C.ratForms (wtA κ) κ.n)
    (fun _ _ => GlobalTheory.CoverRead.Test.add_mem_ratForms C _ _) (GlobalTheory.CoverRead.Test.zero_mem_ratForms C _ _) fun a _ => h1 a, ?_⟩
  rw [castDict_sum]
  exact Finset.sum_congr rfl fun a _ => h2 a

open Classical in

theorem isRat_fibre (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (hU : C.IsUnif)
    (hray : RayIn D (T.Q.l.M * C.d.pd) C.σ₂.fieldRange) {A : Type} [AddCommGroup A] {u : UnivTwist D A}
    {Q : Finset (Pl D.host.E)} (hu : u.Good Q) (hQ : ∀ PP ∈ Q, ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (a : ↥Q → A) {φ : GA D (Wc D j) → ℂ} (h : IsRat T j hV C κ φ) :
    IsRat T j hV C κ fun g => (if Multiplicative.toAdd (detChar (Wc D j) (u.delQ Q) g) = a then 1 else 0) * φ g := by
  obtain ⟨ψ, h1, rfl⟩ := h
  have hM : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have h3 : 3 ≤ C.d.l₂.M := C.d.l₂.three_le
  rw [← hM] at hray hQ
  obtain ⟨l1, l2, l3⟩ := delQ_det_laws hu (T.V ((j : ℕ) + 1) T.σ₀) C.d.l₂.odd hQ
  have key := (GlobalTheory.T.levelCover_forms_mul_componentFunction D T hT _ (inR j) T.σ₀ T.toCore.good_σ₀ C hU C.d.l₂.M (by omega) dvd_rfl
    (Or.inr (GlobalTheory.TwistRat.Field.curveOver_of_rayIn hRF D T.Q hT.pins.1 _ h3 _ C.σ₂ hray))
    (fun g => if Multiplicative.toAdd (detChar _ (u.delQ Q) g) = a then 1 else 0)
    (fun g g' e => by rw [l1 g g' e]) (fun γ hγ g => by rw [l2 γ hγ g]) (fun k _ hk g => by rw [l3 k hk g])
    (wtA κ) κ.n).1 ψ h1
  refine ⟨_, key, ?_⟩
  have e : ∀ {V W : HSp D} (e : V = W) (ψ : GA D V → ℂ),
      castDict e (fun g => C.σ₂ (if Multiplicative.toAdd (detChar V (u.delQ Q) g) = a then 1 else 0) * ψ g) =
        fun g => (if Multiplicative.toAdd (detChar W (u.delQ Q) g) = a then 1 else 0) * castDict e ψ g := by
    rintro V _ rfl ψ
    funext g
    change C.σ₂ (if Multiplicative.toAdd (detChar V (u.delQ Q) g) = a then 1 else 0) * ψ g =
      (if Multiplicative.toAdd (detChar V (u.delQ Q) g) = a then 1 else 0) * ψ g
    split_ifs <;> simp
  exact e hV ψ

theorem exists_sum_of_isRat (hT : LawsJ T) (hlast : κ.LastPos) (hn : 8 * D.R.f * D.R.r + 4 ≤ κ.n) (hU : C.IsUnif)
    (hP : C.IsPinned (wtA κ) κ.n)
    (hmu : ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, T.mu ((j : ℕ) + 1) T.σ₀ (g * k) = T.mu ((j : ℕ) + 1) T.σ₀ g)
    {φ : GA D (Wc D j) → ℂ} (h : IsRat T j hV C κ φ)
    (hinv : ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * cast (congrArg (GA D) hV) k) = φ g) :
    ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (f : Fin m → T.toCore.cuspA ((j : ℕ) + 1) (wtA κ) κ.n),
      φ = ∑ k, C.σ₂ (x k) • castDict hV (T.phiJ ((j : ℕ) + 1) T.σ₀ (wtA κ) (f k : T.R ((j : ℕ) + 1))) := by
  obtain ⟨φ', hφ'm, rfl⟩ := h
  have hspan : Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA κ) κ.n) ≤
      Submodule.span ℂ (rdU (T.U ((j : ℕ) + 1) T.σ₀) '' {f | f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA κ) κ.n ∧
        rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
          (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA κ) κ.n)}) := by
    refine (GlobalTheory.OntoCore.holSub0_le_span_cuspA D T hT _ (inR j) κ hlast hn T.σ₀ T.toCore.good_σ₀).trans
      (Submodule.span_mono (Set.image_mono fun f hf => ⟨Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf, ?_, ?_⟩))
    · exact ((Formalism.L2.Pj.mem_cusp _ _ _ _ _ f).1 hf).2 T.σ₀ T.toCore.good_σ₀
    · exact Formalism.L2.Pj.rdU_mem_offZero _ _
  have hinv' : ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ' (g * k) = φ' g := fun k hk g => by
    rw [LevelInv.apply_eq_castDict hV φ' (g * k), LevelInv.apply_eq_castDict hV φ' g, LevelInv.cast_mul hV g k, hinv k hk]
  obtain ⟨m, xs, ψ, hψ, hφeq⟩ := GlobalTheory.T.holomorphic_sections_span_restriction D T hT _ (inR j) T.σ₀ T.toCore.good_σ₀ C hU (wtA κ) κ.n
    (dom_wtA _) hP hspan hmu φ' hφ'm hinv'
  have hψ' : ∀ k, ∃ f, (f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA κ) κ.n ∧
      rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
        (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA κ) κ.n)) ∧ T.phiJ ((j : ℕ) + 1) T.σ₀ (wtA κ) f = ψ k := hψ
  choose fs hfs using hψ'
  refine ⟨m, xs, fun k => ⟨fs k, GlobalTheory.T.mem_cuspForms_of_reading_bounded_cuspidal_holomorphic D T hT _ (inR j) κ hlast hn (fs k) (hfs k).1.1 (hfs k).1.2⟩, funext fun g => ?_⟩
  rw [hφeq, RatExpand.castDict_sum_smul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (hfs k).2]
  rfl

end Cover

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mu_mul_level {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec}
    (hlev : R.toLevCh.Is A.μ0) (hT : TieIn T R κ v₀) (j : Fin D.R.m) :
    ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, T.mu ((j : ℕ) + 1) T.σ₀ (g * k) = T.mu ((j : ℕ) + 1) T.σ₀ g := by
  intro k hk g
  have hJ := hT.laws
  have hj := inR j
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨τ, hτ⟩ := GlobalTheory.MuLevel.exists_ext (L := D.what₂.LL) T.σ₀
  obtain ⟨hf, hk'⟩ := (hJ.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := hJ.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨y, hy, hu, hc⟩ := GlobalTheory.MuLevel.exists_root_of_level _ _ hodd k hf hk'
  have hm := R.C.isMu0 j
  have h1 : R.mu0 ((j : ℕ) + 1) y = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hlev.mu0 j) hm.tame _
      (fun P hP => hm.unr P fun a ha => hP ?_) y hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  have hg : GoodEmb T.Q.c (τ.comp (algebraMap T.Q.c.F D.what₂.LL)) := hτ ▸ hσ
  obtain ⟨z, hz1, hz2⟩ := (hT.chiR j τ hg).2.2.2.1 y hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL z = 1 :=
    D.what₂.embLL.injective (by rw [← hz1, h1, map_one, Circle.coe_one])
  have hχ : T.chiW ((j : ℕ) + 1) T.σ₀ y = 1 := by
    rw [hτ] at hz2
    apply Subtype.ext
    rw [hz2, h2, map_one, Circle.coe_one]
  have hMV := hJ.muVal _ hj _ hσ
  obtain ⟨x, hx⟩ := hMV.1 g
  have hxy : IsDetRoot _ (g * k) (x * y) := (GlobalTheory.Member.isDetRoot_laws D _).2.2.2 g k x y hx hy
  rw [hMV.2 _ _ hxy, hMV.2 g x hx, map_mul, hχ, mul_one]

theorem ioP_mem_harmonic {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {j : Fin D.R.m}
    {B : Base (Vc D j) (Wc D j)} (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hc : (R.cV j).Is) (hB : B.Good)
    (hψ : B.F.ψ = R.ψ) (hθ : B.F.θ = R.θ) (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ)
    (hBT : B.F.BT = onb (R.MW j (sg0 D A))) (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta)
    (hap : ∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ)
    (ham : ∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ)
    (x : LowT (R.MW j (sg0 D A))) (w₀ : (R.cV j).W) (hw : R.ioP j x w₀ = RealDat.Delta j) (w : (R.cV j).W) :
    R.ioP j x w ∈ harm (Wc D j).rank B.w B.F.BS := by
  have hT := Scale.io_act hlev hth hB hψ hθ hsT hBS hBT hmu heta x
  have hΔ : B.w.delta (Wc D j).rank = RealDat.Delta j := by
    unfold Weight.delta RealDat.Delta
    rw [show B.w.p = _ from funext fun τ => congrArg Prod.fst (hB.sig τ),
      show B.w.q = _ from funext fun τ => congrArg Prod.snd (hB.sig τ), show B.w.ap = _ from funext hap,
      show B.w.am = _ from funext ham]
  have hirr : ∀ U : Submodule ℂ (R.cV j).W, (∀ h : GinfC (Vc D j), U.map ((R.cV j).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hc.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hc.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
  rcases hirr ((harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x)) (fun h => by
    rintro _ ⟨w, hw', rfl⟩
    rw [Submodule.mem_comap, hT h h.2]
    exact fockGL_mem_harm _ _ _ hw') with h | h
  · have h0 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x) := by
      rw [Submodule.mem_comap, hw, ← hΔ]
      exact delta_mem_harm _ _
    rw [h, Submodule.mem_bot] at h0
    rw [h0, map_zero] at hw
    exact absurd hw.symm hΔ0
  · exact (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x))

end Real

theorem exists_vec_of_small (j : Fin D.R.m) {lam : D.what₂.Tau → DomWeight (Vc D j).rank} (h : lam = lamV D j)
    (F : VV ↥D.LL0 lam) : ∃ v : VsV D j D.what₂.LL,
      (∀ m, D.what₂.embLL (MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) ∈ (embLL0 D).fieldRange) ∧
      coefFn (embLL0 D) lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) =
        coefFn D.what₂.embLL (lamV D j) (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
  subst h
  refine ⟨⟨MvPolynomial.map D.LL0.val.toRingHom F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F.2⟩, fun m => ?_, funext fun x => ?_⟩
  · rw [MvPolynomial.coeff_map]
    exact ⟨_, rfl⟩
  · rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]
    rfl

theorem char_mem_of_over {k : Subfield ℂ} (hroots : ∀ (a : Fin 2) (z : ℂ), z ^ (D.host.g a * (D.host.g a - 1)) = 1 → z ∈ k)
    {PP : Pl D.host.E} {a : Fin 2} (hov : ((D.host.g a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (f : (kP PP)ˣ →* ℂˣ) (x : (kP PP)ˣ) :
    ((f x : ℂˣ) : ℂ) ∈ k := by
  classical
  obtain ⟨hn, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g a) (D.host.g_prime a) (D.nd.g_split a) PP hov
  have hcard : Nat.card (kP PP) = D.host.g a := by
    rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (D.host.g_prime a).ne_zero)
  have : Fintype (kP PP) := Fintype.ofFinite _
  have hu : Nat.card (kP PP)ˣ = D.host.g a - 1 := by
    rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have h1 : ((f x : ℂˣ) : ℂ) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  rw [hu] at h1
  refine hroots a _ ?_
  rw [mul_comm, pow_mul, h1, one_pow]

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A} (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good)
  (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem type_mem_range (hU : ρ.LevelOf D.nexp) (g : (ρ.B i j b).G.P.H) :
    (((ρ.B i j b).G.P.chi g : ℂˣ) : ℂ) ∈ (ρ.e i b).fieldRange := by
  have h1 : ρ.eG i j b ((ρ.eG i j b).symm g.1) ∈ (ρ.B i j b).G.P.H := by
    rw [MulEquiv.apply_symm_apply]; exact g.2
  have h2 := hU.psiU_eq i j b ⟨_, (hU.U_eq i j b _).1 h1⟩ h1
  have h3 : (⟨ρ.eG i j b ((ρ.eG i j b).symm g.1), h1⟩ : (ρ.B i j b).G.P.H) = g :=
    Subtype.ext (MulEquiv.apply_symm_apply _ _)
  rw [← h3]
  exact ⟨_, h2.symm⟩

include YS hρ in

theorem exists_cover (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (halg : AlgTie T) (hgal : IsGalois ℚ D.LL0)
    (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) (hU : ρ.LevelOf D.nexp)
    (Q : Finset (Pl D.host.E)) (hcls : Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q) (hS : Disjoint Q (D.ntw.S0 i)) (n : ℕ) :
    ∃ C : Cover T ((j : ℕ) + 1) T.σ₀, GoodCover T Rl.toRealDat j C n ∧ (embLL0 D).fieldRange ≤ C.σ₂.fieldRange ∧
      C.σ₂.fieldRange ≤ (ρ.e i b).fieldRange ∧ pDel D (D.ntw.l i) ∣ C.d.pd ∧
      (∀ P ∈ Q, ((C.d.pd : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
      (∀ g, (((ρ.B i j b).G.P.chi g : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange) ∧
      ∀ PP ∈ (ρ.B i j b).de.Q, ∀ x, (((ρ.B i j b).de.resC PP x : ℂˣ) : ℂ) ∈ C.σ₂.fieldRange := by
  have hB := hρ.base i j b
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  obtain ⟨N, hN0, hNl, haux, hNQ⟩ := exists_auxiliary_squarefree_level_twistPlaces hρ hde i Q hcls hS
  obtain ⟨L₀, i1, i2, h1, h2, h3, h4⟩ := GlobalTheory.RayInFrac.exists_field D ρ hρ i b hRF hray
    (D.host.g 0 * D.host.g 1 * pDel D (D.ntw.l i)) N (dvd_mul_right _ _) (by
      rcases pDel_cases (D := D) (D.ntw.l i) with e | e <;> rw [e]
      · exact dvd_mul_right _ _
      · rw [mul_right_comm _ D.host.pde]; exact dvd_mul_right _ _) hN0 hNl
  haveI : Normal ℚ L₀ := (i2 hgal).to_normal
  haveI : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hord : ∀ {H : Type} [Group H] [Finite H] (f : H →* ℂˣ) (x : H), IsOfFinOrder ((f x : ℂˣ) : ℂ) := fun f x =>
    MonoidHom.isOfFinOrder ((Units.coeHom ℂ).comp f) (isOfFinOrder_of_finite x)
  obtain ⟨L, i3, i4, h5, h6, h7⟩ := exists_field_adjoin_roots (ρ.e i b).fieldRange
    (Z := Set.range (fun g => (((ρ.B i j b).G.P.chi g : ℂˣ) : ℂ)) ∪
      ⋃ PP ∈ (ρ.B i j b).de.Q, Set.range fun x => (((ρ.B i j b).de.resC PP x : ℂˣ) : ℂ))
    ((Set.finite_range _).union ((ρ.B i j b).de.Q.finite_toSet.biUnion fun _ _ => Set.finite_range _)) (by
      rintro z (⟨g, rfl⟩ | hz)
      · exact ⟨type_mem_range i j b hU g, hord _ _⟩
      · obtain ⟨PP, hPP, x, rfl⟩ := Set.mem_iUnion₂.1 hz
        refine ⟨?_, hord _ _⟩
        obtain ⟨y, hy⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hB.de.split.isIdemAt hPP) x
        obtain ⟨hx, hr⟩ := hy.res
        obtain ⟨a, ha⟩ := GlobalTheory.DeltaRange.delta_value_mem_range hρ i j b y
        rw [hB.de.res PP hPP y hy.off hx x hr] at ha
        exact ⟨a, ha⟩) L₀ h2
  have h8 : (embLL0 D).fieldRange ≤ L.toSubfield := fun z hz => h5 (h1 hz)
  rw [← hMg] at haux
  obtain ⟨I, hK, hprod, hsup⟩ := GlobalTheory.HalfCharacter.exists_half_of_auxiliary_split_level D T hT _ haux
  have hMN : T.Q.l.M * (pDel D (D.ntw.l i) * N) = D.host.g 0 * D.host.g 1 * pDel D (D.ntw.l i) * N := by
    rw [hMg, mul_assoc (D.host.g 0 * D.host.g 1)]
  have hne : T.Q.l.M * (pDel D (D.ntw.l i) * N) ≠ 0 :=
    mul_ne_zero (by have := T.Q.l.three_le; omega) fun h0 => Nat.not_odd_zero (h0 ▸ haux.1)
  obtain ⟨C, hpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hT j (inR j) n _ I haux hK hprod hsup L
    (fun z hz => h8 (GlobalTheory.CoverSmall.core_le_small T Rl cG S YS hT halg j hz))
    (h5 (h4 _ (by rw [← hMN]; exact (Complex.isPrimitiveRoot_exp _ hne).pow_eq_one)))
    ⟨fun v hv => by
        obtain ⟨y, hy⟩ := hval.mu0 j v hv
        exact ⟨⟨embLL0 D y, h8 ⟨y, rfl⟩⟩, hy⟩,
      fun v hv => by
        obtain ⟨y, hy⟩ := hval.eta v hv
        exact ⟨⟨embLL0 D y, h8 ⟨y, rfl⟩⟩, hy⟩⟩
    (by
      obtain ⟨H, j1, j2, j3, j4, hH, jj, hjj, hv⟩ := h3
      rw [hMN]
      exact ⟨H, j1, j2, j3, j4, hH, jj, hjj, fun x => h5 (hv x)⟩)
  refine ⟨C, hG, hfr ▸ h8, hfr ▸ h6, hpd ▸ dvd_mul_right _ _, fun P hP => ?_, fun g => ?_, fun PP hPP x => ?_⟩
  · rw [hpd]
    exact GlobalTheory.HalfCompare.mem_of_dvd (hNQ P hP) (dvd_mul_left _ _)
  · rw [hfr]
    exact h7 _ (Or.inl ⟨g, rfl⟩)
  · rw [hfr]
    exact h7 _ (Or.inr (Set.mem_iUnion₂.2 ⟨PP, hPP, x, rfl⟩))

theorem ratUniv_of_reading (hRF : GlobalTheory.NT.RayField) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (hpin : RealPin Rl cG ρ)
    (hU : ρ.LevelOf D.nexp) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (hti : TieIn T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb) (hgal : IsGalois ℚ D.LL0)
    (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK) {c : ℂ} (hc : c ≠ 0)
    (hread : ∀ f : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n, ∃ x : NX.FmK S ((j : ℕ) + 1),
      castDict hV (T.phiJ ((j : ℕ) + 1) T.σ₀ (wtA (κ j)) (f : T.R ((j : ℕ) + 1))) = c • evW YS v₀ j (Subtype.val x))
    {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν) : RatUniv (realRd YS v₀ hρ i j b (c⁻¹ * ν)) := by
  classical
  intro Q M hQ s h P hd _ a
  have hν0 := hν.ne_zero
  obtain ⟨gramR, c0R, c0L, hft, u, hu, c₀, ph, hc₀, -, rfl, hsc, hph⟩ := hν
  have hT := hti.laws
  have hB := hρ.base i j b
  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ _ (ρ.B i j b).F.BS hB.wt hm
  have hlam : (ρ.B i j b).w.lam = lamV D j :=
    GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight D T0 Rl.toLevCh A3.A.μ0 j _ hcore.lev hB (hpin.mu0 i j b) (hpin.ap i j b) (hpin.am i j b)
  refine mem_range_of_small _ (xiLin ρ D.nexp i j b Q M h a) hinj (fun F => ?_) (fun P' hP' F hF => ?_) hd.mem
  · obtain ⟨v, -, hv⟩ := exists_vec_of_small j hlam F
    obtain ⟨u', w₀, hu', -, hw⟩ := IsChosenExtremalVector.io _ (hti.hv₀ j _) hio
    obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
    refine ⟨c₀⁻¹ • Rl.ioP j (PiTensorProduct.tprod ℂ u') (c0L j v), Submodule.smul_mem _ _
      (ioP_mem_harmonic hcore.lev hcore.thP (hcore.models.cV j) hB (hpin.psi i j b) (hpin.inf i j b) (hpin.cartT i j b)
        (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b) _ w₀ hw _), ?_⟩
    exact (map_smul _ _ _).trans ((congrArg (c₀⁻¹ • ·) (hsc v)).trans ((inv_smul_smul₀ hc₀ _).trans hv.symm))

  obtain ⟨v, hvc, hv⟩ := exists_vec_of_small j hlam F
  have hio' : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j v) = c₀ • P' := by
    obtain ⟨u', w₀, hu', -, hw⟩ := IsChosenExtremalVector.io _ (hti.hv₀ j _) hio
    obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
    exact hsc.ioP_eq hinj hP' (ioP_mem_harmonic hcore.lev hcore.thP (hcore.models.cV j) hB (hpin.psi i j b) (hpin.inf i j b)
      (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b)
      _ w₀ hw _) (hF.trans hv)
  have hsub : half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) ⊆ Q := fun P hP => admissibleConjugatePairPlaces_subset i Q M (mem_half.1 hP).1
  have hgood := GlobalTheory.UnivGood.univOf_good D D.nd D.ntw ρ hρ D.nexp i Q M
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) := GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D D.nd D.ntw ρ hρ i j b _
    (fun P hP => hQ.1 P (admissibleConjugatePairPlaces_subset i Q M hP)) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))

  obtain ⟨C, hG, hL0, hLe, hpd, hQpd, hchi, hres⟩ := exists_cover YS hρ i j b hRF hT hti.alg hgal hval hray hde hU
    (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (fun P hP => hQ.2.1 P (hsub hP)) (hQ.2.2.mono_left hsub) (κ j).n
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  have hPg : ∀ PP ∈ (ρ.B i j b).G.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hρ.Pg i j b
  have hN : ∀ PP, PP ∈ (ρ.B i j b).G.Pg ∨ PP ∈ (ρ.B i j b).de.Q ∪ half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M) →
      ((T.Q.l.M * C.d.pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rintro PP (hP | hP)
    · obtain ⟨k, hk⟩ := hPg PP hP
      refine GlobalTheory.HalfCompare.mem_of_dvd hk (Dvd.dvd.mul_right ?_ _)
      rw [hMg]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    · rcases Finset.mem_union.1 hP with hP | hP
      · rw [hρ.delta] at hP
        exact GlobalTheory.HalfCompare.mem_of_dvd ((mem_pD_iff i PP).1 (mem_half.1 hP).1) (hpd.mul_left _)
      · exact GlobalTheory.HalfCompare.mem_of_dvd (hQpd PP hP) (dvd_mul_left _ _)
  have hcop : Nat.Coprime (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK) (T.Q.l.M * C.d.pd) := by
    refine Nat.Coprime.mul_right ?_ hG.2.2.1.2.2.2.2.symm
    rw [hMg]
    exact Nat.Coprime.mul_right (GlobalTheory.CoverHalf.g_coprime D 0).symm (GlobalTheory.CoverHalf.g_coprime D 1).symm
  have hδ := isDelta_delAt Rl.C (D.ntw.l i)
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi :=
    ⟨hpin.delta i j b, hδ.fin, hδ.triv, hδ.tame, fun w hw => hδ.unr w fun h0 => hw (GlobalTheory.HalfCompare.mem_of_dvd h0 hpd),
      fun w hw => by
        obtain ⟨y, hy⟩ := valuesIn_delAt hval _ w hw
        obtain ⟨z, hz⟩ := hL0 ⟨y, rfl⟩
        exact ⟨z, hz.trans hy⟩⟩
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta] at h1
    exact h1

  have hser : ∀ a', IsRat T j hV C (κ j) ((ph * c₀) • series (ρ.B i j b).F (ρ.om i j b 1)
      ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))
        (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) a') h P') := fun a' => by
    have hdat := isLevDatum_vecAt hB hadm (fun PP hP => GlobalTheory.HalfCompare.not_mem_of_coprime PP hcop (hN PP hP)) _ hN
      C.σ₂.fieldRange hchi (fun PP hP x => by
        obtain ⟨k, hk⟩ := hPg PP hP
        exact hL0 (char_mem_of_over hroots hk _ x)) hres
      (fun PP y => ((Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j) PP.1 (a' PP) y : ℚ) : ℂ))
      fun PP y => SubfieldClass.ratCast_mem _ _
    rw [hpin.psi, hpin.latS, hpin.latT, hpin.vac] at hdat
    have h1 := ((hph C hG hL0 h hd.fin _ hdat (c0L j v)
      (Submodule.subset_span ⟨v, fun m => hL0 (hvc m), rfl⟩)).2 _ _ htw).2 _ hω'
    rw [hpin.phase_mul_thetaKO i b hio'] at h1
    exact h1

  have hsum : IsRat T j hV C (κ j) ((ph * c₀) • ρ.xi i j b D.nexp Q M h P' a) := by
    have h1 := isRat_sum fun a' => isRat_fibre hRF hT hG.1 hG.2.2.2.2 hgood
      (fun PP hP => hN PP (Or.inr (Finset.mem_union_right _ hP))) a' (hser (a - a'))
    convert h1 using 1
    funext g
    rw [Finset.sum_apply, Finset.sum_eq_single (Multiplicative.toAdd (detChar (Wc D j)
      ((univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))) g))
      (fun a' _ ha' => by rw [if_neg (Ne.symm ha'), zero_mul]) (fun h0 => absurd (Finset.mem_univ _) h0), if_pos rfl, one_mul,
      Pi.smul_apply, Pi.smul_apply]
    exact congrArg _ (Base.xiCoef_apply _ _ _ _ _ _ _ _ _)

  have hlast : (κ j).LastPos := fun τ k hk => by
    rw [(hti.kap j τ).1 k]
    exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (κ j).n := by
    rw [(hti.kap j (D.eTau.symm 1)).2.2]
    exact hnV
  obtain ⟨m, xs, f, he⟩ := exists_sum_of_isRat hT hlast hn hG.1 (hG.2.1 _ (dom_wtA _)) (mu_mul_level hcore.lev hti j) hsum
    fun k hk g => by
      have hlift := (GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV
        (cast (congrArg (GA D) hV) k)).2 (by rw [cast_cast, cast_eq]; exact hk)
      rw [Pi.smul_apply, Pi.smul_apply]
      refine congrArg _ (DualType.xiCoef_mul_right_of_red hB (D.sp.V_sig _) hgood hadm (Base.isAdmFam_univFam _ _ _) hω
        hlift.1 ?_ (fun PP hPP => ?_) h P' a g)
      · rw [hpin.frT]
        exact parLev_St hlift.2.1
      · rw [hpin.frT]
        exact (GlobalTheory.PrincipalLevel.upperLeftBlock_eq_one_iff_of_mem_blockTri _ (rank_Wc j).symm _).1 (congrFun hlift.2.2 ⟨PP, (hpin.Pg i j b ▸ hPP : PP ∈ Rl.Pg)⟩)
  choose x hx using hread
  refine mem_range_realRd_of_sum hρ (mul_ne_zero (inv_ne_zero hc) hν0) (fun k => C.σ₂ (xs k)) (fun k => hLe ⟨_, rfl⟩)
    (fun k => x (f k)) ?_
  change (c⁻¹ * (ph * c₀)) • ρ.xi i j b D.nexp Q M h P' a = _
  rw [mul_smul, he, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hx, smul_comm c⁻¹, inv_smul_smul₀ hc]

theorem ratUniv_realRd (hRF : GlobalTheory.NT.RayField) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (hpin : RealPin Rl cG ρ)
    (hU : ρ.LevelOf D.nexp) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F)
    (fw : FWTie T Rl.toRealDat κ v₀) (hio : IoExt Rl.toRealDat)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (hpins : OMPins T Rl.toRealDat κ v₀ O j)
    (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hde : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν) : RatUniv (realRd YS v₀ hρ i j b ν) := by
  have hti : TieIn T Rl.toRealDat κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hpb : T.pb = Rl.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat fw.laws.toLawsM hcore.lev (hpins.2.tuple ()).half
  have hev : fw.Evaluates := fw.evaluates
    (GlobalTheory.CuspValues.jEvExists_and_jEvBar D Γ Pl0 T0 A3.A T Rl.toRealDat κ v₀ hcore.lev hcore.models hti hpb).1
  have hσ : res T (sg0 D A3.A) = T.σ₀ := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ Rl.hv0]
    exact res_embLL T hti.alg fw.laws.pins.2.2.1
  have hV' : T.V ((j : ℕ) + 1) (res T (sg0 D A3.A)) = Wc D j := by rw [hσ]; exact hV
  have key := ratUniv_of_reading YS κ v₀ hρ i j b hRF hV hpin hU hnV hcore hti hio hpb hgal hval hray hroots hde one_ne_zero
    (fun f => by
      obtain ⟨x, hx⟩ := exists_evW_eq_phiC YS fw hev j (by rw [hσ]; exact T.toCore.good_σ₀) hV' f
      refine ⟨x, ?_⟩
      rw [one_smul, hx]
      exact funext fun g => (RatExpand.castDict_phiJ hσ hV' hV _ _ g).symm) hν
  rwa [inv_one, one_mul] at key

end Main

theorem ratUniv_of_ratHyp : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → ρ.LevelOf D.nexp → (D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) → GlobalTheory.BigOn.Exp.RatHyp T Rl F κ v₀ O i j hV → ∀ ν, IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν → RatUniv (realRd YS v₀ hρ i j b ν) := by
  intro _ hRF _ D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hU hde h ν hν
  obtain ⟨fw⟩ := h.fw
  exact ratUniv_realRd YS κ v₀ hρ i j b hRF hV hpin hU h.size h.core fw h.io O h.pins h.galois h.small.val h.small.ray
    h.small.roots hde hν

end GlobalTheory.SeriesTie.UnivRat
