import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialFactorTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {J : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}

def MarkedSequenceOfBlowups.controlledNonMonomialTransform (t : MarkedSequenceOfBlowups p J μ E) (N : X.IdealSheafData) (c : ℕ) :
    ∀ i : ℕ, (t.schemeAt i).IdealSheafData
  | 0 => N.comap t.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c i).comap (t.transitionMapSucc i)) (t.exceptionalDivisor i) c

@[simp]
theorem MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero (t : MarkedSequenceOfBlowups p J μ E) (N : X.IdealSheafData)
    (c : ℕ) : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c 0 = N.comap t.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledNonMonomialTransform_succ (t : MarkedSequenceOfBlowups p J μ E) (N : X.IdealSheafData)
    (c i : ℕ) :
    MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c i).comap (t.transitionMapSucc i)) (t.exceptionalDivisor i) c :=
  rfl

def MarkedSequenceOfBlowups.controlledMonomialTransform (t : MarkedSequenceOfBlowups p J μ E) (M : X.IdealSheafData) (a c : ℕ) :
    ∀ i : ℕ, (t.schemeAt i).IdealSheafData
  | 0 => M.comap t.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledMonomialTransform t M a c i).comap (t.transitionMapSucc i) * t.exceptionalDivisor i ^ c)
        (t.exceptionalDivisor i) a

@[simp]
theorem MarkedSequenceOfBlowups.controlledMonomialTransform_zero (t : MarkedSequenceOfBlowups p J μ E) (M : X.IdealSheafData)
    (a c : ℕ) : MarkedSequenceOfBlowups.controlledMonomialTransform t M a c 0 = M.comap t.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledMonomialTransform_succ (t : MarkedSequenceOfBlowups p J μ E) (M : X.IdealSheafData)
    (a c i : ℕ) :
    MarkedSequenceOfBlowups.controlledMonomialTransform t M a c (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledMonomialTransform t M a c i).comap (t.transitionMapSucc i) * t.exceptionalDivisor i ^ c)
        (t.exceptionalDivisor i) a :=
  rfl

end

section

theorem isAdmissible_withIdealAndMult_pow_sup_pow {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {N : T.scheme.IdealSheafData} {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞)) :
    (T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).IsAdmissible ∧
      ∀ x : ↥T.scheme, orderAt (N ^ T.mult ⊔ T.ideal ^ s) x ≤ ((T.mult * s : ℕ) : ℕ∞) := by
  have hcz : CharZero T.base := hT.charZero
  have hsm : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  have hle : ∀ x : ↥T.scheme,
      orderAt (N ^ T.mult ⊔ T.ideal ^ s) x ≤ ((T.mult * s : ℕ) : ℕ∞) := fun x =>
    orderAt_pow_sup_pow_le T.base T.structMap N T.ideal T.mult s hord x
  have hsub : (↑(N ^ T.mult ⊔ T.ideal ^ s).support : Set ↥T.scheme) ⊆
      (↑T.ideal.support : Set ↥T.scheme) := by
    intro x hx
    by_contra hc
    have h0 : orderAt T.ideal x = 0 := (orderAt_eq_zero_iff_not_mem_support T.ideal x).2 hc
    have h1 : (1 : ℕ∞) ≤ orderAt (N ^ T.mult ⊔ T.ideal ^ s) x :=
      (one_le_orderAt_iff_mem_support (N ^ T.mult ⊔ T.ideal ^ s) x).2 hx
    rw [orderAt_pow_sup_pow T.base T.structMap N T.ideal T.mult s x] at h1
    have h2 : (1 : ℕ∞) ≤ (s : ℕ∞) * orderAt T.ideal x := le_trans h1 (min_le_right _ _)
    rw [h0, mul_zero] at h2
    simp at h2
  have hnz : NonzeroOnComponents (N ^ T.mult ⊔ T.ideal ^ s) := by
    rw [nonzeroOnComponents_iff]
    intro Z hZ hZsub
    exact (nonzeroOnComponents_iff T.ideal).1 hT.nonzeroOnComponents Z hZ (hZsub.trans hsub)
  have hmult : 1 ≤ T.mult * s := by
    have h := Nat.mul_le_mul hT.one_le_mult hs
    simpa using h
  exact ⟨{ charZero := hT.charZero
           locallyOfFiniteType := hT.locallyOfFiniteType
           nonzeroOnComponents := hnz
           one_le_mult := hmult
           quasiCompact := hT.quasiCompact
           smooth := hT.smooth
           snc := hT.snc }, hle⟩

theorem isMonomialSplitting_controlledTransform_of_le_length (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞))
    (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s) T.boundary)
    (i : ℕ) (hi : i ≤ t.length) :
    t.ideal i =
        MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i ^ T.mult ⊔
          MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i ^ s ∧
      IsMonomialSplitting (t.boundary i) (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i)
        (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i) (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) ∧
      ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult,
        orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x ≤ (s : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hgeom : OrderAtComapOffExceptionalLocus.{u} :=
    orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs
  have hm : 1 ≤ T.mult := hT.one_le_mult
  have hT' := (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  have key : ∀ j : ℕ, j ≤ t.length →
      (t.ideal j = MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j ^ T.mult ⊔
          MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j ^ s ∧
        IsMonomialSplitting (t.boundary j) (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j)
          (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s j) (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j) ∧
        ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j) T.mult,
          orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j) x ≤ (s : ℕ∞)) := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨?_, ?_, ?_⟩
        · rw [t.ideal_zero, MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero, MarkedSequenceOfBlowups.controlledTransform_zero,
            Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow,
            Scheme.IdealSheafData.comap_pow]
        · rw [t.boundary_zero, MarkedSequenceOfBlowups.controlledTransform_zero, MarkedSequenceOfBlowups.controlledMonomialTransform_zero,
            MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero]
          exact hsplit.comap_iso t.isoZero
        · intro x hx
          have h1 : (T.mult : ℕ∞) ≤ orderAt (T.ideal.comap t.isoZero.hom) x :=
            (mem_orderAtLeastLocus_iff _ _ _).1 hx
          rw [orderAt_comap_of_isIso] at h1
          have h2 := hord _ ((mem_orderAtLeastLocus_iff _ _ _).2 h1)
          show orderAt (N.comap t.isoZero.hom) x ≤ (s : ℕ∞)
          rw [orderAt_comap_of_isIso]
          exact h2
    | succ n ih =>
        intro hn
        have hn' : n < t.length := hn
        obtain ⟨ih1, ih2, ih3⟩ := ih (le_of_lt hn')
        have hbl : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc n) (t.center n) := t.isBlowupAlongIdealSheaf_blowupMorphism n hn'
        have hexc : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) = t.exceptionalDivisor n := by
          rw [MarkedSequenceOfBlowups.exceptionalDivisor_eq, Blowup.exceptionalIdeal_eq_comap]
        have hFcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (t.exceptionalDivisor n) := by
          rw [← hexc]
          exact isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
        have hTn := MarkedIdealWithBoundary.IsAdmissible.transformAt hECNC hT' t n (le_of_lt hn')
        have : AlgebraicGeometry.Smooth (MarkedSequenceOfBlowups.projectionToSpec t n) :=
          MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hT' t n (le_of_lt hn')
        have : AlgebraicGeometry.Smooth (MarkedSequenceOfBlowups.projectionToSpec t (n + 1)) :=
          MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hT' t (n + 1) hn
        have : AlgebraicGeometry.IsNoetherian (t.schemeAt (n + 1)) :=
          MarkedSequenceOfBlowups.isNoetherian_schemeAt hECNC hT' t (n + 1) hn
        have hsmn : AlgebraicGeometry.Smooth
            ((t.center n).subschemeι ≫ MarkedSequenceOfBlowups.projectionToSpec t n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact t.center_smooth n hn'
        have hsncn : HasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec t n) (t.center n) (t.boundary n) := by
          rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
          exact t.center_snc n hn'
        have hcos : orderAtLeastLocus (t.ideal n) (T.mult * s)
            = orderAtLeastLocus (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) s ∩
              orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := by
          rw [ih1]
          exact orderAtLeastLocus_pow_sup_pow T.base (MarkedSequenceOfBlowups.projectionToSpec t n) _ _ hm hs
        have hZord : ∀ x ∈ (t.center n).support,
            orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) x = (s : ℕ∞) := by
          intro x hx
          have hx1 := t.center_order n hn' hx
          rw [hcos] at hx1
          exact le_antisymm (ih3 x hx1.2) ((mem_orderAtLeastLocus_iff _ _ _).1 hx1.1)
        have hZP : (↑(t.center n).support : Set ↥(t.schemeAt n))
            ⊆ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := by
          intro x hx
          have hx1 := t.center_order n hn' hx
          rw [hcos] at hx1
          exact hx1.2
        have hPle : MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n ≤ t.center n ^ T.mult :=
          le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec t n) (t.center n) _ (t.boundary n)
            hsncn T.mult hZP
        have hAle : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n ≤ t.center n ^ s := by
          refine le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec t n) (t.center n) _
            (t.boundary n) hsncn s ?_
          intro x hx
          exact (mem_orderAtLeastLocus_iff _ _ _).2 (le_of_eq (hZord x hx).symm)
        have hPdiv : ∃ B : (t.schemeAt (n + 1)).IdealSheafData, t.exceptionalDivisor n ^ T.mult * B
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          refine (hFcart.pow T.mult).exists_mul_eq ?_
          rw [← hexc]
          exact comap_le_exceptionalIdeal_pow (t.transitionMapSucc n) hPle
        have hAdiv : ∃ B : (t.schemeAt (n + 1)).IdealSheafData, t.exceptionalDivisor n ^ s * B
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          refine (hFcart.pow s).exists_mul_eq ?_
          rw [← hexc]
          exact comap_le_exceptionalIdeal_pow (t.transitionMapSucc n) hAle
        have hPtw : t.exceptionalDivisor n ^ T.mult *
            MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          rw [MarkedSequenceOfBlowups.controlledTransform_succ]
          exact pow_mul_residualByPow _ _ _ hPdiv
        have hAtw : t.exceptionalDivisor n ^ s * MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          rw [MarkedSequenceOfBlowups.controlledNonMonomialTransform_succ]
          exact pow_mul_residualByPow _ _ _ hAdiv
        have hPtw' : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ T.mult *
            MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          rw [hexc]
          exact hPtw
        have hAtw' : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ s *
            MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          rw [hexc]
          exact hAtw
        have hCdiv : ∃ Cc : (t.schemeAt (n + 1)).IdealSheafData,
            Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ T.mult * Cc
              = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
                Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ s :=
          exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow hG _ hTn (t.center n) hsmn hsncn _
            (t.transitionMapSucc n) hbl _ _ _ T.mult s ih2 hZP hZord _ hPtw' _ hAtw'
        have hCtw : t.exceptionalDivisor n ^ T.mult * MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s (n + 1)
            = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
              t.exceptionalDivisor n ^ s := by
          rw [MarkedSequenceOfBlowups.controlledMonomialTransform_succ]
          refine pow_mul_residualByPow _ _ _ ?_
          obtain ⟨Cc, hCc⟩ := hCdiv
          refine ⟨Cc, ?_⟩
          rw [← hexc]
          exact hCc
        have hCtw' : Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ T.mult *
            MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s (n + 1)
            = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
              Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n) ^ s := by
          rw [hexc]
          exact hCtw
        refine ⟨?_, ?_, ?_⟩
        · have hidsucc : t.exceptionalDivisor n ^ (T.mult * s) * t.ideal (n + 1)
              = (t.ideal n).comap (t.transitionMapSucc n) := by
            rw [← hexc]
            exact t.ideal_succ n hn'
          have hcancel : t.exceptionalDivisor n ^ (T.mult * s) * t.ideal (n + 1)
              = t.exceptionalDivisor n ^ (T.mult * s) *
                (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1) ^ T.mult ⊔
                  MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1) ^ s) := by
            rw [hidsucc, ih1, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow,
              Scheme.IdealSheafData.comap_pow, ← hAtw, ← hPtw, mul_pow, mul_pow, ← pow_mul,
              ← pow_mul, Scheme.IdealSheafData.mul_inf, Nat.mul_comm s T.mult]
          exact (hFcart.pow (T.mult * s)).eq_of_mul_eq_mul hcancel
        · rw [t.boundary_succ n hn']
          exact isMonomialSplitting_of_isBlowupAlongIdealSheaf hG _ hTn (t.center n) hsmn hsncn _
            (t.transitionMapSucc n) hbl _ _ _ T.mult s ih2 hZP hZord _ hPtw' _ hAtw' _ hCtw'
        · intro x hx
          by_cases hxE : x ∈ (Blowup.exceptionalIdeal (t.transitionMapSucc n) (t.center n)).support
          · exact hG.controlledTransform_orderAt_le _ hTn (t.center n) hsmn hsncn _
              (t.transitionMapSucc n) hbl _ s hZord _ hAtw' x hxE
          · have hcs : orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)) T.mult
                ⊆ ⇑(t.transitionMapSucc n) ⁻¹'
                  orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult :=
              orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf hgeom _ hTn (t.center n) _ (t.transitionMapSucc n)
                hbl _ T.mult hZP _ hPtw' T.mult le_rfl
            have hxP : (t.transitionMapSucc n) x ∈
                orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := hcs hx
            have hord2 := ih3 _ hxP
            have hoff := hG.monomialInputs.orderAt_comap_off_exceptional _ hTn _
              (t.transitionMapSucc n) (t.center n) hbl x hxE (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n)
            have hoff' : orderAt ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n)) x
                = orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) ((t.transitionMapSucc n) x) := hoff
            have hx0 : orderAt (t.exceptionalDivisor n) x = 0 := by
              rw [← hexc]
              exact (orderAt_eq_zero_iff_not_mem_support _ _).2 hxE
            have hsplit2 :
                orderAt ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n)) x
                  = orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)) x := by
              rw [← hAtw, orderAt_mul T.base (MarkedSequenceOfBlowups.projectionToSpec t (n + 1)),
                orderAt_pow T.base (MarkedSequenceOfBlowups.projectionToSpec t (n + 1)), hx0, mul_zero, zero_add]
            rw [← hsplit2, hoff']
            exact hord2
  exact key i hi

theorem exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞))
    (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s) T.boundary)
    (i : ℕ) (hi : i < t.length) :
    (∀ x ∈ (t.center i).support,
        orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x = (s : ℕ∞)) ∧
      (↑(t.center i).support : Set ↥(t.schemeAt i)) ⊆
        orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult ∧
      (∃ A : (t.schemeAt (i + 1)).IdealSheafData,
        t.exceptionalDivisor i ^ T.mult * A =
          (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i).comap (t.transitionMapSucc i)) ∧
      (∃ B : (t.schemeAt (i + 1)).IdealSheafData,
        t.exceptionalDivisor i ^ s * B =
          (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i).comap (t.transitionMapSucc i)) ∧
      (∃ C : (t.schemeAt (i + 1)).IdealSheafData,
        t.exceptionalDivisor i ^ T.mult * C =
          (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i).comap (t.transitionMapSucc i) *
            t.exceptionalDivisor i ^ s) := by
  classical
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hadm : (T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).IsAdmissible :=
    (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  have hlevel : ((T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).transformAt t i).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt hECNC hadm t i (le_of_lt hi)
  have hchar : CharZero T.base := hT.charZero
  have hsmooth : AlgebraicGeometry.Smooth (t.projectionToSpec i) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hadm t i (le_of_lt hi)
  have hnoeth : AlgebraicGeometry.IsNoetherian (t.schemeAt (i + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt hECNC hadm t (i + 1) hi
  obtain ⟨hideal_i, hsplit_i, hord_i⟩ :=
    isMonomialSplitting_controlledTransform_of_le_length hG hT hsplit hs hord t i (le_of_lt hi)
  have hexc : t.exceptionalDivisor i = Blowup.exceptionalIdeal (t.transitionMapSucc i) (t.center i) := by
    rw [MarkedSequenceOfBlowups.exceptionalDivisor_eq, Blowup.exceptionalIdeal_eq_comap]
  have hbl : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i) := t.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have hsncc : HasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i) (t.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact t.center_snc i hi
  have hsm : AlgebraicGeometry.Smooth ((t.center i).subschemeι ≫ t.projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact t.center_smooth i hi
  have key : ∀ x ∈ (t.center i).support,
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x = (s : ℕ∞) ∧
        (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x := by
    intro x hx
    have hx0 : ((T.mult * s : ℕ) : ℕ∞) ≤ orderAt (t.ideal i) x :=
      (mem_orderAtLeastLocus_iff _ _ _).1 (t.center_order i hi hx)
    rw [hideal_i, orderAt_pow_sup_pow T.base (t.projectionToSpec i) _ _ _ _ x, le_min_iff,
      Nat.cast_mul] at hx0
    obtain ⟨h1, h2⟩ := hx0
    have h1' : (s : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x :=
      (natCast_mul_le_mul_iff hT.one_le_mult s _).1 h1
    have h2' : (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x := by
      refine (natCast_mul_le_mul_iff hs T.mult _).1 ?_
      rwa [mul_comm ((s : ℕ∞)) ((T.mult : ℕ∞))]
    exact ⟨le_antisymm (hord_i x ((mem_orderAtLeastLocus_iff _ _ _).2 h2')) h1', h2'⟩
  have hZP : (↑(t.center i).support : Set ↥(t.schemeAt i)) ⊆
      orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (key x hx).2
  have hZord : (↑(t.center i).support : Set ↥(t.schemeAt i)) ⊆
      orderAtLeastLocus (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) s := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (le_of_eq (key x hx).1.symm)
  have hPle : MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i ≤ t.center i ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i)
      (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) (t.boundary i) hsncc T.mult hZP
  have hAle : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i ≤ t.center i ^ s :=
    le_pow_of_hasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i)
      (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) (t.boundary i) hsncc s hZord
  obtain ⟨B', hB', -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i)
    (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult hbl hPle
  obtain ⟨A', hA', -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i)
    (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) s hbl hAle
  obtain ⟨C', hC'⟩ := exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow hG _ hlevel
    (t.center i) hsm hsncc (t.schemeAt (i + 1)) (t.transitionMapSucc i) hbl
    (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i)
    (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i)
    (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) T.mult s hsplit_i hZP
    (fun x hx => (key x hx).1) B' hB' A' hA'
  refine ⟨fun x hx => (key x hx).1, hZP, ⟨B', ?_⟩, ⟨A', ?_⟩, ⟨C', ?_⟩⟩
  · rw [hexc]
    exact hB'
  · rw [hexc]
    exact hA'
  · rw [hexc]
    exact hC'

private theorem controlledTransform_eq_ofMarkedSequence_controlledTransform {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {J : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p J μ E) (I : X.IdealSheafData) (m i : ℕ) :
    MarkedSequenceOfBlowups.controlledTransform s I m i
      = ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i := by
  induction i with
  | zero =>
      exact (BlowupSequenceData.controlledTransform_zero ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m).symm
  | succ n ih =>
      have h2 := BlowupSequenceData.controlledTransform_succ ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData) I m n
      refine Eq.trans ?_ h2.symm
      exact congrArg
        (fun Jj : (s.schemeAt n).IdealSheafData =>
          residualByPow (Jj.comap (s.transitionMapSucc n)) (s.exceptionalDivisor n) m) ih

private theorem comap_controlledTransform_eq_comap_ofMarkedSequence {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {J : X.IdealSheafData} {μ : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p J μ E) (I : X.IdealSheafData) (m i : ℕ) :
    (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)
      = (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).controlledTransform I m i).comap
          (((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData).map i) :=
  congrArg (fun Jj : (s.schemeAt i).IdealSheafData => Jj.comap (s.transitionMapSucc i))
    (controlledTransform_eq_ofMarkedSequence_controlledTransform s I m i)

theorem isMarked_ofMarkedSequence_of_isMonomialSplitting (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) {M N : T.scheme.IdealSheafData}
    (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞))
    (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s) T.boundary) :
    (MarkedBlowupSequenceData.ofMarkedSequence t).toBlowupSequenceData.IsMarked T.structMap T.ideal T.mult
      T.boundary := by
  have hself := (MarkedBlowupSequenceData.ofMarkedSequence t).isMarked_toBlowupSequenceData
  refine ⟨?_, ?_, hself.center_smooth, hself.center_snc⟩
  · intro i hi
    have hi' : i < t.length := hi
    obtain ⟨A, hA⟩ := (exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length hG hT hsplit hs hord t i hi').2.2.1
    exact ⟨A, hA.trans (comap_controlledTransform_eq_comap_ofMarkedSequence t T.ideal T.mult i)⟩
  · intro i hi
    have hi' : i < t.length := hi
    have hsub := (exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length hG hT hsplit hs hord t i hi').2.1
    intro x hx
    have h1 : (T.mult : ℕ∞) ≤ orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x :=
      (mem_orderAtLeastLocus_iff _ _ _).1 (hsub hx)
    have he : orderAt (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) x
        = orderAt (((MarkedBlowupSequenceData.ofMarkedSequence t).toBlowupSequenceData).controlledTransform T.ideal T.mult i) x :=
      congrArg (fun Jj : (t.schemeAt i).IdealSheafData => orderAt Jj x)
        (controlledTransform_eq_ofMarkedSequence_controlledTransform t T.ideal T.mult i)
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (he ▸ h1)

theorem orderAt_controlledNonMonomialTransform_length_lt (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ℕ∞))
    (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s) T.boundary)
    (hempty : orderAtLeastLocus (t.ideal t.length) (T.mult * s) = ∅) :
    ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult t.length) T.mult,
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s t.length) x < (s : ℕ∞) := by
  classical
  have hECNC : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
  have hadm : (T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s)).IsAdmissible :=
    (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  have hchar : CharZero T.base := hT.charZero
  have hsmooth : AlgebraicGeometry.Smooth (t.projectionToSpec t.length) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec hECNC hadm t t.length le_rfl
  obtain ⟨hideal, -, -⟩ := isMonomialSplitting_controlledTransform_of_le_length hG hT hsplit hs hord t t.length le_rfl
  rw [hideal] at hempty
  exact (orderAtLeastLocus_pow_sup_pow_eq_empty_iff T.base (t.projectionToSpec t.length)
      (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s t.length)
      (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult t.length) hT.one_le_mult hs).1 hempty

end

end FunctorialResolution.EmbeddedResolution

end
