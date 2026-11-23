import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBoundAllPlaces
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentIntegralClosureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverDvrExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrExtensionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeOneStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeTwoStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalComparisonOfOrbitsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3FromLocalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlaceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentGenericFibreStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalNumberPermutationInvariantStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrameStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisLinIndepSpanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagOutsidePrimeFibresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagCmTypeDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyDedekindConstantsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagPairChartBundleCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDvrExtensionStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

theorem model_on_hodge_of_family_pos : FamilyExistsPos → HodgeLatticeFlagBound := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ _ Fl S₀ T hT p hpS hpS₀ hHT hp2 hdisc φ hφ A _ _ _
  intro m _ hm O _ _ _ _ _ _ _
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · haveI : IsEmpty (Fin (D.p + D.q)) := by rw [h0]; exact Fin.isEmpty'
    intro τ k _ Q _
    have h1 : ((T.map (Int.castRingHom O)).comp fun i : Fin (D.p + D.q) => (τ, i)).ck (pointIdeal O y) k Q = 0 := by
      simp [LocPair.ck, GroundTheory.Heights₂.Heights.NumbersDVR.pairNum]
    have h3 : ∀ τ', liePs (Ψ := CMType H) (N := D.p + D.q) D.p (k - 1) τ' = 0 := by
      rintro (τ' | τ') <;> simp [liePs]
    have h2 : bracket (N := D.p + D.q) D.p φ p k τ = 0 := by
      simp [bracket, h3]
    rw [h1, h2]
    simp [cycNum]
  have hpP : p.Prime := 𝔐.S_prime p hpS
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨hAD, hAfin, hAinj, hAcst, hloc⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  haveI := hAD
  haveI := hAfin
  obtain ⟨hOint, hOfn⟩ := hloc m O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hModel, hVert⟩ := GlobalTheory.T.localization_model_over_place K J Ω y A hAinj hAcst d hV m O
  have hT2 := hT
  obtain ⟨hS₀, hvb, hsub, e₀, e, hR₀, hR, hfg, hvo⟩ := hT2
  have hTv := hVert ϖ hϖ _ _ T hvo
  have hOinj : Function.Injective (algebraMap O Ω) := hOint.1
  have hb : ∀ t, LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t :=
    GlobalTheory.T.flag_basis_lin_indep_span E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl
  have hfam := hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV hpos Fl.b hb p hpS hHT hp2 hdisc φ hφ A m hm O
  choose Sg hSg ε φ' F hF1 hF2 hF3 w σ Df hDf using hfam
  have hFc : ∀ t, 0 < Fintype.card (F t) - 1 := fun t => by
    have := Fintype.one_lt_card (α := F t)
    omega
  have hN0 : 0 < ∏ t, (Fintype.card (F t) - 1) := Finset.prod_pos fun t _ => hFc t
  obtain ⟨O', _, _, _, _, _, _, Ω', _, _, _, _, _, _, ζ, hO'inj, hζ, hadj⟩ := GlobalTheory.T.exists_dvr_extension_field O Ω hOinj _ hN0
  have hζt : ∀ t, IsPrimitiveRoot (ζ ^ ((∏ t, (Fintype.card (F t) - 1)) / (Fintype.card (F t) - 1)))
      (Fintype.card (F t) - 1) := fun t =>
    hζ.pow hN0 (Nat.div_mul_cancel
      (Finset.dvd_prod_of_mem (fun t => Fintype.card (F t) - 1) (Finset.mem_univ t))).symm
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  haveI : CharZero Ω' := charZero_of_injective_ringHom (algebraMap Ω Ω').injective
  haveI : CharZero O' := (algebraMap O' Ω').charZero
  have hModel' := (GlobalTheory.T.model_over_dvr_extension O Ω K J y d hModel hOint O' Ω' hO'inj).2
  have hfn' := GlobalTheory.T.function_field_dvr_extension O Ω K J y hOfn O' Ω' ζ hadj
  have hTwin : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O'
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O' (fun v => algebraMap Ω Ω' (y v))) d :=
    (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O' _ d).2 ⟨hV.1, hModel'⟩
  have hagree : ∀ s (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) → 𝔐.HT p s q = 𝔐.dR s q :=
    GlobalTheory.T.hodge_flag_outside_prime_fibres E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
  have hLat := GlobalTheory.T.hodge_flag_cm_type_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl S₀ T hT p hpS hpS₀ hagree
  have hag2 : ∀ s, ∀ q : Cpt 𝔐.ξ, q ∈ overPrime 𝔐.ξ p → ¬ InFibre 𝔐.ξ p q → 𝔐.dR s q = 𝔐.HT p s q := by
    intro s q hq hqp
    refine (hagree s q fun p' hp' => ?_).symm
    by_cases h : p' = p
    · subst h; exact hqp
    · exact hq p' hp' h
  have hB := fun s => GlobalTheory.T.arith_variety_dedekind_constants 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d hV A hAinj hAcst p hpP m hm O ϖ hϖ 𝔐.Li
    (labelRk D s) (Fl.b s) (hb s).1 (𝔐.dR s) (𝔐.HT p s) (labelPair D T s) (hLat s) (hag2 s)
  choose B B' v v' hBlat hBfp using hB
  have hC := fun s : CMType H ⊕ CMType H => GlobalTheory.T.flag_pair_chart_bundle_compat O Ω K J y ϖ _ (B s.swap) (B' s.swap) (v s.swap) (v' s.swap) _ _ _ _
    (hBfp s.swap)
  choose C C' u u' hClat hCfp using hC
  have hmm : ∀ {σ' : Type} (Q : LocPair J ℤ σ'),
      (Q.map (Int.castRingHom O)).map (algebraMap O O') = Q.map (Int.castRingHom O') := by
    intro σ' Q
    rw [map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hE := fun s => GlobalTheory.T.model_descent_valuation_fibre O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (B s) (B' s) (v s)
    (v' s) ((labelPair D T s).map (Int.castRingHom O)) (hBfp s)
  choose LB LB' lv lv' hLBlat hLBfp using hE
  have hE2 := fun s => GlobalTheory.T.model_descent_valuation_fibre O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (C s) (C' s) (u s)
    (u' s) ((omPair D T s).map (Int.castRingHom O)) (hCfp s)
  choose LC LC' lu lu' hLClat hLCfp using hE2
  have hRel : ∀ t, Relations (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (φ' t)
      (fun τ => (labelPair D T (ε t τ)).map (Int.castRingHom O'))
      (fun τ => (omPair D T (ε t τ)).map (Int.castRingHom O')) := by
    intro t
    obtain ⟨-, -, hpre, hfamOf⟩ := hDf t
    obtain ⟨χ, Df', hM3, hspan⟩ := GlobalTheory.T.model_descent_generic_fibre O Ω K J y d hModel hOint O' Ω' hO'inj (F t) p _ (hζt t)
      (D.p + D.q) (Sg t) _ _ (w t) (σ t) (φ' t) (Df t) hpre
    refine GlobalTheory.T.arithmetic_relations_statement_holds O' Ω' K J (fun v => algebraMap Ω Ω' (y v)) ϖ' hϖ' d hTwin hfn' p hpP
      (algebraMap O O' (w t)) χ (φ' t) Df' hM3
      (fun τ => LB (ε t τ)) (fun τ => LB' (ε t τ)) (fun τ => LC (ε t τ)) (fun τ => LC' (ε t τ)) ?_ _ _ ?_
    · intro τ c hc
      have hc' : segreVec y c ≠ 0 := by
        intro h
        apply hc
        show ∏ k, algebraMap Ω Ω' (y ⟨k, c k⟩) = 0
        rw [← map_prod]
        exact (congrArg (algebraMap Ω Ω') h).trans (map_zero _)
      obtain ⟨hl, hW, ho, hoh⟩ := hfamOf c hc' τ
      obtain ⟨s1, s2, s3, s4⟩ := hspan c hc' τ
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [(hLBlat _ c hc').1, (hBlat _ c hc').1, s1, hl]; rfl
      · rw [(hLBlat _ c hc').2, (hBlat _ c hc').2, s2, hW]; rfl
      · rw [(hLClat _ c hc').1, (hClat _ c hc').1, (hBlat _ c hc').1, s3, ho]; rfl
      · rw [(hLClat _ c hc').2, (hClat _ c hc').2, (hBlat _ c hc').2, s4, hoh]; rfl
    · intro τ
      refine ⟨⟨lv (ε t τ), lv' (ε t τ), ?_⟩, ⟨lu (ε t τ), lu' (ε t τ), ?_⟩⟩
      · have h := hLBfp (ε t τ)
        rw [hmm] at h
        exact h
      · have h := hLCfp (ε t τ)
        rw [hmm] at h
        exact h
  have hLoc : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPair D T s).map (Int.castRingHom O')) := by
    refine GlobalTheory.T.local_comparison_of_orbits_holds O' K J (CMType H ⊕ CMType H) _ d p hpP.two_le φ _ _ _ _ fun τ => ?_
    obtain ⟨hrange, hcomm, -, -⟩ := hDf τ
    exact ⟨Sg τ, inferInstance, ε τ, φ' τ, hrange, hcomm, hRel τ⟩
  have hLoc2 : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O')) := by
    intro k hk Q hQ τ
    rcases τ with τ | τ
    · exact hLoc k hk Q hQ (.inl τ)
    · exact hLoc k hk Q hQ (.inr τ)
  have hp0' : (p : O') ≠ 0 := Nat.cast_ne_zero.2 hpP.ne_zero
  have hFlag' := GlobalTheory.T.flag_m3_from_local O' ϖ' hϖ' K J _ d hModel' p hp0' (CMType H) D.p D.q φ (T.map (Int.castRingHom O'))
    (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O'))
    (fun τ => rfl)
    (fun τ => by
      show (dualRev (dualRev (T.comp _))).map _ = _
      rw [dualRev_dualRev]
      rfl)
    (fun τ k Q _ => (GlobalTheory.T.local_number_permutation_invariant O' K J D.q Fin.revPerm _ k Q).1 (p : O')
      (fun i => -(T.map (Int.castRingHom O')).x (τ, Fin.natAdd D.p i)))
    hLoc2
  have hT' : FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p D.p φ
      ((T.map (Int.castRingHom O)).map (algebraMap O O')) := by
    rw [hmm]
    exact hFlag'
  exact (GlobalTheory.T.model_descent_integral_closure O Ω K J y d hModel hOint O' Ω' hO'inj ϖ hϖ p).1 hpP.ne_zero (CMType H) (D.p + D.q) D.p φ
    (T.map (Int.castRingHom O)) hTv hT'

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
