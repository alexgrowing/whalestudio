import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRankTwoAutomorphyOfPatching
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.InertiaLeRangeOfUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcRegAlgPolarizedPairStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoCommStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Bc GlobalTheory.RealGal UpperTheory.V.Af.ExLib
open private UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr
namespace UpperTheory.Gal.SV
theorem attRes_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → AttRes π ι K r := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a ha π P hBC r wt HT H
  have hloc := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L
  have hsl := GlobalTheory.T.satakeParameters_local
  refine (hBC.unr.and (eventually_not_mem K l)).mono ?_
  rintro w ⟨hu, hw⟩ f hf
  obtain ⟨B, hB, hBw⟩ := hu (w.under (𝓞 F)) rfl f hf
  refine ⟨B, hB, ?_⟩
  obtain ⟨⟨σ, hσ⟩, hi⟩ := hloc K a P w
  have hS := ((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw
  have h1 := frob_of (ι := ι) (r := r) hw σ hS fun A h rc hrc => by
    have g := gdOf K Ω A w h rc hrc a σ ((plainOf K a ha P w).2 ⟨_, hBw⟩ σ hσ)
    rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
    exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
  rwa [hf, GlobalTheory.RealGal.AttResProof.algSat_pow] at h1
section Descent
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem local_condition_at_place_of_decomposition_le_range (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ha : 1 ≤ a) {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] {ι : Qbar l ≃+* ℂ} {π : TR.CuspSub F a} {P : CuspSub K a} (hBC : IsBC π P)
    {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (hG : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι (r.comp (res F Ω K)) wt HT) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A v) (hdec : Dec (F := F) A ≤ (res F Ω K).range) {HTF : (F →+* Qbar l) → Multiset ℤ}
    (hHT : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) : At π ι r HTF h := by
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hl hw => by
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have ST := splitTr F K a ha π P hBC v w i ⟨hi.cont, hi.loc⟩
  obtain ⟨⟨σ', hσ'⟩, -⟩ := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L K a P w
  obtain ⟨rc', hrc'⟩ := recTExists K Ω A w h'
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' _ _ i hi
  have inj : ∀ {x y : WD h} {x' y' : WD h'}, WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → x' = y' → x = y :=
    fun hx hy e => S.injective (by rw [(hS _ _).1 hx, (hS _ _).1 hy, e])
  have up : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → Gd (rc' (algNorm σ')) := fun σ hσ hp => by
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    exact gdOf K Ω A w h' rc' hrc' a σ' (UpperTheory.V.Z.Win.SplitTorusFixedPoints.plainTor_of_iso i hi.cont
      (GlobalTheory.LocalFieldIso.continuous_symm i hi.cont) _ _ _ _ e he hp)
  have br : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      ∃ (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (_ : Induces Bw'), Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL :=
    fun O _ _ _ Bw hj => by
      obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw (GlobalTheory.T.local_field_embedding_mem F Ω K l A O Bw hdec)
      exact ⟨Bw', fun x => by rw [e2]; exact hj x, e1, e2, e3⟩
  refine ⟨fun B hB => ST.1.2 ((plainOf K a ha P w).2 (ST.2 ⟨B, hB⟩)), fun σ hσ hp rc hrc => ?_, fun σ hσ hp O _ _ _ Bw hj => ?_,
    fun hl hp => ?_, fun O _ _ _ Bw hj σ hσ hs => ?_⟩
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hy := recTr L.aut.art hi σ σ' e he hrc hrc' hp
    have g := up σ hσ hp
    refine ⟨fun hl => ?_, fun O _ _ _ Bw hj _ => ?_⟩
    · obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
        (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
      exact ⟨x, hx, fun _ => inj hxx hy ((hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2)⟩
    · obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
      obtain ⟨-, a2, -, a4⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
      have hpst := (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.2.1 a2
      exact ⟨hpst, inj (GlobalTheory.T.local_embedding_restrict_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r hpst ι v w h h' hj hj' i hi) hy (a4.tor g.1 g.2)⟩
  · have g := up σ hσ hp
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    obtain ⟨a1, -, a3, -⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
    have D := GlobalTheory.T.local_embedding_compatible_extension F Ω K l (Loc.PP l) A O Bw Bw' e1 e2 e3 a r
    refine ⟨D.1 a1, fun τ LL' τ' hτ => ?_⟩
    obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.T.local_embedding_agree F Ω K l A O Bw Bw' e1 e2 τ LL' τ' hτ
    have hJ := D.2.2.2.2 τK (HT τK) (a3 τK LL' τ'' hind)
    rw [hHT τK, hτK] at hJ
    exact hJ
  · have hp' := ST.1.1 hp
    have g := gdOf K Ω A w h' rc' hrc' a σ' (hp' σ' hσ')
    obtain ⟨t, ht⟩ := winPt UpperTheory.V.Z.Gam.suppFacts UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf K a ha P
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
      (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
    rw [hx.wdOf_eq hl]
    refine UpperTheory.GalN.V.RatioW.descend hi hxx ?_
    rw [(hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2]
    exact ratioT K Ω A w h' rc' hrc' a P t (ht w hp') σ' hσ'
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    exact (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.1
      ((hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').crys σ' hσ' ((GlobalTheory.T.aux_statement_23 F K v w i hi.cont a σ σ' e he).2 hs)).1
end Descent
theorem galois_rep_exists_totally_real_rank_two_of_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Bc.QuadBC2 → AdmissibleReal → GaloisRepExistsTotallyRealGL2 := by
  intro litN qbc adm F Ω _ _ _ _ _ _ l _ ι a ha2 ha π χ hreg hpol
  let S : Set (QCM F Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsBC π P}
  have good : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ P : CuspSub ↥Q.K a, IsBC π P}.Infinite := by
    intro v A hA
    obtain rfl := ha2.out
    have hT := GlobalTheory.T.eventually_has_satake_parameters adm F 2 π
    refine (GlobalTheory.T.infinite_quadratic_fields_split_inertia F Ω (fun u => ∃ B, π.HasSat u B) hT v A hA).mono ?_
    rintro Q ⟨hdec, u, A', ⟨B, hB⟩, hA', hine⟩
    refine ⟨hdec, ?_⟩
    rcases qbc F Q.K Q.two π hreg with ⟨η, hq, htw⟩ | hP
    · exact absurd (_root_.GlobalTheory.T.inertia_le_range_of_unramified_alt litN F Ω Q.K Q.two η hq u A' hA' (unrAt_of_isoTwist adm F 2 ha π η htw u B hB)) hine
    · exact hP
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω v0
  have hS : S.Infinite := (good v0 A0 hA0).mono fun Q hQ => hQ.2
  have key : ∀ Q : ↥S, ∃ (P : CuspSub ↥Q.1.K a)
      (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (↥Q.1.K →+* Qbar l) → Multiset ℤ),
      IsBC π P ∧ UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT := by
    rintro ⟨Q, P, hP⟩
    obtain ⟨hregP, χ', hχ'⟩ := _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change litN F ↥Q.K Q.two a ha π χ P hreg hpol hP
    obtain ⟨r, wt, HT, hr⟩ := _root_.UpperTheory.Gal.SV.rowOf' litN.aut.gal ↥Q.K Ω l ι a ha P χ' hregP hχ'
    exact ⟨P, r, wt, HT, hP, hr⟩
  choose P r wt HT hP hr using key
  have hatt : ∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q) := fun Q =>
    ⟨(hr Q).cont, (hr Q).ss,
      _root_.UpperTheory.Gal.SV.attRes_alt litN F Ω ↥Q.1.K l ι a ha π (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)⟩
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.T.galois_rep_patching_infinite_family F Ω l ι a π S hS r hatt
  obtain ⟨HTF, hcard, hwts, hbc⟩ := hodgeTate F Ω l ι a π hreg
  have hgal : ∀ᶠ Q : ↥S in Filter.cofinite,
      UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) :=
    hev.mono fun Q hQ => props_iso (hr Q) hQ.1 hQ.2
  have hHT : ∀ Q : ↥S, (∀ τ : ↥Q.1.K →+* Qbar l, HT Q τ = HTF (τ.comp (algebraMap F ↥Q.1.K))) ∧
      ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt Q - ·) :=
    fun Q => hbc ↥Q.1.K Q.1.two (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)
  obtain ⟨Q0⟩ : Nonempty ↥S := hS.nonempty.to_subtype
  let τ0 : F →+* Qbar l := ι.symm.toRingHom.comp (Classical.arbitrary (InfinitePlace F)).embedding
  have hwt : ∀ Q : ↥S, wt Q = wt Q0 := fun Q =>
    GlobalTheory.T.eq_of_multiset_symmetric_reflections (HTF τ0) (wt Q) (wt Q0) (by rw [← Multiset.card_pos, hcard]; exact ha) ((hHT Q).2 τ0) ((hHT Q0).2 τ0)
  have hpick : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ∃ Q : ↥S, Dec (F := F) A ≤ (res F Ω ↥Q.1.K).range ∧
        UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) := by
    intro v A hA
    have hfin := (Filter.eventually_cofinite.1 hgal).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((good v A hA).diff hfin).nonempty
    refine ⟨⟨Q, hQ.2⟩, hQ.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQ.2⟩, hc, rfl⟩
  have hD : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A v), At π ι ρ HTF h := fun v A h => by
    obtain ⟨Q, hdec, hQ⟩ := hpick v A h
    exact _root_.UpperTheory.Gal.SV.local_condition_at_place_of_decomposition_le_range litN ha (hP Q) hQ h hdec (hHT Q).1
  have hpl : ∀ w B, π.HasSat w B → PlainAtR π w := fun w B hB => by
    obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω w
    exact (hD w A h).plain B hB
  refine ⟨ρ, wt Q0, HTF, hρc, hρs, hpl, fun w σ hσ hp => ⟨fun A h => (hD w A h).cmp σ hσ hp, fun A h => (hD w A h).ht σ hσ hp⟩,
    fun w hw B hB => ?_, fun w hw A h => (hD w A h).ratio hw, hwts, (hHT Q0).2, fun w A h => (hD w A h).crys⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := GlobalTheory.T.local_global_compatibility_real adm F a π w
  have hS := ((GlobalTheory.T.satakeParameters_local F a w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  exact frob_of hw σ hS fun A h rc hrc => (((hD w A h).cmp σ hσ (hpl w B hB σ hσ) rc hrc).1 hw).isWDOf
    (gdOf F Ω A w h rc hrc a σ (hpl w B hB σ hσ))
end UpperTheory.Gal.SV
end
end
