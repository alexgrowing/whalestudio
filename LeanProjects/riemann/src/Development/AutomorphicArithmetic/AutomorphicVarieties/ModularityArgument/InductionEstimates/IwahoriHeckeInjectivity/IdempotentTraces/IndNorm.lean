import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.NormOfSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SwapAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.NormIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ConjIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbTwo

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

private theorem U_invol {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ)
    (h : ∀ g, θ.e (θ.e g) = g) (v : L2 μ) : θ.U (θ.U v) = v := by
  have hp' : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, θ.e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by
    rw [← θ.mem_gam, θ.e.apply_symm_apply]
  obtain ⟨h2, q2⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (Gam K n) μ θ.e.symm hg' hp'
  have hs : ∀ g, θ.e.symm (θ.e.symm g) = g := fun g => by
    have := h (θ.e.symm (θ.e.symm g))
    rw [θ.e.apply_symm_apply, θ.e.apply_symm_apply] at this
    exact this.symm
  refine Lp.ext ?_
  filter_upwards [θ.U_spec (θ.U v), q2.quasiMeasurePreserving.ae_eq_comp (θ.U_spec v)] with y a b
  simp only [Function.comp_apply] at b
  rw [a, b, h2, hs]
  congr 1
  exact Quotient.out_eq y

private theorem irr_of {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {V : Submodule ℂ (L2 μ)} (h : IsSummand μ V) : CuspIrr μ V :=
  ⟨h.le, h.closed, h.ne_bot, fun g v hv => h.inv g v hv, fun ρ a b c => h.irred ρ a b c⟩

private theorem unr_of_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (v : Pl K) (h : GM.Split M v) : GM.Unr M v := by
  rintro ⟨w, hl⟩
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hl.over
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w]
    have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
      ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.2 (Nat.eq_one_of_mul_eq_one_right h1)

private theorem sat_iff {M : Type} [Field M] [NumberField M] [IsTotallyComplex M] {n : ℕ} {μ : Measure (G1 M n)} [μ.IsHaarMeasure]
    {π : CuspSub M n} {V : Submodule ℂ (L2 μ)} (h : Dp.Carries μ π V) (w : Pl M) (B : Multiset ℂˣ) :
    (CG.mk π).HasSat w B ↔ SSat μ V w (B.map fun b : ℂˣ => (b : ℂ)) := by
  rw [Dp.sSatIff M n μ π V h w]
  constructor
  · exact fun hB => ⟨B, rfl, hB⟩
  · rintro ⟨B', e, hB⟩
    rw [Multiset.map_injective Units.val_injective e]
    exact hB

private theorem exAt {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (hn : 0 < n) {μ : Measure (G1 E n)}
    [μ.IsHaarMeasure] {V : Submodule ℂ (L2 μ)} (hV : IsSummand μ V) (S : Set (Pl E)) (h : ∀ w ∉ S, ∃ B, SSat μ V w B) :
    ∃ m B, At μ S V m B := by
  choose m hm using fun τ => ((Dp.parEx E n hn μ V hV).1 τ).exists
  refine ⟨m, fun w => if hw : ∃ B, SSat μ V w B then hw.choose else 0, hm, fun w hw => ?_⟩
  have hx := h w hw
  simp only [dif_pos hx]
  exact hx.choose_spec

private theorem emb_two {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (h2 : Module.finrank K M = 2) (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) (τ τ' : M →+* ℂ) (hne : τ ≠ τ')
    (he : τ.comp (algebraMap K M) = τ'.comp (algebraMap K M)) : τ.comp σ.toRingEquiv.toRingHom = τ' :=
  _root_.UpperTheory.Reformulated.B.Qe21.emb_two h2 σ hσ τ τ' hne he

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indNorm :
    CoreInd → IndNorm := by
  intro hC K M _ _ _ _ _ _ _ _ h2 π hn hc hb
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  have hcard : Nat.card (M ≃ₐ[K] M) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (M ≃ₐ[K] M) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : M ≃ₐ[K] M)
  have hgen : ∀ τ : M ≃ₐ[K] M, τ ∈ Subgroup.zpowers σ := fun τ => mem_zpowers_of_prime_card hcard hσ
  obtain ⟨-, hAtE, -, -, -, θ, hθ, hst⟩ :=
    UpperTheory.ConvolutionTheory.T.carryLift K M σ hgen hp 2 two_pos (BW.mu1 M 2) (BW.mu1 K 2)
  have hG := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc K M σ h2 hgen 2 two_pos (BW.mu1 M 2) θ
  have hIsGal := hG.1.1 hθ
  obtain ⟨hinv, -, hspl⟩ := hG.2 hθ
  obtain ⟨τ₁, hτ₁⟩ : ∃ V, Dp.Carries (BW.mu1 M 2) π V :=
    ⟨_, (Dp.exSummand M 2 _ π _).2 ⟨(Dp.normIff M 2 π).1 hn, rfl⟩⟩
  have hs₁ := hτ₁.summand
  obtain ⟨τ₂, hτ₂d⟩ : ∃ τ₂, τ₁.map (θ.U : L2 (BW.mu1 M 2) →ₗ[ℂ] L2 (BW.mu1 M 2)) = τ₂ := ⟨_, rfl⟩
  have hs₂ : IsSummand (BW.mu1 M 2) τ₂ := hτ₂d ▸ (Dp.twSummand M 2 _ θ τ₁).1 hs₁
  have hback : τ₂.map (θ.U : L2 (BW.mu1 M 2) →ₗ[ℂ] L2 (BW.mu1 M 2)) = τ₁ := by
    rw [← hτ₂d]
    ext v
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      show θ.U (θ.U u) ∈ τ₁
      rwa [U_invol θ hinv]
    · intro hv
      exact ⟨θ.U v, ⟨v, hv, rfl⟩, U_invol θ hinv v⟩
  have hne : τ₁ ≠ τ₂ := fun e => hc σ hσ ((hst π τ₁ hτ₁).2 (hτ₂d.trans e.symm) σ)
  have hPair : Pair (BW.mu1 M 2) τ₁ τ₂ := ⟨irr_of hs₁, irr_of hs₂, Dp.multiplicity_one_cuspidal_spectrum_normOneGL M 2 _ τ₁ τ₂ hs₁ hs₂ hne⟩
  obtain ⟨π', hτ₂, -⟩ := Dp.exCusp M 2 _ τ₂ hs₂
  obtain ⟨hsI, hsS⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.swapAt K M σ h2 hgen τ₁ τ₂ θ hPair hIsGal hτ₂d hback
  obtain ⟨Λ₁, t₁, S₁, hfin, hAt₁⟩ := hAtE τ₁ hs₁
  let S : Finset (Pl K) := (hfin.image fun w => w.under (𝓞 K)).toFinset.filter (GM.Split M)
  have hS : ∀ v, v ∈ S ↔ GM.Split M v ∧ ∃ w ∈ S₁, w.under (𝓞 K) = v := fun v => by
    simp [S, and_comm]
  have hSs : ∀ v ∈ S, GM.Split M v := fun v hv => ((hS v).1 hv).1
  have hSu : ∀ v ∉ S, GM.Unr M v := fun v _ => by
    by_cases h : GM.Split M v
    · exact unr_of_split v h
    · exact (hb v h).1
  have other : ∀ w : Pl M, GM.Split M (w.under (𝓞 K)) → ∃ w' : Pl M, w' ≠ w ∧ w'.under (𝓞 K) = w.under (𝓞 K) := fun w h => by
    obtain ⟨e, -⟩ := hspl _ h
    haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have hx : e (e.symm ⟨w, hl⟩ + 1) ≠ ⟨w, hl⟩ := fun hh => by
      have := e.injective (hh.trans (e.apply_symm_apply _).symm)
      revert this
      generalize e.symm _ = i
      revert i
      decide
    exact ⟨(e (e.symm ⟨w, hl⟩ + 1)).1, fun hh => hx (Subtype.ext hh), HeightOneSpectrum.ext (e _).2.over.symm⟩
  have hSat₁ : ∀ w : Pl M, w.under (𝓞 K) ∉ S → ∃ B, SSat (BW.mu1 M 2) τ₁ w B := fun w hw => by
    by_cases h : GM.Split M (w.under (𝓞 K))
    · exact ⟨t₁ w, hAt₁.2 w fun hm => hw ((hS _).2 ⟨h, w, hm, rfl⟩)⟩
    · obtain ⟨B, hB⟩ := (hb _ h).2 w rfl
      exact ⟨_, (sat_iff hτ₁ w B).1 hB⟩
  have hSat₂ : ∀ w : Pl M, w.under (𝓞 K) ∉ S → ∃ B, SSat (BW.mu1 M 2) τ₂ w B := fun w hw => by
    by_cases h : GM.Split M (w.under (𝓞 K))
    · obtain ⟨w', hne', hu⟩ := other w h
      obtain ⟨B, hB⟩ := hSat₁ w' (hu ▸ hw)
      exact ⟨B, (hsS w w' hu.symm (Or.inl hne'.symm) B).2 hB⟩
    · obtain ⟨B, hB⟩ := hSat₁ w hw
      exact ⟨B, (hsS w w rfl (Or.inr h) B).2 hB⟩
  obtain ⟨m₁, B₁, hA₁⟩ := exAt two_pos hs₁ {w | w.under (𝓞 K) ∈ S} hSat₁
  obtain ⟨m₂, B₂, hA₂⟩ := exAt two_pos hs₂ {w | w.under (𝓞 K) ∈ S} hSat₂
  obtain ⟨V, Λ, t, hV, ⟨S₃, hf₃, hA₃⟩, hΛ, ht⟩ :=
    hC K M σ h2 hgen τ₁ τ₂ θ hPair hIsGal hτ₂d hback S hSs hSu m₁ m₂ B₁ B₂ hA₁ hA₂ (BW.mu1 K (2 + 2))
  obtain ⟨P, hP, -⟩ := Dp.exCusp K (2 + 2) _ V hV
  refine ⟨P, ?_, ?_⟩
  · refine sysOf K M h2 (CG.mk π) (CG.mk π') (CG.mk P) (fun w w' hu hor B => ?_) ?_
    · rw [sat_iff hτ₂, sat_iff hτ₁]
      exact hsS w w' hu hor _
    · have hev : ∀ᶠ w : Pl M in cofinite, w.under (𝓞 K) ∉ S₃ :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hf₃.compl_mem_cofinite
      have hev' : ∀ᶠ w : Pl M in cofinite, w.under (𝓞 K) ∉ S :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually S.finite_toSet.compl_mem_cofinite
      filter_upwards [ht, hev, hev'] with w hw₁ hw₃ hwS f hf
      obtain ⟨C₁, e₁, c₁⟩ := (Dp.sSatIff M 2 _ π τ₁ hτ₁ w _).1 (hA₁.2 w hwS)
      obtain ⟨C₂, e₂, c₂⟩ := (Dp.sSatIff M 2 _ π' τ₂ hτ₂ w _).1 (hA₂.2 w hwS)
      obtain ⟨C₃, e₃, c₃⟩ := (Dp.sSatIff K (2 + 2) _ P V hP _ _).1 (hA₃.2 _ hw₃)
      have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := NumberField.HeightOneSpectrum.one_lt_absNorm _
      have hfr : f = resDeg K w := by
        have hpl : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) ^ resDeg K w :=
          (UpperTheory.ConvolutionTheory.T.places K M hp).2.2.2.2.1 w
        exact Nat.pow_right_injective hq (hf.symm.trans hpl)
      refine ⟨C₃, c₃, ![C₁, C₂], ?_, ?_⟩
      · intro i
        fin_cases i
        · exact c₁
        · exact c₂
      · apply Multiset.map_injective Units.val_injective
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [Multiset.map_add, ← e₁, ← e₂, hw₁, bcSat, e₃, hfr]
        simp [Multiset.map_map, Function.comp_def]
  · intro τ τ' m m' hne' hk hm hm'
    have e1 : m₁ τ = m := ((Dp.parEx M 2 two_pos _ τ₁ hs₁).1 τ).unique (hA₁.1 τ) ((Dp.sInfIff M 2 _ π τ₁ hτ₁ τ m).2 hm)
    have e2 : m₂ τ = m' := by
      refine ((Dp.parEx M 2 two_pos _ τ₂ hs₂).1 τ).unique (hA₂.1 τ) ((hsI τ m').2 ?_)
      rw [emb_two h2 σ hσ τ τ' hne' hk]
      exact (Dp.sInfIff M 2 _ π τ₁ hτ₁ τ' m').2 hm'
    have e3 : Λ (τ.comp (algebraMap K M)) = m + m' := by
      have := congrFun hΛ τ
      simp only [bcInf] at this
      rw [← this, e1, e2]
    have h4 := hA₃.1 (τ.comp (algebraMap K M))
    rw [e3] at h4
    exact (Dp.sInfIff K (2 + 2) _ P V hP _ _).1 h4
