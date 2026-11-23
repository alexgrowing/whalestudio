import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.ArchEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TypeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IntSurjPi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GaloisTwistFiniteAdelicPoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.LiesOverUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.FiniteAdeleInclusionInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.UiwAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.RigidE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.RigidF
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LineEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LintegralInvUniqueHaar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ProjEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.InfSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AmpSlot
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.GoodEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

private theorem fin_pre {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (Pl F)) (hS : S.Finite) : {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  have hfib : ∀ v : Pl F, {w : Pl E | w.under (𝓞 F) = v}.Finite := fun v => by
    refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
    rintro w rfl
    exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩
  exact hS.preimage' fun v _ => hfib v

private theorem under_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext (w.2.over).symm

private theorem at_mono {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]
    {S S' : Set (Pl K)} (h : S ⊆ S') {V : Submodule ℂ (LL μ)} {Λ : (K →+* ℂ) → Multiset ℂ} {t : Pl K → Multiset ℂ}
    (H : At μ S V Λ t) : At μ S' V Λ t :=
  ⟨H.1, fun w hw => H.2 w fun h' => hw (h h')⟩

private theorem geo_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n l : ℕ}
    {μE : Measure (G1 E n)} [μE.IsHaarMeasure] {μF : Measure (G1 F n)} [μF.IsHaarMeasure] {θ : Twist μE}
    {𝔢 𝔢' : Side θ l} {𝔣 : Side (Twist.id μF) l} {c : ℂ} (h1 : 𝔢'.toAmp = 𝔢.toAmp) (h2 : 𝔢'.g = 𝔢.g)
    (h3 : 𝔢'.Uq 0 = 𝔢.Uq 0) (h : GeoPair 𝔢 𝔣 c) : GeoPair 𝔢' 𝔣 c := by
  unfold GeoPair Side.Rep at h ⊢
  rw [h1, h2, h3]
  exact h

private theorem hecke_smul {K : Type} [Field K] [NumberField K] {n : ℕ} {D : TypeDat K n} {f : TG K n}
    (h : D.Hecke f) (c : ℂ) : D.Hecke (c • f) := by
  intro g
  have e1 : ∀ x, (c • f) x = c * f x := fun x => rfl
  simp only [e1]
  refine ⟨?_, ?_⟩
  · simp only [mul_left_comm (D.e _)]
    rw [integral_const_mul, (h g).1]
  · simp only [mul_assoc]
    rw [integral_const_mul, (h g).2]

private theorem ind_inv {G : Type} [Group G] (U : Subgroup G) (φ : G → ℂ)
    (hφ : ∀ x, φ x = (U : Set G).indicator 1 x) : ∀ u ∈ U, ∀ x, φ (u * x) = φ x ∧ φ (x * u) = φ x := by
  intro u hu x
  have h1 : u * x ∈ U ↔ x ∈ U := Subgroup.mul_mem_cancel_left U hu
  have h2 : x * u ∈ U ↔ x ∈ U := Subgroup.mul_mem_cancel_right U hu
  simp only [hφ, Set.indicator, SetLike.mem_coe, h1, h2, Pi.one_apply, and_self]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.coreInd :
    CIx → GM.GM → T.LiftAll → CoreInd := by
  intro hCI hGM hLift F E _ _ _ _ _ _ _ _ σ hσ hgen τ₁ τ₂ θ₂ hpair hgal₂ hsw₁ hsw₂ S hSsp hSunr m₁ m₂ B₁ B₂ hA₁ hA₂ μF _
  have hpr : (Module.finrank F E).Prime := hσ ▸ Nat.prime_two
  have hpl := UpperTheory.ConvolutionTheory.T.places F E hpr
  obtain ⟨q, hqsp, hqS⟩ := hpl.1.exists_notMem_finset S
  have hqsp' : GM.Split E q := hqsp
  obtain ⟨w₀⟩ := hpl.2.2.1 q
  have hf1 := fin_pre (E := E) (S : Set (Pl F)) S.finite_toSet
  have hf2 := fin_pre (E := E) (insert q (S : Set (Pl F))) (S.finite_toSet.insert q)
  obtain ⟨SE', hSE'⟩ : ∃ SE' : Finset (Pl E), ∀ w, w ∈ SE' ↔ w.under (𝓞 F) ∈ S :=
    ⟨hf1.toFinset, fun w => by simp⟩
  obtain ⟨SE, hSE⟩ : ∃ SE : Finset (Pl E), ∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q :=
    ⟨hf2.toFinset, fun w => by simp [or_comm]⟩
  obtain ⟨pp⟩ := (UpperTheory.ConvolutionTheory.L1.infSplit F E σ hgen 1 hσ).1 inferInstance
  obtain ⟨D, -⟩ := (UpperTheory.ConvolutionTheory.L1.infSplit F E σ hgen 1 hσ).2 pp
  obtain ⟨κF, eF, κ, e, κ₂, p₁, p₂, k₀, hIF, hSq, hAL⟩ := archEx F E σ hσ hgen τ₁ τ₂ θ₂ hpair hgal₂ hsw₁ hsw₂ D
  have hsph₁ : SphOff (BW.mu1 E 2) τ₁ SE' := fun w hw => (hA₁.2 w fun h => hw ((hSE' w).2 h)).2.1
  have hsph₂ : SphOff (BW.mu1 E 2) τ₂ SE' := fun w hw => (hA₂.2 w fun h => hw ((hSE' w).2 h)).2.1
  obtain ⟨U₀, f, hU₀, hf0, hsec, hfA, hfF⟩ := hAL.ex SE' hsph₁ hsph₂
  obtain ⟨L, U, hLS, hU, hUle, hUq, hlev, hLφ, htw⟩ :=
    locSm F E σ hσ hgen (2 + 2) (by norm_num) q w₀ S hqS hSunr hSsp U₀ hU₀ SE hSE
  have hLL := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws (K := E) (2 + 2) SE).1 U hU
  obtain ⟨Dt, hTy, hSt⟩ := typeOf E (2 + 2) κ e hAL.idem (levOn SE U) hLL.2 hLL.1.2
  have hflat := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr (BW.mu1 E 2) τ₁ τ₂ κ e hAL.idem).2.1 f hsec.cont
  have hle : levOn SE U ≤ levOn SE' U₀ := by
    intro u hu
    have hu' : ∀ v, finAt v (finEmb E (2 + 2) u) ∈
        (if v ∈ SE then U v else GLnLocal.integralGL (v.adicCompletion E) (2 + 2)) := hu
    show ∀ v, finAt v (finEmb E (2 + 2) u) ∈
        (if v ∈ SE' then U₀ v else GLnLocal.integralGL (v.adicCompletion E) (2 + 2))
    intro v
    have h := hu' v
    by_cases h1 : v ∈ SE'
    · have h1' := (hSE' v).1 h1
      rw [if_pos ((hSE v).2 (Or.inl h1')), ] at h
      rw [if_pos h1]
      exact hUle v h1' h
    · rw [if_neg h1]
      split_ifs at h with h2
      · exact (hU v).2 h
      · exact h
  have hfF' : FixF (levOn SE U) f := fun u hu g => hfF u (hle hu) g
  obtain ⟨θ, hθK⟩ := UpperTheory.ConvolutionTheory.K.galTwistEx E (2 + 2) (BW.mu1 E (2 + 2)) σ.toRingEquiv
  have hgl := galLoc F E σ hσ hgen (2 + 2) (by norm_num) (BW.mu1 E (2 + 2)) θ
  have hθ : IsGalTwist σ θ := hgl.1.2 hθK
  obtain ⟨hinv, harc, -⟩ := hgl.2 hθ
  have htw' := htw (BW.mu1 E (2 + 2)) θ hθ
  have hSta : Stable Dt θ := hSt (BW.mu1 E (2 + 2)) θ (harc D eF e hSq) htw' hinv
  have hpair' : Pair (BW.mu1 E 2) τ₂ τ₁ := ⟨hpair.irr₂, hpair.irr₁, hpair.orth.symm⟩
  obtain ⟨d, ⟨A⟩⟩ := lineEx E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair Dt
  obtain ⟨d', ⟨A'⟩⟩ := lineEx E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' Dt
  obtain ⟨⟨P, hP⟩, -⟩ := projEx E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair Dt d d' A A'
  obtain ⟨s, hs_sec, hs_op⟩ := convU E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair Dt d d' A A' σ.toRingEquiv θ θ₂
    hθK hgal₂ hSta hsw₁ hsw₂
  have hHH : Continuous (HP (K := E) 2 2) := (hpSpec (K := E)).2.2.2.1
  have hflc : Continuous (flat 0 f) :=
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hHH))).mul hsec.cont
  have hfne : flat 0 f ≠ 0 := fun h => hf0 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr (BW.mu1 E 2) τ₁ τ₂ κ e hAL.idem).2.2.1 f 0
    (h.trans (by funext x; simp [flat])))
  let νF : Measure (archGroup F (2 + 2)) := Measure.haar
  haveI hνE : (Measure.map (glueA D (2 + 2)) (Measure.pi fun _ => νF)).IsHaarMeasure :=
    (UpperTheory.ConvolutionTheory.L1.archBasic F E σ 1 D (2 + 2)).2.2.2.2.2.2.1 νF
  obtain ⟨b, a, aE, aF, hsl, hBi, g₀, hg₀⟩ := ampEx F E σ D (2 + 2) (by norm_num) κF eF κ e hIF hAL.idem hSq
    (Measure.map (glueA D (2 + 2)) (Measure.pi fun _ => νF)) νF rfl (flat 0 f) hflc hfne (hflat.1.2 hfA)
  obtain ⟨hAE, hAF⟩ := UpperTheory.ConvolutionTheory.L1.ampPosition F E σ 1 D (2 + 2) _ νF b a aE aF hsl
  have hAP : GM.ArchPair σ _ νF aE aF 1 := @UpperTheory.ConvolutionTheory.L1.pairPosition F E _ _ _ _ _ _ _ σ 1 hσ D (2 + 2) _ _ νF _ b a aE aF hsl
  obtain ⟨cκ, hcκ, hG⟩ := hGM F E σ hgen hpr (2 + 2) (by norm_num) (BW.mu1 E (2 + 2)) μF θ hθ q w₀ hqsp' _ νF aE aF 1 one_pos
    (hAE (BW.mu1 E (2 + 2))) (hAF μF) (@hAP)
  obtain ⟨ν, hν⟩ := UpperTheory.ConvolutionTheory.T.goodEx (2 + 2) (by norm_num)
  have hG' := hG L ν hν
  rw [hσ] at hG'
  obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG'
  obtain ⟨𝔢', φ, w₁, h1, h2, h3, h4, hφ, hten, c, hc, hca⟩ :=
    sideX F E σ hσ hgen (2 + 2) (by norm_num) (BW.mu1 E (2 + 2)) θ hθ q w₀ hqsp' L _ aE ν 𝔢 h𝔢 hLφ
  have hgeo' := geo_congr h1 h2 h3 hgeo
  have hU' : 𝔢'.toAmp.U = levOn SE U := by rw [h1]; exact h𝔢.2.2.2.1.trans hlev
  have ha₀ : 𝔢'.toAmp.a₀ = aE := by rw [h1]; exact h𝔢.2.1
  have hν' : 𝔢'.toAmp.ν = Measure.map (glueA D (2 + 2)) (Measure.pi fun _ => νF) := by rw [h1]; exact h𝔢.1
  have hSE𝔢 : ∀ w, w ∈ 𝔢'.toAmp.S ↔ w ∈ SE := fun w => by
    rw [h1, hSE w, ← hLS]; exact h𝔢.2.2.1 w
  have hUq0 : 𝔢'.Uq 0 = Uiw (BW.mu1 E (2 + 2)) w₀.1 ν := h3.trans h𝔢.2.2.2.2.2
  have hφ' : ∀ x, φ x = (levOn SE U : Set (FA E (2 + 2))).indicator 1 x := fun x => by
    rw [hφ x, ← hU', h1]
  have hinvφ := ind_inv (levOn SE U) φ hφ'
  have hBi' : BiA κ e 𝔢'.toAmp.a₀ := ha₀ ▸ hBi
  have hg_hecke : Dt.Hecke 𝔢'.g := hten ▸ hTy.hecke _ φ hBi' hinvφ
  have ha_hecke : Dt.Hecke 𝔢'.a := hca ▸ hecke_smul hg_hecke c
  have hlevel : Dt.Level (levOn SE U) := hTy.level
  have hsub : {w : Pl E | w.under (𝓞 F) ∈ S} ⊆ 𝔢'.toAmp.S := fun w hw =>
    (hSE𝔢 w).2 ((hSE w).2 (Or.inl hw))
  have hat₁ := at_mono hsub hA₁
  have hat₂ := at_mono hsub hA₂
  have hs₁ : IsSummand (BW.mu1 E 2) τ₁ := ⟨hpair.irr₁.le, hpair.irr₁.closed, hpair.irr₁.inv, hpair.irr₁.ne, hpair.irr₁.irr⟩
  have hs₂ : IsSummand (BW.mu1 E 2) τ₂ := ⟨hpair.irr₂.le, hpair.irr₂.closed, hpair.irr₂.inv, hpair.irr₂.ne, hpair.irr₂.irr⟩
  have hrE := rigidE E τ₁ τ₂ hpair 𝔢'.toAmp.S 𝔢'.toAmp.finS m₁ m₂ B₁ B₂ hat₁ hat₂
  have hw₀S : w₀.1 ∈ SE := (hSE _).2 (Or.inr (under_of w₀))
  have hw₁S : w₁.1 ∈ SE := (hSE _).2 (Or.inr (under_of w₁))
  have hI₀ := hUq w₀.1 (under_of w₀)
  have hI₁ := hUq w₁.1 (under_of w₁)
  have hUa := uiwAct E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₁ τ₂ hpair SE U hU Dt hlevel d d' A A'
  have hUb := uiwAct E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' SE U hU Dt hlevel d' d A' A
  have hz : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  have hv : ∀ i : ZMod 2, ∃ s', Act A.J (𝔢'.Uq i) s' := fun i => by
    rcases hz i with rfl | rfl
    · rw [hUq0]; exact ((hUa _ hw₀S hI₀ ν).1).imp fun _ h => h.1
    · rw [h4]; exact ((hUa _ hw₁S hI₁ ν).1).imp fun _ h => h.1
  have hu : ∀ i : ZMod 2, ∃ s', Act A'.J (𝔢'.Uq i) s' := fun i => by
    rcases hz i with rfl | rfl
    · rw [hUq0]; exact ((hUb _ hw₀S hI₀ ν).1).imp fun _ h => h.1
    · rw [h4]; exact ((hUb _ hw₁S hI₁ ν).1).imp fun _ h => h.1
  choose vv hvv using hv
  choose uu huu using hu
  obtain ⟨βa, hβa⟩ := convR E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' Dt d' d A' A 𝔢'.a ha_hecke
  obtain ⟨βg, hβg⟩ := convR E (BW.mu1 E (2 + 2)) (BW.mu1 E 2) τ₂ τ₁ hpair' Dt d' d A' A 𝔢'.g hg_hecke
  let 𝔵 : Fam 𝔢' :=
    { τ₁ := τ₁, τ₂ := τ₂, pair := hpair, m₁ := m₁, m₂ := m₂, B₁ := B₁, B₂ := B₂, at₁ := hat₁, at₂ := hat₂
      smo₁ := fun V hV hAt => UpperTheory.ConvolutionTheory.Dp.atInj E 2 (BW.mu1 E 2) V τ₁ hV hs₁ _ 𝔢'.toAmp.finS B₁ hAt.2 hat₁.2
      smo₂ := fun V hV hAt => UpperTheory.ConvolutionTheory.Dp.atInj E 2 (BW.mu1 E 2) V τ₂ hV hs₂ _ 𝔢'.toAmp.finS B₂ hAt.2 hat₂.2
      rigid := hrE.1, D := Dt, level := hU' ▸ hlevel, d := d, d' := d', A := A, A' := A', P := P, isP := hP
      σ := σ.toRingEquiv, θ₂ := θ₂, gal := hθK, gal₂ := hgal₂, stable := hSta, swap₁ := hsw₁, swap₂ := hsw₂
      s := s, s_sec := hs_sec, s_op := hs_op, a_hecke := ha_hecke, g_hecke := hg_hecke, βa := βa, βg := βg
      a_acts := hβa, g_acts := hβg, u := uu, v := vv, u_act := huu, v_act := hvv
      u_comm := by rw [hUq0]; exact (hUa _ hw₀S hI₀ ν).2 P hP }
  have hrig : ∀ (b : Datum F (2 + 2)) Λ' t', b.Pt 𝔣.toAmp.S Λ' t' →
      ¬ (𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w) := fun b Λ' t' hb h =>
    rigidF hLift F E σ hσ hgen τ₁ τ₂ θ₂ hpair hgal₂ hsw₁ hsw₂ 𝔢'.toAmp.S 𝔣.toAmp.S 𝔢'.toAmp.finS 𝔣.toAmp.finS
      m₁ m₂ B₁ B₂ hat₁ hat₂ b Λ' t' hb h.2
  obtain ⟨N, hN, hid⟩ := hCI F E (BW.mu1 E (2 + 2)) μF θ 𝔢' 𝔣 _ hgeo' 𝔵 hrig
  have hSpl : ∀ w ∈ SE, GM.Split E (w.under (𝓞 F)) ∧ ∀ w' : Pl E, w'.under (𝓞 F) = w.under (𝓞 F) → w' ∈ SE := by
    intro w hw
    refine ⟨?_, fun w' h => (hSE w').2 (h ▸ (hSE w).1 hw)⟩
    rcases (hSE w).1 hw with h | h
    · exact hSsp _ h
    · rw [h]; exact hqsp'
  obtain ⟨v₀, hv₀⟩ : f ∈ LinearMap.range A.sec :=
    (A.onto f).2 ⟨hsec, (hTy.fix f hsec.cont).2 ⟨hfA, hfF'⟩⟩
  have hnz : ∃ v g, ∫ y, 𝔢'.toAmp.a₀ y * flat 0 (𝔵.A.sec v) (g * archP E (2 + 2) y) ∂𝔢'.toAmp.ν ≠ 0 := by
    refine ⟨v₀, g₀, ?_⟩
    change ∫ y, 𝔢'.toAmp.a₀ y * flat 0 (A.sec v₀) (g₀ * archP E (2 + 2) y) ∂𝔢'.toAmp.ν ≠ 0
    rw [hv₀, ha₀, hν']
    exact hg₀
  obtain ⟨x, hx, hfr⟩ := famNe F E σ hσ hgen (BW.mu1 E (2 + 2)) θ hθ 𝔢' 𝔵 κ e κ₂ p₁ p₂ k₀ hAL SE U hU hSpl hU' hTy htw'
    w₀.1 hw₀S hI₀ ν hν.1.antitone hUq0 φ hφ' hten ⟨c, hc, hca⟩ hBi' hnz N hN
  obtain ⟨j, hj1, hj2⟩ := (hfr.and_eventually (hid x hx)).exists
  have hcusp : 𝔢'.tr (fun V => At (BW.mu1 E (2 + 2)) 𝔢'.toAmp.S V 𝔵.Λ 𝔵.t) x j = 0 := by
    have : {V : Submodule ℂ (LL (BW.mu1 E (2 + 2))) | IsSummand (BW.mu1 E (2 + 2)) V ∧
        V.map (θ.U : LL (BW.mu1 E (2 + 2)) →ₗ[ℂ] LL (BW.mu1 E (2 + 2))) = V ∧
        At (BW.mu1 E (2 + 2)) 𝔢'.toAmp.S V 𝔵.Λ 𝔵.t} = ∅ :=
      Set.eq_empty_of_forall_notMem fun V hV => hrE.2 (BW.mu1 E (2 + 2)) V hV.1 hV.2.2
    unfold Side.tr
    rw [this, finsum_mem_empty]
  rw [hcusp, zero_add] at hj2
  have hne : 𝔣.tr (fun V => ∃ Λ' t', At μF 𝔣.toAmp.S V Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w) x j ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hj2
    exact hj1 ((mul_eq_zero.1 hj2).resolve_left (by norm_num))
  obtain ⟨V, hV, -, Λ', t', hAt, hΛ, ht⟩ : ∃ V : Submodule ℂ (LL μF), IsSummand μF V ∧
      V.map ((Twist.id μF).U : LL μF →ₗ[ℂ] LL μF) = V ∧
      ∃ Λ' t', At μF 𝔣.toAmp.S V Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w := by
    by_contra hno
    apply hne
    have hemp : {V : Submodule ℂ (LL μF) | IsSummand μF V ∧ V.map ((Twist.id μF).U : LL μF →ₗ[ℂ] LL μF) = V ∧
        ∃ Λ' t', At μF 𝔣.toAmp.S V Λ' t' ∧ 𝔵.Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢'.toAmp.S, 𝔵.t w = bcSat t' w} = ∅ :=
      Set.eq_empty_of_forall_notMem fun V hV => hno ⟨V, hV⟩
    unfold Side.tr
    rw [hemp, finsum_mem_empty]
  exact ⟨V, Λ', t', hV, ⟨_, 𝔣.toAmp.finS, hAt⟩, hΛ,
    Filter.mem_of_superset 𝔢'.toAmp.finS.compl_mem_cofinite fun w hw => ht w hw⟩
