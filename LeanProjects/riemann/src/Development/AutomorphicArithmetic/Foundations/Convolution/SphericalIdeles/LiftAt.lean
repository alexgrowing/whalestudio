import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.T2SpaceGlCompletionsOver
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AmpFin
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LevelEx
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PosSide
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.GoodEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.InfSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchSlotEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AmpSlot
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.BumpEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.IntPow
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.T
open scoped Classical

section Hilb

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem star_zero_of (B : H →L[ℂ] H) (x : H) (h : (B * star B) x = 0) : star B x = 0 := by
  have e : inner ℂ (star B x) (star B x) = inner ℂ x ((B * star B) x) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rfl
  rw [h, inner_zero_right] at e
  exact inner_self_eq_zero.1 e

private theorem pow_zero_of (B : H →L[ℂ] H) (m : ℕ) : ∀ x : H, ((B * star B) ^ (m + 1)) x = 0 → star B x = 0 := by
  have hs : star (B * star B) = B * star B := by rw [star_mul, star_star]
  induction m with
  | zero => exact fun x h => star_zero_of B x (by simpa using h)
  | succ m ih =>
    intro x h
    rw [pow_succ, ContinuousLinearMap.mul_apply] at h
    have h1 := ih _ h
    have h2 : ((B * star B) * star (B * star B)) x = 0 := by
      rw [hs, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, h1, map_zero]
    have h3 := star_zero_of _ x h2
    rw [hs] at h3
    exact star_zero_of B x h3

private theorem prj_of_mem (V : Submodule ℂ H) {x : H} (h : x ∈ V) : prj V x = x :=
  Submodule.starProjection_eq_self_iff.2 (V.le_topologicalClosure h)

end Hilb

private theorem oinf_congr {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν ν' : Measure (archGroup K n)) [ν.IsHaarMeasure] [ν'.IsHaarMeasure] (h : ν = ν') (a : TI K n) : Oinf μ ν a = Oinf μ ν' a := by
  subst h
  rfl

private theorem fixL_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
    {J J' : Subgroup (Gw n w)} (h : J ≤ J') : fixL μ w J' ≤ fixL μ w J :=
  biInf_mono fun _ hu => Subgroup.map_mono h hu

theorem UpperTheory.ConvolutionTheory.Sph.liftAt (hCI : UpperTheory.ConvolutionTheory.CI) (hGM : UpperTheory.ConvolutionTheory.GM.GM) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (θ : Twist μE),
      IsGalTwist σ θ → ∀ (V : Submodule ℂ (LL μF)) Λ t (S₀ : Set (Pl F)), IsSummand μF V → S₀.Finite → At μF S₀ V Λ t →
      OffAll F n (bcInf (K := E) Λ) (bcSat t) → ∀ v₀ : Pl F, v₀ ∉ S₀ → GM.Unr E v₀ →
      ∃ V' : Submodule ℂ (LL μE), IsSummand μE V' ∧ AtAE μE V' (bcInf Λ) (bcSat t) ∧
        ∀ w : Pl E, w.under (𝓞 F) = v₀ → SSat μE V' w (bcSat t w) := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ V Λ t S₀ hV hS₀ hAt hOff u₀ hu₀ hu₁
  obtain ⟨hinf, hunr, hne, -⟩ := places F E hp
  have hfin : (S₀ ∪ {v | ¬ GM.Unr E v}).Finite := hS₀.union hunr
  set S := hfin.toFinset with hS
  have hS1 : ∀ v ∉ S, v ∉ S₀ ∧ GM.Unr E v := fun v hv => by
    simpa [hS, not_or] using hv
  obtain ⟨q, hq, hqS'⟩ := hinf.exists_notMem_finset (insert u₀ S)
  have hqS : q ∉ S := fun h => hqS' (Finset.mem_insert_of_mem h)
  have hqu : u₀ ≠ q := fun h => hqS' (h ▸ Finset.mem_insert_self _ _)
  have huS : u₀ ∉ S := by simp [hS, hu₀, hu₁]
  obtain ⟨w₀⟩ := hne q
  obtain ⟨U, hU, hv⟩ := levelEx F n μF V hV S fun w hw => (hAt.2 w (hS1 w hw).1).2.1
  obtain ⟨v₀, ⟨⟨hv1, hv2⟩, hv3⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 hv
  obtain ⟨L, hLS, hL⟩ := locUp F E σ hσ hp n hn q w₀ S hqS (fun v h => (hS1 v h).2) U fun v => (hU v).1.2
  have hfix : v₀ ∈ fixF μF (GM.levF L.UF) := by
    have e : GM.levF L.UF = levOn (insert q S) L.UF := by
      unfold levOn
      congr 1
      funext v
      split_ifs with h
      · rfl
      · rw [Finset.mem_insert, not_or] at h
        exact (L.off v (hLS ▸ h.2) h.1).2.2.2
    have hs : ∀ v ∉ S, v₀ ∈ fixL μF v (GLnLocal.integralGL (v.adicCompletion F) n) := fun v h =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv2 v) h
    rw [e, fixLev]
    refine ⟨(Submodule.mem_iInf _).2 fun v => (Submodule.mem_iInf _).2 fun h => hs v fun h' => h (Finset.mem_insert_of_mem h'),
      (Submodule.mem_iInf _).2 fun v => (Submodule.mem_iInf _).2 fun h => ?_⟩
    rcases Finset.mem_insert.1 h with rfl | h
    · rw [L.at_q.2.2.2]
      exact fixL_anti μF v (GLnLocal.iwahori_le_integralGL _ _) (hs v hqS)
    · exact fixL_anti μF v (hL v h).2.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv3 v) h)
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  obtain ⟨⟨p⟩, hD⟩ := (infSplit F E σ hσ m hm).imp (fun h => h inferInstance) id
  obtain ⟨D, -⟩ := hD p
  let νF : Measure (archGroup F n) := Measure.haar
  let π := (rightRegularRep (rationalGLOne F n) μF).compHom (archP F n) continuous_archP
  obtain ⟨b, hb1, hb2, hb3, hb4⟩ := bumpEx F n νF _ π v₀ hv0
  obtain ⟨νE, iE, a, aE, aF, hA⟩ := archPositionEx F E σ m D n νF b hb1 hb2 hb3
  obtain ⟨hAE, hAF⟩ := ampPosition F E σ m D n νE νF b a aE aF hA
  obtain ⟨ν, hν⟩ := goodEx n hn
  obtain ⟨κ, hκ, hG⟩ := hGM F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos (hAE μE) (hAF μF)
    (pairPosition F E σ m hm D n νE νF b a aE aF hA)
  obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG L ν hν
  have hne0 : 𝔣.toAmp.A v₀ ≠ 0 := by
    obtain ⟨s1, -, -, s4⟩ := sqOp F n νF b a aF m hA.sq hA.pow hb3 _ π
    rw [Amp.A, ContinuousLinearMap.comp_apply, h𝔣.2.2.2.1, prj_of_mem _ hfix, oinf_congr μF _ νF h𝔣.1, h𝔣.2.1]
    intro h
    refine hb4 (pow_zero_of _ m v₀ ?_)
    rw [← s1, ← s4]
    exact h
  obtain ⟨x, hx, hxe⟩ := (ampFin F n hn μF 𝔣.toAmp).2 V hV ⟨v₀, hv1, hne0⟩
  have hfS : ∀ v ∉ 𝔣.S, v ∉ S₀ := fun v h => (hS1 v fun h' => h ((h𝔣.2.2.1 v).2 (Or.inl (hLS ▸ h')))).1
  have hoff : OffFam F n 𝔢.S 𝔣.S (bcInf Λ) (bcSat t) := by
    rw [show 𝔢.S = {w : Pl E | w.under (𝓞 F) ∈ 𝔣.S} from Set.ext hgeo.1]
    exact hOff _ 𝔣.finS
  have h1 := hCI F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo (bcInf Λ) (bcSat t) (fun τ => (hAt.1 _).1) (fun w hw => by
    have hs := hAt.2 _ (hfS _ fun h => hw ((hgeo.1 w).2 h))
    refine ⟨by rw [bcSat, Multiset.card_map, hs.1], fun h0 => ?_⟩
    obtain ⟨z, hz, e⟩ := Multiset.mem_map.1 h0
    exact (Dp.parEx F n hn μF V hV).2.2 _ _ hs (eq_zero_of_pow_eq_zero e ▸ hz)) hoff x hx
  have h2 := posSide F E σ hσ hp n hn μF q w₀ νF aF L ν _ 𝔣 hν.1.antitone h𝔣 (fun v h => (hL v (hLS ▸ h)).2.2)
    (fun V => ∃ Λ' t', At μF 𝔣.S V Λ' t' ∧ bcInf (K := E) Λ = bcInf Λ' ∧ ∀ w ∉ 𝔢.S, bcSat t w = bcSat t' w) V x hV
    ⟨Λ, t, ⟨hAt.1, fun v h => hAt.2 v (hfS v h)⟩, rfl, fun _ _ => rfl⟩ hx hxe
  obtain ⟨j, hj2, hj1⟩ := (h2.and_eventually h1).exists
  have hc : (κ : ℂ) * ∏ v ∈ L.S, L.c v ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hκ.ne') (Finset.prod_ne_zero_iff.2 fun v h => (hL v (hLS ▸ h)).1)
  by_contra hno
  refine mul_ne_zero hc hj2 (hj1.symm.trans ?_)
  refine finsum_mem_of_eqOn_zero fun V' hV' => ?_
  refine absurd ⟨V', hV'.1, ⟨𝔢.S, 𝔢.finS, hV'.2.2⟩, fun w hw => hV'.2.2.2 w fun h => ?_⟩ hno
  rcases (h𝔢.2.2.1 w).1 h with h | h
  · exact huS (hw ▸ hLS ▸ h)
  · exact hqu (hw ▸ h)
