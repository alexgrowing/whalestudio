import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.CompDecomp

open Filter Topology

theorem tendsto_one_sub_sum (F : Type) [Field F] [NumberField F] :
    Tendsto (fun Q : Finset (HeightOneSpectrum (𝓞 F)) => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop (𝓝 0) := by
  classical
  let A : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) :=
    fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let y : Finset (HeightOneSpectrum (𝓞 F)) → (∀ v, A v) := fun Q v =>
    ⟨if v ∈ Q then 0 else 1, by
      by_cases h : v ∈ Q
      · rw [if_pos h]; exact (v.adicCompletionIntegers F).zero_mem
      · rw [if_neg h]; exact (v.adicCompletionIntegers F).one_mem⟩
  let z : ∀ v, A v := fun v => ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hy : Tendsto y atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_ge_atTop {v}] with Q hQ
    have hv : v ∈ Q := Finset.singleton_subset_iff.mp hQ
    apply Subtype.ext
    show (if v ∈ Q then (0 : v.adicCompletion F) else 1) = 0
    rw [if_pos hv]
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      A Filter.cofinite) := RestrictedProduct.isEmbedding_structureMap.continuous
  have key : ∀ Q, (1 : Af F) - ∑ v ∈ Q, singleV F v 1 =
      RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A Filter.cofinite (y Q) := by
    intro Q
    apply FiniteAdeleRing.ext
    intro w
    have hw : ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) w = evalV F w ((1 : Af F) - ∑ v ∈ Q, singleV F v 1) := rfl
    rw [hw, map_sub, map_one, map_sum]
    show _ = (if w ∈ Q then (0 : w.adicCompletion F) else 1)
    by_cases h : w ∈ Q
    · rw [Finset.sum_eq_single_of_mem w h (fun b _ hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (Ne.symm hb)),
        GlobalTheory.LatVac.evalV_singleV_same, if_pos h, sub_self]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.LatVac.evalV_singleV_ne F b w (by rintro rfl; exact h hb)),
        if_neg h, sub_zero]
  have h0 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
      Filter.cofinite z = (0 : Af F) :=
    by
      apply FiniteAdeleRing.ext
      intro w
      rfl
  have h1 : Tendsto (fun Q => (1 : Af F) - ∑ v ∈ Q, singleV F v 1) atTop
      (𝓝 (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) A
        Filter.cofinite z)) :=
    ((hc.tendsto z).comp hy).congr (fun Q => (key Q).symm)
  rw [h0] at h1
  exact h1

variable {D : D7}

private theorem infComponent_algebraMap_pairA {D : D7} (a : Ainf D.host.F) (b : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F a b)) = a ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

private theorem sum_sgW_plTau_eq_one (D : D7) :
    ∑ τ : D.what₂.Tau, GlobalTheory.AutFunCompare.sgW (plTau D τ) 1 = (1 : Ainf D.host.F) := by
  classical
  have hb := (GlobalTheory.CMTypePlaces.places_bijective D).sum_comp
    (fun w : InfinitePlace D.host.F => GlobalTheory.AutFunCompare.sgW w (1 : w.Completion))
  have h : ∑ w : InfinitePlace D.host.F, GlobalTheory.AutFunCompare.sgW w (1 : w.Completion) = (1 : Ainf D.host.F) := by
    have h' := Finset.univ_sum_single (1 : ∀ w : InfinitePlace D.host.F, w.Completion)
    simp only [Pi.one_apply] at h'
    simp only [GlobalTheory.AutFunCompare.sgW]
    exact h'
  exact hb.trans h

private theorem af_ext_of_fstA_sndA {F : Type} [Field F] [NumberField F] {x y : AF F}
    (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) : x = y :=
  Prod.ext h1 h2

private theorem fstA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    fstA F (pairA F a b) = a := rfl

private theorem sndA_pairA_twisted_operators {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) :
    sndA F (pairA F a b) = b := rfl

theorem one_sub_sum_idem (P : Finset (Place D)) (hP : P.toRight = Finset.univ) :
    1 - ∑ p ∈ P, idem D p = algebraMap (AF D.host.F) (AE D)
      (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) := by
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hP]
  rw [show (1 : AE D) - (∑ v ∈ P.toLeft, idem D (.inl v) + ∑ τ : D.what₂.Tau, idem D (.inr τ)) =
      algebraMap (AF D.host.F) (AE D) (1 - (∑ v ∈ P.toLeft, pairA D.host.F 0 (singleV D.host.F v 1) +
        ∑ τ : D.what₂.Tau, pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0)) by
    rw [map_sub, map_add, map_one, map_sum, map_sum]
    rfl]
  congr 1
  apply af_ext_of_fstA_sndA
  · simp [fstA_pairA_twisted_operators, map_sum, sum_sgW_plTau_eq_one D]
  · simp [sndA_pairA_twisted_operators, map_sum]

theorem exists_eq_sum_wAt_add_two_smul : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : WO S T, ∃ P₀ : Finset (Place D), ∀ P : Finset (Place D), P₀ ⊆ P → ∃ u ∈ (latO S T ΛS ΛT fun _ => True), w = ∑ p ∈ P, wAt p w + 2 • u := by
  intro D S T ΛS ΛT hS hT w
  classical
  have hU := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 2 two_pos
  let g : Af D.host.F → WO S T := fun e => algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 e) • w
  have hg : Continuous g := by
    have h1 : Continuous fun e : Af D.host.F => pairA D.host.F 0 e :=
      (continuous_const.prodMk continuous_id : Continuous fun e : Af D.host.F => ((0 : Ainf D.host.F), e))
    have h2 : Continuous (algebraMap (AF D.host.F) (AE D)) := by
      have hs : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun r => r • (1 : AE D) := by
        funext r
        exact Algebra.algebraMap_eq_smul_one r
      rw [hs]
      exact Continuous.smul (f := fun r : AF D.host.F => r) (g := fun _ : AF D.host.F => (1 : AE D))
        continuous_id continuous_const
    exact (h2.comp h1).smul continuous_const
  have hg0 : g 0 = 0 := by
    show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 0) • w = 0
    rw [show pairA D.host.F 0 0 = 0 from rfl, map_zero, zero_smul]
  have hlim : Tendsto (fun Q => g (1 - ∑ v ∈ Q, singleV D.host.F v 1)) atTop (𝓝 0) := by
    have h := (hg.tendsto 0).comp (tendsto_one_sub_sum D.host.F)
    rw [hg0] at h
    exact h
  have hmem : (0 : WO S T) ∈ {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - (2 : ℕ) • l).map (finPart D) = 0} := by
    simp only [Set.mem_ofPred_eq]
    refine ⟨0, zero_mem _, ?_⟩
    simp
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 (hlim.eventually_mem (hU.mem_nhds hmem))
  refine ⟨Q₀.disjSum Finset.univ, fun P hP => ?_⟩
  have hR : P.toRight = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro τ
    rw [Finset.mem_toRight]
    exact hP (Finset.inr_mem_disjSum.2 (Finset.mem_univ τ))
  have hL : Q₀ ⊆ P.toLeft := by
    intro v hv
    rw [Finset.mem_toLeft]
    exact hP (Finset.inl_mem_disjSum.2 hv)
  obtain ⟨l, hl, hfin⟩ := hQ₀ _ hL
  refine ⟨l, hl, ?_⟩
  have hrest : w - ∑ p ∈ P, wAt p w = g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) := by
    show w - ∑ p ∈ P, wAt p w =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1)) • w
    rw [← one_sub_sum_idem P hR, sub_smul, one_smul, Finset.sum_smul]
    congr 1
  have hl0 := GlobalTheory.SplitScalar.latO_fin hl
  have h2l : g (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1) = (2 : ℕ) • l := by
    ext i j
    apply GlobalTheory.SplitScalar.adele_ext
    · have hij := congrFun (congrFun hl0 i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at hij
      show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (1 - ∑ v ∈ P.toLeft, singleV D.host.F v 1))
        * w i j) = infPart D ((2 : ℕ) • l i j)
      rw [map_mul, infComponent_algebraMap_pairA, TensorProduct.zero_tmul, zero_mul, map_nsmul, hij, smul_zero]
    · have hij := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply, map_sub] at hij
      exact sub_eq_zero.1 hij
  rw [← h2l, ← hrest]
  exact (add_sub_cancel _ _).symm

end GlobalTheory.PlaceTensor.CompDecomp
