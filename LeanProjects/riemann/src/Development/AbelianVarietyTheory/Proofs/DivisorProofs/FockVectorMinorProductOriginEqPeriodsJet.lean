import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

def scaleCLM {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) : VC D N N' →L[ℂ] VC D N N' :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ i j => c τ * Z τ i j
      map_add' := fun Z Z' => by funext τ i j; simp [mul_add]
      map_smul' := fun s Z => by funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem scaleCLM_apply {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (Z : VC D N N') :
    scaleCLM c Z = fun τ i j => c τ * Z τ i j := rfl

theorem scaleCLM_coordV {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (k : D.what₂.Tau × Fin N' × Fin N) :
    scaleCLM c (Formalism.MainNotions.TaylorLogMetric.coordV D k) = c k.1 • Formalism.MainNotions.TaylorLogMetric.coordV D k := by
  funext τ i j
  simp only [scaleCLM_apply, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.1]
  · simp

theorem prod_toList_get {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ)
    (h : ∀ i : Fin (Finsupp.toMultiset m).card, (i : ℕ) < (Finsupp.toMultiset m).toList.length) :
    (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩)) =
      m.prod fun k e => g k ^ e := by
  have hl : (Finsupp.toMultiset m).card = (Finsupp.toMultiset m).toList.length := (Multiset.length_toList _).symm
  calc (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩))
      = ∏ i : Fin (Finsupp.toMultiset m).toList.length, g ((Finsupp.toMultiset m).toList.get i) :=
        Fin.prod_congr' (fun i => g ((Finsupp.toMultiset m).toList.get i)) hl
    _ = ((Finsupp.toMultiset m).toList.map g).prod := Fin.prod_univ_fun_getElem _ g
    _ = (Multiset.map g (Finsupp.toMultiset m)).prod := by
        conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
        rw [Multiset.map_coe, Multiset.prod_coe]
    _ = m.prod fun k e => g k ^ e := by
        rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
          Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem taylor_scale {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) α =
      (α.prod fun k e => c k.1 ^ e) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  have hfun : (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) = G ∘ scaleCLM c := rfl
  have hGc : ContDiff ℂ ⊤ G := (GlobalTheory.SCV.analyticOnNhd_of_differentiable hG Set.univ).contDiff
  rw [Formalism.MainNotions.TaylorLogMetric.taylor, Formalism.MainNotions.TaylorLogMetric.taylor, hfun,
    (scaleCLM c).iteratedFDeriv_comp_right hGc 0 le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  simp only [scaleCLM_coordV]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_div_assoc]
  congr 1
  exact prod_toList_get α (fun k => c k.1) _

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

def placeWt (D : D7) (a d : ℕ) : Formalism.MainNotions.GL3Theta.Idx D a d → D.what₂.Tau → ℕ := fun k => Pi.single k.1 1

theorem prod_eq_prod_weight {D : D7} {a d : ℕ} (f : D.what₂.Tau → ℂ) (v : Formalism.MainNotions.GL3Theta.Idx D a d →₀ ℕ) :
    (v.prod fun k e => f k.1 ^ e) = ∏ τ, f τ ^ Finsupp.weight (placeWt D a d) v τ := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single k.1]
  · simp [placeWt]
  · intro τ _ hτ
    simp [placeWt, hτ]
  · simp

theorem minorPol_isWeightedHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (t : Tup D a d n) :
    (minorPol D t).IsWeightedHomogeneous (placeWt D a d) (fun τ => a * n τ) := by
  have hdet : ∀ τ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, (t τ j).1 i, i') :
      MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det.IsWeightedHomogeneous (placeWt D a d) (a • Pi.single τ 1) := by
    intro τ j
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun i => (MvPolynomial.X (τ, (t τ j).1 (σ i), i) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ))
      (fun _ => (Pi.single τ 1 : D.what₂.Tau → ℕ))
      (fun i _ => MvPolynomial.isWeightedHomogeneous_X ℂ (placeWt D a d) (τ, (t τ j).1 (σ i), i))
    simpa using this
  have h := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun τ _ =>
    MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun j _ => hdet τ j
  have hdeg : (fun τ => a * n τ) = ∑ τ, ∑ _j : Fin (n τ), a • (Pi.single τ 1 : D.what₂.Tau → ℕ) := by
    funext τ'
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hdeg]
  exact h

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

theorem fock_minorPol_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ (n : D.what₂.Tau → ℕ) (t : Tup D a d n),
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f
        (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hT.symm k.2.1, Fin.cast hS.symm k.2.2) : FVar D T.rank S.rank))
          (minorPol D t)) 0 =
      (∏ τ, period D δ r τ ^ (a * n τ)) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D t) G := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hG hR n t
  subst hS hT
  have hren : MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D S.rank T.rank =>
      ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : FVar D T.rank S.rank)) (minorPol D t) = minorPol D t :=
    MvPolynomial.rename_id_apply _
  rw [hren]
  obtain ⟨hstd, hinf, hgS, hgT, hcrv, hsc⟩ := hs
  have hrd := (reads_iff hcrv hsc G f).1 hR
  have hΦ : Differentiable ℂ (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) :=
    hG.comp (scaleCLM (fun τ => δ * embT D τ r)).differentiable
  have hfr : ∀ m, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin m) D.host.E) = fun _ => 1 := fun m =>
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  have hon : ∀ V : HSp D, V.gram = 1 →
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 * V.gram *
        (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    simp [Formalism.UG.cT, hV]
  have hmono := GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ S T 1 1 hstd hinf (hon S hgS) (hon T hgT) f _ hΦ hrd.2
  rw [hfr, hfr] at hmono
  set P := minorPol D t with hPdef
  have hP : P = ∑ v ∈ P.support, MvPolynomial.coeff v P • MvPolynomial.monomial v (1 : ℂ) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    exact Finset.sum_congr rfl fun v _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [hP, map_sum, Finset.sum_apply]
  rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hmono v]
  have happ : Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial v 1)
      (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) =
      (v.prod fun _ e => (e.factorial : ℂ)) *
        Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) v := by
    rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.sum_subset MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
    intro x _ hx
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul, zero_mul]
  rw [happ, taylor_scale (fun τ => δ * embT D τ r) G hG v]
  have hw : Finsupp.weight (placeWt D S.rank T.rank) v = fun τ => S.rank * n τ :=
    minorPol_isWeightedHomogeneous t (MvPolynomial.mem_support_iff.1 hv)
  have hper : (∏ τ, period D δ r τ ^ (S.rank * n τ)) =
      (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (v.sum fun _ e => e) *
        v.prod fun k e => (δ * embT D k.1 r) ^ e := by
    rw [← Finset.prod_congr rfl fun τ _ => congrArg (period D δ r τ ^ ·) (congrFun hw τ),
      ← prod_eq_prod_weight]
    simp only [period, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← mul_pow,
      div_eq_mul_inv]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [hper]
  ring

end GlobalTheory.NormExact
