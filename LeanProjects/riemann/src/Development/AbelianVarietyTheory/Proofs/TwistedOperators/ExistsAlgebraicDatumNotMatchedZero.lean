import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZeroStatement

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem tprod_ne_zero_of_ne {κ : Type} [Fintype κ] {V : κ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {v : ∀ j, V j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem tmul_ne_zero_of_ne {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} {y : Q}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h0
  have := congrArg ((TensorProduct.rid ℂ P).toLinearMap ∘ₗ LinearMap.lTensor P l) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero, hl,
    one_smul] at this
  exact hx this

theorem pure_neg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (-f) φ = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, neg_mul]

theorem exists_not_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ¬ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  classical
  haveI := hM.real.nontriv
  obtain ⟨y, hy⟩ := exists_ne (0 : R.Pi)
  obtain ⟨f, hfP, hfy⟩ : ∃ f ∈ G.M.Pol Bs.ψ Bs.emb, R.p f = y := by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    exact Submodule.mem_map.1 this
  have hloc : ∀ v, ∃ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Rf.p v φ ≠ 0 := fun v => by
    haveI := hM.fin.nontriv v
    obtain ⟨z, hz⟩ := exists_ne (0 : Rf.Pi v)
    have : z ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := (hM.fin.onto v) ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 this
    exact ⟨φ, hφ, hz⟩
  choose ψ0 hψ0 hψ0ne using hloc
  have hvac := hM.triple.geo.hM.vac
  let φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun v => if v ∈ Xc.T then ψ0 v else G.M.vac v
  have hφSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _ := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0 v
    · simp only [φ, h, if_false]; exact (hvac v).1
  have hφout : ∀ v ∉ Xc.T, φ v = G.M.vac v := fun v h => by simp [φ, h]
  have hφne : ∀ v, Rf.p v (φ v) ≠ 0 := fun v => by
    by_cases h : v ∈ Xc.T
    · simp only [φ, h, if_true]; exact hψ0ne v
    · simp only [φ, h, if_false]; exact (hM.fin.sph v h).2
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, ?_, ?_⟩
  · have := sum_pure_mem_algD G.M Bs.ψ Bs.emb Xc.T (m := 1) (fun _ => f) (fun _ => φ) (fun _ => ⟨hfP, hφSB, hφout⟩)
    simpa using this
  · rintro ⟨T, hT, m, f', φ', hf', hΦ, hsum⟩
    let g : Fin (m + 1) → SInf F (Fin a × Fin (a + a')) := Fin.cons (-f) f'
    let χ : Fin (m + 1) → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := Fin.cons φ φ'
    have h0 : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (χ i) = 0 := by
      simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, pure_neg, ← hΦ, neg_add_cancel]
    have hout : ∀ i, ∀ v ∉ T, χ i v = G.M.vac v := by
      intro i v hv
      induction i using Fin.cases with
      | zero => exact hφout v (fun h => hv (hT h))
      | succ j => exact (hf' j).2.2 v hv
    have key := GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M.vac (fun v => (hvac v).2.1) hM.triple.geo.hM.std R.p Rf.Pi Rf.p T (m + 1) g χ hout h0
    simp only [Fin.sum_univ_succ, g, χ, Fin.cons_zero, Fin.cons_succ, map_neg, TensorProduct.neg_tmul, hsum, add_zero,
      neg_eq_zero] at key
    exact tmul_ne_zero_of_ne (hfy ▸ hy) (tprod_ne_zero_of_ne fun v : T => hφne v.1) key

end GlobalTheory.PolKer
