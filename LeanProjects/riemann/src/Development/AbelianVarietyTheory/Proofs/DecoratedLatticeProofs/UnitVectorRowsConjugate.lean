import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslatedEvaluationRowsConjLinearBijectionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomHypothesisMatchingCentralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.LineV

open GlobalTheory.PiTensorInner

theorem tprod_eq_smul_of_prod_inner {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (a b : ∀ i, E i) (l : ℂ)
    (h : ∀ x : ∀ i, E i, ∏ i, ⟪a i, x i⟫_ℂ = l * ∏ i, ⟪b i, x i⟫_ℂ) :
    PiTensorProduct.tprod ℂ a = (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b := by
  set w := PiTensorProduct.tprod ℂ a - (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b with hw
  have hy : ∀ y, ipT y w = 0 := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [hw, map_smul, LinearMap.smul_apply, map_sub, map_smulₛₗ, ipT_tprod, ipT_tprod, h x]
      simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  by_contra hne
  have := ipT_pos w (sub_ne_zero.2 hne)
  rw [hy w] at this
  simp at this

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem eq_of_evS_ae {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {θ : InfFam D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))}
    {χ : GA D (D.sp.Y 0) → ℂ} (t : GA D (D.sp.Y 0)) {T T' : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)}
    (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (a b : M.Vec)
    (he : evS X h t (T (PiTensorProduct.tprod ℂ a)) =ᵐ[muX X] evS X h t (T' (PiTensorProduct.tprod ℂ b))) :
    T (PiTensorProduct.tprod ℂ a) = T' (PiTensorProduct.tprod ℂ b) := by
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  have hU' := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T').1 hT')
  have hva : (PiTensorProduct.lift.symm T : MMap M) a = T (PiTensorProduct.tprod ℂ a) := by
    simp [PiTensorProduct.lift_symm]
  have hvb : (PiTensorProduct.lift.symm T' : MMap M) b = T' (PiTensorProduct.tprod ℂ b) := by
    simp [PiTensorProduct.lift_symm]
  have hc := (hU.aut a).cont
  have hl := (hU.aut a).left
  have hc' := (hU'.aut b).cont
  have hl' := (hU'.aut b).left
  rw [← hva, ← hvb] at he ⊢
  generalize (PiTensorProduct.lift.symm T : MMap M) a = f at hc hl he ⊢
  generalize (PiTensorProduct.lift.symm T' : MMap M) b = f' at hc' hl' he ⊢
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => f (ι.symm x * t) - f' (ι.symm x * t)
  have hφc : Continuous φ := by
    have hm : Continuous fun x : X.B.I.GA => ι.symm x * t := ι.symm.continuous.mul continuous_const
    exact (hc.comp hm).sub (hc'.comp hm)
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    simp only [φ, map_mul, mul_assoc]
    rw [hl _ (hQ γ hγ), hl' _ (hQ γ hγ)]
  have hae : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have he' : evS X h t f =ᵐ[muX X] evS X h t f' := he
    filter_upwards [he'] with x hx
    simp only [φ, Pi.zero_apply, sub_eq_zero]
    exact hx
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae
  funext g
  have e := hz (ι (g * t⁻¹))
  simp only [φ, ContinuousMulEquiv.symm_apply_apply, inv_mul_cancel_right, sub_eq_zero] at e
  exact e

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem line_of_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ)
    {T T' : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (v₀ v : M.Vec)
    (h1 : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) (hT0 : T ≠ 0)
    (he : T (PiTensorProduct.tprod ℂ v₀) = T' (PiTensorProduct.tprod ℂ v)) :
    ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  obtain ⟨ν, 𝓖, hν, h𝓖⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  have hUm := (mem_multT θ M J χ T).1 hT
  have hUm' := (mem_multT θ M J χ T').1 hT'
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 hUm
  set U : MMap M := PiTensorProduct.lift.symm T with hUd
  set U' : MMap M := PiTensorProduct.lift.symm T' with hUd'
  have hval : ∀ x, U x = T (PiTensorProduct.tprod ℂ x) := fun x => by simp [U, PiTensorProduct.lift_symm]
  have hval' : ∀ x, U' x = T' (PiTensorProduct.tprod ℂ x) := fun x => by simp [U', PiTensorProduct.lift_symm]
  have hUv : U v₀ = U' v := by rw [hval, hval', he]
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ hz => by
    have h1τ := h1 τ
    rw [hz, norm_zero] at h1τ
    exact zero_ne_one h1τ
  have hU0 : U v₀ ≠ 0 := by
    intro hz
    apply hT0
    have h0 : U = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hU v₀ hne hz
    have : T = PiTensorProduct.lift U := (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, h0, map_zero]
  obtain ⟨c1, hc1⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U hUm U hUm
  obtain ⟨c2, hc2⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U' hUm' U hUm
  have hpos := GlobalTheory.SchurConst.re_pos_of_isMultIP M ν 𝓖 hν h𝓖 U hc1 v₀ (hU.aut v₀).cont (hU.aut v₀).left hU0
  have hc10 : c1 ≠ 0 := fun hz => by simp [hz] at hpos
  have key : ∀ x : M.Vec, ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = (c2 / c1) * ∏ τ, ⟪v τ, x τ⟫_ℂ := by
    intro x
    have e1 := (hc1 v₀ x).2
    have e2 := (hc2 v x).2
    rw [hUv, e2] at e1
    have e3 : ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = ∏ τ, ⟪(v₀ τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    have e4 : ∏ τ, ⟪v τ, x τ⟫_ℂ = ∏ τ, ⟪(v τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    rw [e3, e4, div_mul_eq_mul_div, eq_div_iff hc10, mul_comm, e1]
  have hl := tprod_eq_smul_of_prod_inner v₀ v _ key
  refine ⟨_, ?_, hl⟩
  intro hz
  rw [hz, zero_smul] at hl
  have hp := GlobalTheory.PiTensorInner.ipT_tprod v₀ v₀
  simp only [hl, map_zero] at hp
  have : ∏ τ, ⟪v₀ τ, v₀ τ⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖(v₀ τ : M.H τ)‖ : ℂ)) ^ 2 = 1
    rw [h1]; simp
  rw [this] at hp
  exact zero_ne_one hp

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop

theorem unit_vector_line_conjugate : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ ThetaLiftSpaceZero W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB v₀ v hv hn T hTm hT0 φ hφ hst
  obtain ⟨-, hθ, -, hM, -, -⟩ := GlobalTheory.T.bottom_hypothesis_matching_central W hB
  have hMt : Matches W.S.X W.Q.instEq (rJ W) (rChi W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
    have := hM 1 (one_mem _) (Subgroup.one_mem _)
    rwa [one_mul] at this
  obtain ⟨⟨j, hj, hjT⟩, -⟩ := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (rJ W) (rChi W)
    (show GA D (D.sp.Y 0) from W.Q.tS) v (by simp) hθ hB.gap hB.idE hMt hv
  obtain ⟨T', hT'⟩ := hj.2 ⟨star φ, hst⟩
  have h1 := hjT T'
  rw [hT'] at h1
  have he : evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX W.S.X]
      evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T'.1 (PiTensorProduct.tprod ℂ v)) := by
    filter_upwards [hφ, h1, Lp.coeFn_star φ] with x a1 a2 a3
    rw [← a1]
    have a4 := a3.symm.trans a2
    simpa using congrArg star a4
  exact LineV.line_of_eq hCR hθ hTm T'.2 v₀ v hn hT0 (LineV.eq_of_evS_ae W.S.X W.Q.instEq _ hTm T'.2 v₀ v he)

end GlobalTheory.MiTop
