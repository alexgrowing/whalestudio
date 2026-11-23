import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCuspHomOfCuspLowest
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMultMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadicalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCusp

theorem isCuspFun_iota (D : D7) (I : AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] [SigmaFinite μf] (ψ : I.GA → ℂ) (hc : Continuous ψ)
    (hi : ∀ γ ∈ I.GFset, ∀ y, ψ (γ * y) = ψ y) (hcusp : I.IsCuspFn (I.muA μf) ψ) :
    IsCuspFun (D.sp.Y 0) (fun g => ψ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) g)) := by
  subst h
  intro r C hC μ 𝓕 hμ h𝓕 g
  have : BorelSpace (GA D (D.sp.Y 0)) := ⟨rfl⟩
  have hW : (Formalism.IndefR.RationalEmbedding.inst D).IsIsot (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff _ _).2 ⟨r, C, hC, rfl⟩
  have key := (GlobalTheory.CuspCompare.constTerm_iff_inst (Formalism.IndefR.RationalEmbedding.inst D) μf
    (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ⟨(Formalism.IndefR.RationalEmbedding.iota D).continuous,
      (Formalism.IndefR.RationalEmbedding.iota D).symm.continuous⟩ (GQ (D.sp.Y 0)) (NI (D.sp.Y 0) C)
    (Formalism.IndefR.RationalEmbedding.iota_rat D) _ hW (GlobalTheory.T.mem_unipotentRadical_iff_iota_mem_adelicRadical D C hC) ψ hc hi).2 (hcusp _ hW) μ 𝓕 hμ h𝓕 g
  exact key

theorem conjMap_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c ht hConj hInt Φ hΦ hRep u
  change IsCuspFun (D.sp.Y 0) _
  obtain ⟨-, -, -, -, -, -, hSL⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hDS
  obtain ⟨hd, hl, hb, hh, hph, -⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨-, -, ⟨T0, hT0⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds X.B X.dv hd hph
  have hw := GlobalTheory.RowCusp.row_isCuspFn hSL X.B X.dv _ hd hg hh hl hb T0 hT0 Φ hΦ
  have hcH := GlobalTheory.RowLev.isCuspHom_of_cusp_lowest X.B X.ds (fun v => (X.low v).1) Φ hΦ hw
  obtain ⟨ψ, hψ⟩ := hRep u
  have he := (GlobalTheory.ExtContRep.ext_ae_eq_contRep X.B _ ψ hψ).1
  have hcψ : X.B.I.IsCuspFn (X.B.I.muA X.B.μf) ψ :=
    (GlobalTheory.IntertwMult.contRep_facts X.B.I X.B.μf X.B.fund X.B.R X.B.fund_spec X.B.R_spec _ ψ hψ.1 hψ.2.1
      (he.mono fun x hx => hx.symm)).2.1 (hcH _)
  have hY := isCuspFun_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hcψ
  set t' : GA D (D.sp.Y 0) := t with ht'
  have hfun : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u = fun y => star (ψ (iotaX X h (y * t'⁻¹))) := by
    funext y
    exact congrArg star (congrFun (GlobalTheory.ConjRowMult.contRepL_spec X hψ) _)
  rw [hfun]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have key := hY r C hC μ 𝓕 hμ h𝓕 (g * t'⁻¹)
  have e : ∀ n : NI (D.sp.Y 0) C, ((n : GA D (D.sp.Y 0)) * g * t'⁻¹) = (n : GA D (D.sp.Y 0)) * (g * t'⁻¹) :=
    fun n => mul_assoc _ _ _
  have hs : ∀ z : ℂ, star z = starRingEnd ℂ z := fun _ => rfl
  simp only [e, hs]
  rw [integral_conj]
  exact (congrArg (starRingEnd ℂ) key).trans (map_zero _)

end GlobalTheory.ConjCusp

end
