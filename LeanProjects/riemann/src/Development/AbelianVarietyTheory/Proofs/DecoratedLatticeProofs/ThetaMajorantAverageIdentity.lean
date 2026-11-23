import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTargetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.IkedaK

variable {D : D7}

theorem isCompact_Kmax (T : HSp D) (b : GL (Fin T.rank) (AE D)) : IsCompact (Kmax T b : Set (GA D T)) := by
  haveI := isLattice_frameLat_host T
  exact GlobalTheory.Doubling.isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _

theorem bdd_om_compact {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {P : Set (GA D S × GA D T)}
    (hP : IsCompact P) : ∃ C : ℝ, ∀ p ∈ P, ∀ x, ‖om p f x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW f hf
  obtain ⟨C, hC⟩ := (hP.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun p hp x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := (hW.om_pres p f hf).quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)) γ') = ratW T S γ' := rfl
  rw [e] at hx
  have h1 := hW.std.1.2.1 (-(symplOH S T (ratW T S γ') x))
  have := hC (p, ratW T S γ' + x) ⟨hp, hx⟩
  simp only at this
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem om_mul_apply {S T : HSp D} (om : WRep S T) (p q : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om q f) = om (p * q) f := by
  rw [map_mul]; rfl

theorem weilRepUnitaryPair_left_apply_right {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (g, 1) (om (1, k) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

theorem weilRepUnitaryPair_right_apply_left {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (1, k) (om (g, 1) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

theorem integrable_om_Kmax {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (b : GL (Fin T.rank) (AE D))
    (ν : Measure (Kmax T b)) [IsFiniteMeasure ν] (g : GA D S) (w : WO S T) :
    Integrable (fun k : Kmax T b => om (g, (k : GA D T)) f w) ν := by
  haveI : BorelSpace (GA D T) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := bdd_om_compact hW hf ((isCompact_singleton (x := g)).prod (isCompact_Kmax T b))
  have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW f hf
  have hk : Continuous fun k : Kmax T b => om (g, (k : GA D T)) f w :=
    hc.comp ((continuous_const.prodMk continuous_subtype_val).prodMk continuous_const)
  exact Integrable.mono' (integrable_const C) hk.aestronglyMeasurable
    (ae_of_all _ fun k => hC (g, (k : GA D T)) ⟨Set.mem_singleton g, k.2⟩ w)

theorem ikeda_projK_intertwine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (om' : WRep S T'), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T' χS χT om' → ∀ b : GL (Fin T.rank) (AE D), IsMaj T b → ∀ ν : Measure (Kmax T b), IsProbabilityMeasure ν → ∀ (μ₁ : Measure (Mx D t S.rank)) (𝓕₁ : Set (Mx D t S.rank)), IsCovolOne (ratMx D t S.rank) μ₁ 𝓕₁ → (∀ φ, IsThetaFunO ψ S T φ → IsThetaFunO ψ S T (projK om ν φ)) → (∀ φ, IsThetaFunO ψ S T φ → ∀ g, ikeda ψ d μ₁ 𝓕₁ (projK om ν (om (g, 1) φ)) = om' (g, 1) (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ))) ∧ ∀ (K : Subgroup (GA D S)) φ, IsThetaFunO ψ S T φ → IsKFinVec om K φ → IsKFinVec om' K (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ)) := by
  intro D ψ S T T' t d χS χT om om' hW hW' b hb ν hν μ₁ 𝓕₁ hcov hP
  haveI : BorelSpace (GA D T) := ⟨rfl⟩
  haveI : SecondCountableTopology (GA D T) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T).2.1
  have hKc := isCompact_Kmax T b
  have hcomm : ∀ φ, IsThetaFunO ψ S T φ → ∀ g, projK om ν (om (g, 1) φ) = om (g, 1) (projK om ν φ) := by
    intro φ hφ g
    funext x
    have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW φ hφ
    obtain ⟨C1, hC1⟩ := bdd_om_compact hW hφ ((isCompact_singleton (x := (1 : GA D S))).prod hKc)
    obtain ⟨C2, hC2⟩ := bdd_om_compact hW hφ ((isCompact_singleton (x := g)).prod hKc)
    have hF2 : (fun q : Kmax T b × WO S T => om (g, 1) (om (1, (q.1 : GA D T)) φ) q.2) =
        fun q => om (g, (q.1 : GA D T)) φ q.2 := by
      funext q; rw [weilRepUnitaryPair_left_apply_right]
    have key := GlobalTheory.CommIntBdd.om_integral_comm_bdd D ψ S T χS χT om hW (Kmax T b) ν
      (fun k : Kmax T b => om (1, (k : GA D T)) φ) (g, 1)
      (fun k => hW.om_pres _ φ hφ)
      (hc.comp ((continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))
      ⟨C1, fun k y => hC1 (1, (k : GA D T)) ⟨Set.mem_singleton _, k.2⟩ y⟩
      (by rw [hF2]; exact hc.comp ((continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd))
      ⟨C2, fun k y => by rw [weilRepUnitaryPair_left_apply_right]; exact hC2 (g, (k : GA D T)) ⟨Set.mem_singleton _, k.2⟩ y⟩
      (hP φ hφ) x
    refine Eq.trans ?_ key.symm
    show ∫ k, om (1, (k : GA D T)) (om (g, 1) φ) x ∂ν = ∫ k, om (g, 1) (om (1, (k : GA D T)) φ) x ∂ν
    simp only [weilRepUnitaryPair_left_apply_right, weilRepUnitaryPair_right_apply_left]
  have hmix := GlobalTheory.T.mixedModelFormulas_wittTarget D ψ S T T' t d χS χT om om' hW hW' μ₁ 𝓕₁ hcov
  have cl1 : ∀ φ, IsThetaFunO ψ S T φ → ∀ g, ikeda ψ d μ₁ 𝓕₁ (projK om ν (om (g, 1) φ)) =
      om' (g, 1) (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ)) := by
    intro φ hφ g
    rw [hcomm φ hφ g]
    have := (hmix _ (hP φ hφ)).source g 0
    rw [Matrix.mul_zero] at this
    exact this
  refine ⟨cl1, fun K φ hφ hfin => ?_⟩
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f}
      add_mem' := fun hf hg => Formalism.IndefR.Fock.CCR.theta_add hf hg
      zero_mem' := Formalism.IndefR.Fock.CCR.theta_zero ψ S T
      smul_mem' := fun c _ hf => Formalism.IndefR.Fock.CCR.theta_smul hf c }
  have hPadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      projK om ν (f + g) = projK om ν f + projK om ν g := by
    intro f g hf hg
    funext w
    simp only [projK, map_add, Pi.add_apply]
    exact integral_add (integrable_om_Kmax hW hf b ν 1 w) (integrable_om_Kmax hW hg b ν 1 w)
  have hPsmul : ∀ (c : ℂ) f, projK om ν (c • f) = c • projK om ν f := by
    intro c f
    funext w
    simp only [projK, map_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  have hIadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      ikeda ψ d μ₁ 𝓕₁ (f + g) = ikeda ψ d μ₁ 𝓕₁ f + ikeda ψ d μ₁ 𝓕₁ g := by
    intro f g hf hg
    funext w
    have h1 := d.integrableOn_mixT hW.std.1.1 hcov hf 0 w
    have h2 := d.integrableOn_mixT hW.std.1.1 hcov hg 0 w
    simp only [ikeda, HypDec.mixT, HypDec.integrandT_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
    exact integral_add h1 h2
  have hIsmul : ∀ (c : ℂ) f, ikeda ψ d μ₁ 𝓕₁ (c • f) = c • ikeda ψ d μ₁ 𝓕₁ f := by
    intro c f
    funext w
    simp only [ikeda, HypDec.mixT, HypDec.integrandT_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      integral_const_mul]
  let L : Θ →ₗ[ℂ] (WO S T' → ℂ) :=
    { toFun := fun f => ikeda ψ d μ₁ 𝓕₁ (projK om ν f.1)
      map_add' := fun f g => by
        simp only [Submodule.coe_add]
        rw [hPadd _ _ f.2 g.2, hIadd _ _ (hP _ f.2) (hP _ g.2)]
      map_smul' := fun c f => by
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [hPsmul, hIsmul] }
  set V := Submodule.span ℂ {f : WO S T → ℂ | ∃ k ∈ K, f = om (k, 1) φ} with hV
  have hle : V ≤ Θ := Submodule.span_le.2 (by rintro f ⟨k, -, rfl⟩; exact hW.om_pres _ φ hφ)
  haveI : FiniteDimensional ℂ V := hfin
  let V' := Submodule.comap Θ.subtype V
  have e : V' ≃ₗ[ℂ] V := (Submodule.equivMapOfInjective Θ.subtype Subtype.val_injective V').trans
    (LinearEquiv.ofEq _ _ (by rw [Submodule.map_comap_subtype, inf_eq_right.2 hle]))
  haveI : FiniteDimensional ℂ V' := LinearEquiv.finiteDimensional e.symm
  show FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ k ∈ K, f = om' (k, 1) (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ))})
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ : _ ≤ V'.map L)
  rintro f ⟨k, hk, rfl⟩
  refine ⟨⟨om (k, 1) φ, hW.om_pres _ φ hφ⟩, Submodule.subset_span ⟨k, hk, rfl⟩, ?_⟩
  exact cl1 φ hφ k

end GlobalTheory.IkedaK
