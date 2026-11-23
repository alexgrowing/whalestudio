import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionPeriodicNormFiniteSqIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.MovedKappaNorm

section Mean
open MeasureTheory
open scoped Pointwise

theorem mean_eq_of_swap {G V : Type} [AddCommGroup G] [TopologicalSpace G] [ContinuousAdd G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure G) (𝓕 : Set G) (h𝓕 : μ 𝓕 = 1) (ν : Measure V) (Fd : Set V) (h0 : ν Fd ≠ 0) (ht : ν Fd ≠ ⊤)
    (g : G → ℝ) (hg : Continuous g) (M : ℝ) (hM : ∀ w, ‖g w‖ ≤ M) (ι : V → G) (hι : Continuous ι) (c m : ℝ)
    (h1 : ∀ x, ∫ w in 𝓕, g (w + x) ∂μ = c) (h2 : ∀ w, ⨍ z in Fd, g (w + ι z) ∂ν = m) : m = c := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h𝓕]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict Fd) := ⟨by rw [Measure.restrict_apply_univ]; exact ht.lt_top⟩
  have hc : Continuous (Function.uncurry fun (w : G) (z : V) => g (w + ι z)) :=
    hg.comp (continuous_fst.add (hι.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun (w : G) (z : V) => g (w + ι z)) ((μ.restrict 𝓕).prod (ν.restrict Fd)) :=
    Integrable.of_bound hc.measurable.aestronglyMeasurable M (Filter.Eventually.of_forall fun p => hM _)
  have hs := integral_integral_swap hint
  have hr : ν.real Fd ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, ht⟩
  have h3 : ∀ w, ∫ z in Fd, g (w + ι z) ∂ν = ν.real Fd * m := fun w => by
    rw [← h2 w, setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  simp only [h1, h3, setIntegral_const, smul_eq_mul] at hs
  rw [show μ.real 𝓕 = 1 by rw [measureReal_def, h𝓕, ENNReal.toReal_one], one_mul] at hs
  exact mul_left_cancel₀ hr hs

theorem setIntegral_shift {D : D7} {S T : HSp D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h : IsCovolOne (ratL T S) μ 𝓕)
    (φ : WO S T → ℝ) (hφ : ∀ γ ∈ ratL T S, ∀ a, φ (γ + a) = φ a) (b : WO S T) :
    ∫ a in 𝓕, φ (a + b) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, h𝓨, -⟩ := h
  have e1 : ∫ a in 𝓕, φ (a + b) ∂μ = ∫ a in b +ᵥ 𝓕, φ a ∂μ := by
    rw [← Set.image_vadd]
    simp only [vadd_eq_add]
    rw [(measurePreserving_add_left μ b).setIntegral_image_emb (MeasurableEquiv.addLeft b).measurableEmbedding]
    simp only [add_comm b]
  rw [e1]
  exact (h𝓨.vadd_of_comm b).setIntegral_eq h𝓨 fun γ a => hφ γ γ.2 a

theorem vol_fd {D : D7} {δ : ℂ} (hC : Crv D D.host.ccK δ) {N N' : ℕ} {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D D.host.ccK δ) A) :
    volume (Classical.epsilon (fun Fd : Set (VC D N N') => IsAddFundamentalDomain A Fd volume)) ≠ 0 ∧
    volume (Classical.epsilon (fun Fd : Set (VC D N N') => IsAddFundamentalDomain A Fd volume)) ≠ ⊤ := by
  obtain ⟨f₁, s₁, d₁, -⟩ := GlobalTheory.ThetaInter.klat_facts hC hA
  have hH := GlobalTheory.ThetaInter.isHerm_sesqOf D (tor0 D D.host.ccK δ) N N'
  have : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (VC D N N')).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨n, b, hb⟩ := GlobalTheory.ThetaInter.exists_basis (GlobalTheory.ThetaInter.discrete_of_selfDual hH d₁ f₁) s₁
  subst hb
  have h1 := ZSpan.isAddFundamentalDomain' b (volume : Measure (VC D N N'))
  have h2 := Classical.epsilon_spec
    (p := fun Fd => IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup Fd (volume : Measure (VC D N N'))) ⟨_, h1⟩
  rw [h2.measure_eq h1]
  exact ⟨ZSpan.measure_fundamentalDomain_ne_zero b, (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne⟩

theorem normSq_real_form {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {δ : ℂ} (hC : Crv D D.host.ccK δ) (hδ : δ ≠ 0) {A : AddSubgroup (VC D S.rank T.rank)}
    (hA : KLat D (tor0 D D.host.ccK δ) A) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) (hn : nrm2 μ 𝓕 f = 1)
    (Φ : VC D S.rank T.rank → ℂ)
    (hreal : ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w))
    (hTh : (fun Y => Φ (δ⁻¹ • Y)) ∈ ThSp D (tor0 D D.host.ccK δ) A) :
    normSq D (tor0 D D.host.ccK δ) A (fun Y => Φ (δ⁻¹ • Y)) = 1 := by
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hH := GlobalTheory.ThetaInter.isHerm_sesqOf D (tor0 D D.host.ccK δ) S.rank T.rank
  set Θ : VC D S.rank T.rank → ℂ := fun Y => Φ (δ⁻¹ • Y) with hΘ
  set ι : VC D S.rank T.rank → WO S T := fun Y =>
    GlobalTheory.FockCompare.iotaW σ T S (GlobalTheory.FockPos.frLin frS frT (δ⁻¹ • Y)) with hι
  have hιc : Continuous ι :=
    (hch.continuous_iota T S).comp ((GlobalTheory.FockPos.frLin frS frT).continuous.comp (continuous_const_smul _))
  have hιadd : ∀ Y Z, ι (Y + Z) = ι Y + ι Z := fun Y Z => by
    simp only [hι, smul_add, map_add]
  have hzι : ∀ Y, GlobalTheory.FockPos.zCo θ frS frT (ι Y) = δ⁻¹ • Y := fun Y => by
    rw [hι]
    dsimp only
    rw [GlobalTheory.ThetaLawOF.zCo_iota hch]
    funext τ
    exact GlobalTheory.ThetaLawOF.coord_back frS frT _ τ
  have hιz : ∀ r : WO S T, r.map (finPart D) = 0 → ι (δ • GlobalTheory.FockPos.zCo θ frS frT r) = r := fun r hr => by
    have e1 : GlobalTheory.FockPos.frLin frS frT (GlobalTheory.FockPos.zCo θ frS frT r) = GlobalTheory.FockCompare.piW θ T S r := by
      funext τ
      rw [GlobalTheory.FockPos.frLin_apply]
      change GlobalTheory.FockPos.frAt frT τ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * compAt θ τ r * GlobalTheory.FockPos.frAt frS τ) *
        (GlobalTheory.FockPos.frAt frS τ)⁻¹ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (GlobalTheory.ThetaLawOF.frAt_inv frT τ).2, Matrix.one_mul, Matrix.mul_assoc,
        (GlobalTheory.ThetaLawOF.frAt_inv frS τ).2, Matrix.mul_one]
      rfl
    rw [hι]
    dsimp only
    rw [smul_smul, inv_mul_cancel₀ hδ, one_smul, e1, hch.iota_pi hr]
  have hrho : ∀ Y, ‖f (ι Y)‖ ^ 2 = GlobalTheory.ThetaInter.rho (GlobalTheory.ThetaInter.sesqOf D (tor0 D D.host.ccK δ) S.rank T.rank) Θ Y := by
    intro Y
    obtain ⟨Z, rfl⟩ : ∃ Z, Y = δ • Z := ⟨δ⁻¹ • Y, by rw [smul_smul, mul_inv_cancel₀ hδ, one_smul]⟩
    rw [hreal _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO]
    change ‖_ * Φ (GlobalTheory.FockPos.zCo θ frS frT (ι (δ • Z)))‖ ^ 2 =
      ‖Φ (δ⁻¹ • δ • Z)‖ ^ 2 * Real.exp (-Real.pi * (Hf D (tor0 D D.host.ccK δ) (δ • Z) (δ • Z)).re)
    have hz := hzι (δ • Z)
    simp only [hι] at hz ⊢
    rw [hz, GlobalTheory.ThetaLawOF.torusHermitianForm_scaled_coordinate_eq hδ, smul_smul, inv_mul_cancel₀ hδ, one_smul, norm_mul, mul_pow, mul_comm,
      Complex.norm_exp, ← Real.exp_nat_mul]
    congr 2
    simp only [Complex.mul_conj']
    norm_cast
    push_cast
    ring
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hper := (GlobalTheory.ThetaSqInt.thetaO_norm_fin D ψ hψ S T μ 𝓕 hμ f hf).1
  obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  obtain ⟨v0, vt⟩ := vol_fd hC hA
  have huni := (GlobalTheory.theta_translation_intertwiner_unitary D D.host.ccK δ hC S.rank T.rank A A hA hA Θ hTh).1
  refine mean_eq_of_swap μ 𝓕 hμ.2.2 volume _ v0 vt (fun w => ‖f w‖ ^ 2) (hf.cont.norm.pow 2) (M ^ 2)
    (fun w => by rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hM w) 2) ι hιc 1 _ (fun x => ?_)
    (fun w => ?_)
  · rw [setIntegral_shift hμ (fun w => ‖f w‖ ^ 2) (fun γ hγ a => by simp only [hper γ hγ a]) x]
    exact hn
  · obtain ⟨γ, u, huU, hu0, r, hr0, rfl⟩ := GlobalTheory.VacNonzeroReal.decomp_WO U hUo w
    rw [← huni (δ • GlobalTheory.FockPos.zCo θ frS frT r)]
    change _ = ⨍ z in _, GlobalTheory.ThetaInter.rho (GlobalTheory.ThetaInter.sesqOf D (tor0 D D.host.ccK δ) S.rank T.rank)
      (Formalism.L2.Th1.H.opU (GlobalTheory.ThetaInter.sesqOf D (tor0 D D.host.ccK δ) S.rank T.rank) (δ • GlobalTheory.FockPos.zCo θ frS frT r) Θ) z
    congr 1
    funext z
    rw [GlobalTheory.ThetaInter.rho_opU hH, ← hrho, hιadd, hιz r hr0, add_assoc, add_assoc, hper (ratW T S γ) ⟨γ, rfl⟩]
    have h2 := congrArg (fun F => ‖F (ι z + r)‖) (hU u huU hu0)
    simp only [heisO, norm_mul, hψ1, one_mul] at h2
    rw [← h2]
    congr 3
    abel

end Mean

theorem inV_stdL {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    GlobalTheory.MovedDict.inV B (Formalism.MainNotions.StandardLatticesGL3.stdL D n) = (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) := by
  have hc := GlobalTheory.ColStd.colLat_comap_eq_stdLat B
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.L2.Pj.stdLat D.host.E n := hy
    rw [← hc] at hy'
    exact hy'
  · intro hx
    refine ⟨(B⁻¹ : GL (Fin n) D.host.E).1.mulVec x, ?_, ?_⟩
    · show _ ∈ Formalism.L2.Pj.stdLat D.host.E n
      rw [← hc, Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]
      exact hx
    · simp only [Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]

theorem scal_eq {D : D7} {N N' : ℕ} {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) (hG0 : G ≠ 0)
    (P : (GL3Theta.Idx D N N' →₀ ℕ) → ℂ) (hP : ∀ k, P k ≠ 0) {a b : ℂ}
    (h : ∀ k, a * (P k * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G) =
      b * (P k * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G)) : a = b := by
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D hG hG0
  have hJ : GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G ≠ 0 := by
    rw [GlobalTheory.FockPos.applyAt0_monomial']
    exact mul_ne_zero (Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)) hα
  exact mul_right_cancel₀ (mul_ne_zero (hP α) hJ) (h α)

theorem normSq_intertwiner_image_vacuum_selfDual {D : D7} {δ t0 : ℂ} (hC : Crv D D.host.ccK δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0)
    {N N' : ℕ} {e0 : VC D N N' → ℂ} (he0 : oddE0 D D.host.ccK δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    normSq D (tor0 D D.host.ccK δ) (La D (tor0 D D.host.ccK δ) L L')
      (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (La D (tor0 D D.host.ccK δ) L L') e0) =
      normSq D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') e0 ∧
    normSq D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') e0 ≠ 0 := by
  have k0 : KLat D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') :=
    Or.inr ⟨_, _, GlobalTheory.MovedVacuum.sd_stdL D N, GlobalTheory.MovedVacuum.sd_stdL D N', rfl⟩
  have k1 : KLat D (tor0 D D.host.ccK δ) (La D (tor0 D D.host.ccK δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  refine ⟨(GlobalTheory.theta_translation_intertwiner_unitary D D.host.ccK δ hC N N' _ _ k0 k1 e0 he0.1).2.2.1, ?_⟩
  rw [he0.2.2.1]
  exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 D.host.ccK δ t0 hC ht)

theorem normSq_scalar {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {δ t0 : ℂ} (hC : Crv D D.host.ccK δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0)
    {e0 : VC D S.rank T.rank → ℂ} (he0 : oddE0 D D.host.ccK δ t0 S.rank T.rank e0)
    {Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hLs : SD D Ls) (hLt : SD D Lt) (f : WO S T → ℂ)
    (hf : IsVacO ψ θ S T sS sT (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f) (a : ℂ)
    (ha : ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        a * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1)
          (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) S.rank T.rank) (La D (tor0 D D.host.ccK δ) Ls Lt) e0))) :
    ‖a‖ ^ 2 * normSq D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) S.rank T.rank) e0 = 1 := by
  have hδ : δ ≠ 0 := GlobalTheory.InertSign.delta_ne_zero hC
  obtain ⟨Θ', hΘ', hΘ0', hjet'⟩ := GlobalTheory.MovedKappa.fock_jets_moved ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ Ls Lt hLs hLt f hf
  obtain ⟨κ', hκ', hd⟩ := GlobalTheory.MovedKappa.intertwining_mem_ne_zero hC ht he0 hLs hLt hΘ' hΘ0'
  have hF0 : Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) S.rank T.rank) (La D (tor0 D D.host.ccK δ) Ls Lt) e0 ≠ 0 := by
    intro h
    apply hΘ0'
    rw [hκ', h]
    funext z
    simp
  have hsS := GlobalTheory.FockPos.cart_one frS hS hcS
  have hsT := GlobalTheory.FockPos.cart_one frT hT hcT
  subst hsS hsT
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
  have hTh := GlobalTheory.T.unitVacuumEntireFactor_isTheta_movedLattices ψ θ S T frS frT hS hT δ hC hδ Ls Lt hLs hLt f hf Φ hΦd hreal
  obtain ⟨⟨μ, 𝓕⟩, hμ⟩ := hf.2.norm.1
  have k1 : KLat D (tor0 D D.host.ccK δ) (La D (tor0 D D.host.ccK δ) Ls Lt) := Or.inr ⟨_, _, hLs, hLt, rfl⟩
  have hN := normSq_real_form ψ θ S T frS frT hf.1 hf.2.inf hC hδ k1 f hf.2.theta hμ (hf.2.norm.2 (μ, 𝓕) hμ) Φ hreal hTh
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hTh hN
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hΘ0 : Θ ≠ 0 := by
    intro h0
    rw [h0] at hN
    simp [Formalism.MainNotions.TaylorLogMetric.normSq] at hN
  have hjet : ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
    intro k
    have hdiff : Differentiable ℂ Θ := hTh.1
    have hj := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hf.2.inf hS hT f Φ hΦd hreal k
    change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f
      (MvPolynomial.monomial k 1) 0 = _
    rw [hj, hΦeq, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial',
      GlobalTheory.FockPos.taylor_comp_smul' D _ hdiff]
    have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ =
        δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
      intro τ
      rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
    have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
        (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
      simp only [hper, Finsupp.prod, Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprod, mul_pow]
    ring
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.MovedKappa.intertwining_mem_ne_zero hC ht he0 hLs hLt hTh hΘ0
  have hak : a = κ := by
    refine scal_eq hd hF0 (fun k => k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n)
      (fun k => Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero hδ v.1)) fun k => ?_
    rw [← ha k, hjet k, hκ, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd]
    ring
  rw [hκ, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.normSq_const_mul, (normSq_intertwiner_image_vacuum_selfDual hC ht he0 hLs hLt).1, ← hak] at hN
  exact hN

theorem iop_self {D : D7} {δ t0 : ℂ} (hC : Crv D D.host.ccK δ) {N N' : ℕ} {e0 : VC D N N' → ℂ}
    (he0 : oddE0 D D.host.ccK δ t0 N N' e0) :
    Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
      (La D (tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) e0 = e0 :=
  (GlobalTheory.ThetaTriple.klat_triples D D.host.ccK δ hC N N').2.2.1 _
    (Or.inr ⟨_, _, GlobalTheory.MovedVacuum.sd_stdL D N, GlobalTheory.MovedVacuum.sd_stdL D N', rfl⟩) e0 he0.1

theorem norm_eq_one_of_sq {c κ : ℂ} {n : ℝ} (h1 : ‖c‖ ^ 2 * n = 1) (h2 : ‖c * κ‖ ^ 2 * n = 1) : ‖κ‖ = 1 := by
  have h3 : ‖κ‖ ^ 2 = 1 := by
    rw [norm_mul, mul_pow] at h2
    linear_combination h2 - ‖κ‖ ^ 2 * h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg κ) two_ne_zero).1 h3

theorem norm_kappa : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ → ‖κ‖ = 1 := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hκ
  have hC := ch.S.Z.crv
  have he0 := ch.S.Z.e0_is p hp
  have hsd := GlobalTheory.T.lattices_self_dual_moved_pair hP hI ch hch p hp x y
  have hvac := GlobalTheory.T.vacuum_vector_moved_pair hP hI ch hch p hp x y
  have hvac0 := ch.S.Z.vac_is p hp
  have hc0 := ch.S.Z.kernelNorm_constant_spec p hp
  have hd := GlobalTheory.MovedDict.Entire.differentiable_intertwining_moved hP hI ch hch p hp x y
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have h2 := fun f k => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std ch.W.θ_is k 0
    have key := fun Ls Lt => @normSq_scalar D ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.fr (.grid (i + 1) D.R.m)) (ch.S.N.fr (.grid i D.R.m))
      (ch.S.N.fr_on _ ⟨hi, rfl⟩) (ch.S.N.fr_on _ ⟨by omega, rfl⟩)
      (ch.W.cart_is _ ⟨hi, le_rfl⟩) (ch.W.cart_is _ ⟨by omega, le_rfl⟩) _ _ hC ch.S.Z.pt0 _ he0 Ls Lt
    have hconj := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac
    have hconj0 := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac0
    refine norm_eq_one_of_sq (c := starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ))
      (key _ _ (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) _ (by rw [inV_stdL, inV_stdL]; exact hconj0) _
        fun k => ?_) (key _ _ hsd.1 hsd.2 _ hconj _ fun k => ?_)
    · rw [iop_self hC he0]
      have h := congrArg (starRingEnd ℂ) ((h2 _ k).symm.trans (hc0 k))
      rw [Complex.conj_conj, map_mul] at h
      refine h.trans ?_
      show _ * starRingEnd ℂ (starRingEnd ℂ _) = _
      rw [Complex.conj_conj]
    · have h := congrArg (starRingEnd ℂ) ((h2 _ k).symm.trans (hκ k))
      rw [Complex.conj_conj, map_mul, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd] at h
      refine h.trans ?_
      show _ * starRingEnd ℂ (starRingEnd ℂ _) = _
      rw [Complex.conj_conj, mul_left_comm _ κ, mul_assoc]
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1 : j + 1 ≤ D.R.m := hp
    have key := fun Ls Lt => @normSq_scalar D ch.W.ψ ch.W.θ (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))
      (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) (ch.S.N.fr (.top j)) (ch.S.N.fr (.top (j + 1)))
      (ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)) (ch.S.N.fr_on (.top (j + 1)) hj1)
      (ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)) (ch.W.cart_is (.top (j + 1)) hj1) _ _ hC ch.S.Z.pt0 _ he0 Ls Lt
    refine norm_eq_one_of_sq (c := (ch.S.Z.c0 (.top t j) : ℂ))
      (key _ _ (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) _ (by rw [inV_stdL, inV_stdL]; exact hvac0) _
        fun k => ?_) (key _ _ hsd.1 hsd.2 _ hvac _ fun k => ?_)
    · rw [iop_self hC he0]
      exact hc0 k
    · have h := hκ k
      rw [GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd] at h
      refine h.trans ?_
      show _ * RingHom.id ℂ _ = _
      rw [RingHom.id_apply, mul_left_comm _ κ, mul_assoc]

end GlobalTheory.MovedKappaNorm
