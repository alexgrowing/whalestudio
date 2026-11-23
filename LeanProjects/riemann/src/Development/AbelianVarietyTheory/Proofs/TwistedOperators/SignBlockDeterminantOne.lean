import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignaturesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantNeZeroOfMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantMulMaximalCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.ChainFr GlobalTheory.Chain.IoLift GlobalTheory.Chain.IoLift.FockOrbit GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec maxCpt)
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembers

theorem signBlockDeterminant_one {n : ℕ} (ε : Fin n → Bool) (e : Bool) : signBlockDeterminant ε e 1 = 1 := by
  unfold signBlockDeterminant
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : {a // ε a = e} → Fin n) Subtype.val = 1 from by
    ext x y; simp [Matrix.one_apply, Subtype.ext_iff]]
  exact Matrix.det_one

theorem fr_elt_one {D : D7} {V : HSp D} {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr V) (τ : D.what₂.Tau) :
    A.elt θ τ 1 = 1 := by
  rw [Fr.elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)), GlobalTheory.PointAtPlaceHom.atTau_one hθ]

theorem frame_fock_orbit : ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (A : GlobalTheory.ChainFr.Fr V) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → GlobalTheory.ChainFr.CompactFockF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), GlobalTheory.Chain.IoLift.IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (GlobalTheory.ChainFr.ptF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') f φ) = ∑ i, c i k • GlobalTheory.ChainFr.ptF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') f (φs i) := by
  intro D V W S' A M' θ ψ ω f τ aS aT hθ hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) :=
    pureTensorO ψ θ V W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f
  have hp : ptF ψ θ A (Fr.ofModel M') f = pt := rfl
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k =>
    signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (A.ε τ) (M'.ε τ) 1 (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [fr_elt_one hθ, signBlockDeterminant_one, signBlockDeterminant_one, _root_.one_zpow, _root_.one_zpow, one_mul, one_mul,
      Matrix.map_one _ (map_zero _) (map_one _), hp, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := (hz true).mul (hz false)
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      simp only [ρ, s, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, e,
        subst_one_mul τ (A.ε τ) (M'.ε τ) a.2 b.2, signBlockDeterminant_mul_maximalCompact _ a.2 b.2, mul_zpow]
      congr 1
      ring)
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  refine ⟨n, φs, c, h1, fun k => ?_⟩
  rw [hp, key, h2, map_sum]
  simp only [map_smul]

set_option maxHeartbeats 1000000 in

theorem lowVanishFock (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules)
    (h3 : GlobalTheory.Published.CuspRapidDecay) : ∀ D : D7, LowVanishFock D := by
  classical
  intro D
  obtain ⟨X, hX, -, h5, -, -, -, hAR⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis h1 h2
  have hTB := (GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra h1 h2 D).2
  intro k i V' W M' θ ψ hθ hP hi hs ω' hω ν 𝓕 hν h𝓕 J χ F hF v A f₀ hf P
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  by_cases f0 : f₀ = 0
  · subst f0
    funext g
    simp [Lift.liftInt, thetaKO, ptF_zero]

  have tgt : ∀ τ, ∃ a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ),
      kFin M' τ ≤ M'.sm τ ∧ IsKAct M' τ a' := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, -, e2⟩ := hP τ
    obtain ⟨-, -, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types _ al be ga de hd.1
    have ht := hd.1.1
    obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W _ M' τ (al.length + de.length + D.R.t) (ga.length + be.length) _ _
      (expS D k τ) ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, congrArg dualPar e2⟩
    obtain ⟨U', hU'⟩ := hU' e' he'
    obtain ⟨hsm, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W _ M' τ _ _ _ _ _ _ _ hU'
    exact ⟨a', hsm, ha'⟩
  choose a' hsm ha' using tgt
  have h' : KSm M' := hsm
  have hMF : IsMultMap θ M' J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hF)
  have hM : ∀ F' : MultT θ M' J χ, IsMultMap θ M' J χ (PiTensorProduct.lift.symm (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ))) :=
    fun F' => (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F'.2)
  let pt : PolF D W.rank V'.rank →ₗ[ℂ] (WO V' W → ℂ) :=
    pureTensorO ψ θ V' W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f₀
  have hp : ptF ψ θ A (Fr.ofModel M') f₀ = pt := rfl
  have hpt : ∀ φ, IsThetaFunO ψ V' W (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 φ
  have L := GlobalTheory.T.thetaLift_cuspForm_automorphic_smooth_moderateGrowth h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hint : ∀ F' : MultT θ M' J χ, ∀ φ x g, IntegrableOn
      (fun h => thetaKO ω' g h (pt φ) * (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)) x h) 𝓕 ν := fun F' φ x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F').aut w, (hM F').cusp w⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω' (g, h)) pt (MultT θ M' J χ) hint
  let G : PolF D W.rank V'.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V' → ℂ) :=
    B.compr₂ (LinearMap.applyₗ (⟨F, hF⟩ : MultT θ M' J χ))
  have hG : ∀ φ x, G φ x = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) (F x) := fun φ x => hB φ x ⟨F, hF⟩
  have hcl : ∀ w : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ w)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ w)) := fun w => ⟨hMF.aut w, hMF.cusp w⟩

  have hT : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ W τ Y t) (pt φ) z)
      (pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ) z) 0 :=
    fun τ Y hY φ z => (GlobalTheory.T.lieAction_fockOperators_scalars_trace D V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ (expS D k τ) (expT D k τ) hθ hW
      (hexp τ).1 (hexp τ).2 hf).2 Y hY φ z
  have hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (w : M'.Vec) (u : M'.sm τ), (u : M'.H τ) = dRep (M'.rep τ) Y (w τ) →
      G (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ)
        (PiTensorProduct.tprod ℂ w) + G φ (PiTensorProduct.tprod ℂ (Function.update w τ u)) = 0 := by
    intro τ Y hY φ w u hu
    have e1 := GlobalTheory.MultGelf.rder_apply hMF τ w hY (w τ) u hu
    rw [Function.update_eq_self] at e1
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω' τ Y (pt φ) =
        pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ) :=
      funext fun z => (hT τ Y hY φ z).deriv
    funext g
    have := L.derT_add (hpt φ) (hcl w) τ hY g
    rw [e2, add_comm] at this
    rw [Pi.add_apply, hG, hG]
    exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) A g) e1).symm.trans this

  have hav := mem_span_of_average G h' fun τ φ w => by
    obtain ⟨n, φs, c, hc, hφ⟩ := frame_fock_orbit D V' W _ A M' θ ψ ω' f₀ τ (expS D k τ) (expT D k τ) hθ
      (GlobalTheory.T.compact_subgroups_act_on_fock_vectors_all_signatures D V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ _ _ hθ hW (hexp τ).1 (hexp τ).2 hf f0) φ
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (w τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, ?_⟩
    funext g
    simp only [hG, Finset.sum_apply]
    exact GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V' W _ M' θ ψ χS χT ω' ν 𝓕 hθ hW hν h𝓕 τ n c _ _ _ _
      hc.1 (hpt φ) hφ (hcl w).1.toIsAutFun (fun i x => apply_kMean hMF τ (hc.1 i) w _ rfl x) g
      (hint ⟨F, hF⟩ _ _ g) fun i => hint ⟨F, hF⟩ _ _ g

  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨al, be, ga, de, hd, hbig, e1, e2⟩ := hP τ₀
  obtain ⟨p', q', hp', hq', hsig⟩ := hs τ₀
  have hnd : ((al ++ be) ++ (ga ++ de)).Nodup := by simpa only [List.append_assoc] using hd.1.2.2.2.2.2.2.1
  have hcard := signCard_signed (al ++ be) (ga ++ de) (expT D k τ₀) hnd.of_append_left hnd.of_append_right
  have e1' : parB (Ptw D) k τ₀ = dualPar (signed (al ++ be) (ga ++ de) (expT D k τ₀)) := congrArg dualPar e1
  rw [e1', GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.1, List.length_append] at hp'
  rw [e1', GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.2, List.length_append] at hq'
  obtain rfl : p' = al.length + be.length - i := by omega
  obtain rfl : q' = ga.length + de.length - i := by omega
  obtain ⟨e, he⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').2 A τ₀ _ _ hsig
  obtain ⟨-, -, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types _ al be ga de hd.1
  have ht := hd.1.1
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W _ M' τ₀ (al.length + de.length + D.R.t) (ga.length + be.length) _ _
    (expS D k τ₀) ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, congrArg dualPar e2⟩
  obtain ⟨U', hU'⟩ := hU' e' he'
  have kvan : ∀ φ (y : KT M'), G φ (inclK h' y) = 0 := by
    have hz := span_multi (G.compl₂ (inclK h')) fun p y => by
      funext g
      let b := slice (multi ((G.compl₂ (inclK h')).compr₂ (LinearMap.proj g))) τ₀ p y
      have hb0 := pairing_eq_zero X h5 hAR D.R.t al be ga de hd hbig i hi (by omega) (by omega) D V' W _ M' τ₀
        (A.ε τ₀) e e' m' (expS D k τ₀) U' (a' τ₀) b he he' hm' hU' (ha' τ₀) (fun Y hY Q z => by
          simp only [b, slice_apply, multi_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
            LinearMap.proj_apply]
          have eq1 : glue (Function.update p τ₀ (locT (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) Q +
              ((expS D k τ₀ : ℂ) * Y.trace) • Q)) =
              fockT τ₀ (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) (glue (Function.update p τ₀ Q)) +
                ((expS D k τ₀ : ℂ) * Y.trace) • glue (Function.update p τ₀ Q) := by
            rw [((GlobalTheory.T.gluing_law_holds D V'.rank W.rank).2 τ₀ _ _ _).2, Function.update_idem, Function.update_self]
            simp only [← glueM_apply, MultilinearMap.map_update_add, MultilinearMap.map_update_smul]
          have eq2 : Function.update y τ₀ (a' τ₀ Y z) = Function.update (Function.update y τ₀ z) τ₀
              (a' τ₀ Y (Function.update y τ₀ z τ₀)) := by
            rw [Function.update_idem, Function.update_self]
          rw [eq1, eq2, inclK_tprod h' (Function.update y τ₀ z), inclK_update h' (Function.update y τ₀ z) τ₀]
          refine congrFun (hBt τ₀ Y hY _ _ _ ?_) g
          exact ((ha' τ₀).der Y hY _).deriv.symm)
      have := LinearMap.congr_fun₂ hb0 (p τ₀) (y τ₀)
      simpa [b, slice_apply, multi_apply, Function.update_eq_self] using this
    exact fun φ y => LinearMap.congr_fun₂ hz φ y
  have h0 : G P v ∈ (⊥ : Submodule ℂ (GA D V' → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨φ, y, rfl⟩; simp [kvan φ y]) (hav P v)
  rw [Submodule.mem_bot, hG] at h0
  rw [hp]
  exact h0

end GlobalTheory.LowerMembers

end
