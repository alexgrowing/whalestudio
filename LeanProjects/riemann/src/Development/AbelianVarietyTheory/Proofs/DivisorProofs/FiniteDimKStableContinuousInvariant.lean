import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDataFromUnramifiedInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianFormIntegralLatticeExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianRealPlaceSignatureNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeSelfDualHermitianExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLevelMatrixEntryIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationRepUnitaryModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothModerateGrowthArchimedeanRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActionIterateMatchesDifferentialStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HCFinU

theorem automorphicForms_finite_skew : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → Even d → ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ T : Submodule ℂ (UA σ W.J → ℂ), FiniteDimensional ℂ T → (∀ t ∈ T, Continuous t) → (∀ k, ∀ t ∈ T, rt (Subgroup.closure (KInf σ W B.emb)) k t ∈ T) → ∀ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) → ∀ A : Set (UA σ W.J → ℂ), A ⊆ typeSet (rt (Subgroup.closure (KInf σ W B.emb))) ⊤ T → (∀ φ ∈ A, IsSmoothModerate σ (c • W.J.map σ) (fun x => φ ((toGAd hσ W.J hc).symm x))) → (∀ φ ∈ A, ∀ k ∈ U, k ∈ finU σ W.J → ∀ x, φ (x * k) = φ x) → (∀ z, IsCentral σ (c • W.J.map σ) z → ∃ (N : ℕ) (b : Fin N → ℂ), ∀ φ ∈ A, (dop z)^[N] (fun x => φ ((toGAd hσ W.J hc).symm x)) = ∑ i : Fin N, b i • (dop z)^[i.val] (fun x => φ ((toGAd hσ W.J hc).symm x))) → FiniteDimensional ℂ (Submodule.span ℂ A) := by
  intro hKP F E _ _ _ _ _ σ hσ B d r s W hG hW hd c hc hcs T hTfin hTcont hTst U hU A hA hsm hlev hz
  obtain ⟨⟨hJ, hdet⟩, L, hfg, hspan, hdual⟩ := GlobalTheory.T.skew_hermitian_form_integral_lattice_exists F E σ B d r s W hG hW hd c hc hcs
  have cm := GlobalTheory.T.cm_data_from_unramified_involution F E σ hσ hG.cm hG.unram
  choose ε P hPu hP hθ using GlobalTheory.T.skew_hermitian_real_place_signature_normal F E σ B d r s W hG hW c hc hcs
  have hφ : ∀ v (a : F), (B.emb v).1 (algebraMap F E a) = v.embedding a := fun v a =>
    RingHom.congr_fun (B.emb v).2 a
  let I := GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP
  have hs : σ = I.cm.sig := GlobalTheory.HCFinU.mkI_sig σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε _ hφ P hPu hP
  let e : I.GA ≃ₜ* GAd σ (c • W.J.map σ) := GlobalTheory.HCFinU.bridgeS I σ hs
  let u := toGAd hσ W.J hc
  have hu' : Continuous u.symm := continuous_subtype_val.subtype_mk _
  let U' : Subgroup (GAd σ (c • W.J.map σ)) := U.map u.toMonoidHom
  have hU'mem : ∀ y, y ∈ U' ↔ u.symm y ∈ U := fun y => Subgroup.mem_map_equiv
  have hU' : IsOpen (U' : Set (GAd σ (c • W.J.map σ))) := by
    have : (U' : Set (GAd σ (c • W.J.map σ))) = u.symm ⁻¹' (U : Set (UA σ W.J)) :=
      Set.ext fun y => hU'mem y
    rw [this]; exact hU.preimage hu'
  obtain ⟨g, hg, hgk⟩ := GlobalTheory.T.finite_level_matrix_entry_integrality I σ hs U' hU'
  haveI := GlobalTheory.T.archimedean_maximal_compact_is_compact I
  let incl : GlobalTheory.Dec.Kinf I →* I.GA := (MonoidHom.inl _ _).comp
    (Pi.monoidHom fun v => (Formalism.REAL.KG (I.ε v)).subtype.comp (Pi.evalMonoidHom _ v))
  have hincl : Continuous incl :=
    (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v)).prodMk continuous_const
  let j : GlobalTheory.Dec.Kinf I →* UA σ W.J := u.symm.toMonoidHom.comp (e.toMulEquiv.toMonoidHom.comp incl)
  have hj : Continuous j := hu'.comp (e.continuous.comp hincl)
  have hjH : ∀ k, j k ∈ Subgroup.closure (KInf σ W B.emb) := fun k =>
    Subgroup.subset_closure (GlobalTheory.T.cm_lattice_self_dual_hermitian_exists F E σ hσ B d r s W hG hW c hc hcs cm hJ hdet L hfg hspan hdual ε hφ P hPu hP hθ hs k)
  haveI : IsTopologicalGroup (UA σ W.J) := (GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J).1
  obtain ⟨m, τ, hτ, hL⟩ := GlobalTheory.T.finite_dim_translation_rep_unitary_model (UA σ W.J) (GlobalTheory.Dec.Kinf I) j hj _ hjH T hTfin hTcont hTst
  choose zz hzc hzeq using fun v mm => GlobalTheory.T.center_action_iterate_matches_differential I σ hs v mm
  choose NN bb hNb using fun v mm => hz (zz v mm) (hzc v mm)
  have hAF : GlobalTheory.Dec.AutFinite := hKP.automorphicFormsFiniteUnitary
  have hfin := hAF I g hg NN bb (EuclideanSpace ℂ (Fin m)) τ hτ
  let f : (UA σ W.J → ℂ) → I.GA → ℂ := fun φ x => φ (u.symm (e x))
  let S : Set (I.GA → ℂ) := {f : I.GA → ℂ | GlobalTheory.Dec.IsSmoothMG I g f ∧
    (∀ v mm x, (GlobalTheory.Dec.zOp I v mm)^[NN v mm] f x = ∑ i, bb v mm i * (GlobalTheory.Dec.zOp I v mm)^[i.val] f x) ∧
    ∃ L : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (I.GA → ℂ),
      (∀ (k : GlobalTheory.Dec.Kinf I) w x, L (τ k w) x = L w (x * (fun v => (k v : Formalism.REAL.UJ (I.ε v)), 1))) ∧
        f ∈ LinearMap.range L}
  have key : ∀ φ ∈ A, f φ ∈ S := by
    intro φ hφA
    have hsmφ := hsm φ hφA
    refine ⟨⟨?_, ?_, fun xf => GlobalTheory.T.smooth_moderate_growth_archimedean_restriction I σ hs _ hsmφ xf⟩, ?_, ?_⟩
    · intro γ hγ x
      show φ (u.symm (e (γ * x))) = φ (u.symm (e x))
      rw [map_mul]
      exact hsmφ.left (e γ) (GlobalTheory.HCFinU.bridgeS_rat I σ hs γ hγ) (e x)
    · intro k hk x
      obtain ⟨hkU, hkf⟩ := hgk k hk
      show φ (u.symm (e (x * (1, k)))) = φ (u.symm (e x))
      rw [map_mul, map_mul]
      refine hlev φ hφA _ ((hU'mem _).1 hkU) ?_ _
      rw [mem_finU]
      have h1 := toGAd_mat hσ W.J hc (u.symm (e (1, k)))
      rw [MulEquiv.apply_symm_apply] at h1
      show (((u.symm (e (1, k))).1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)).map _ = 1
      rw [← h1]
      exact hkf
    · intro v mm x
      have h1 := hzeq v mm (NN v mm) (fun y => φ (u.symm y)) hsmφ.smooth
      have h2 := hNb v mm φ hφA
      refine (congrFun h1 x).trans ((congrFun h2 (e x)).trans ?_)
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h3 := congrFun (hzeq v mm i.val (fun y => φ (u.symm y)) hsmφ.smooth) x
      rw [Pi.smul_apply, smul_eq_mul]
      exact congrArg _ h3.symm
    · obtain ⟨L₀, hL₀, w, hw⟩ := hL φ (hA hφA)
      refine ⟨(LinearMap.funLeft ℂ ℂ (fun y => u.symm (e y))).comp L₀, fun k w' x => ?_, w, ?_⟩
      · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]
        rw [hL₀, map_mul, map_mul]
        rfl
      · funext x
        simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, hw, f]
  let Φ : (I.GA → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ) := LinearMap.funLeft ℂ ℂ (fun y => e.symm (u y))
  have hspanA : Submodule.span ℂ A ≤ (Submodule.span ℂ S).map Φ := by
    rw [Submodule.span_le]
    intro φ hφA
    refine ⟨f φ, Submodule.subset_span (key φ hφA), ?_⟩
    funext y
    simp [Φ, f, LinearMap.funLeft_apply]
  haveI : FiniteDimensional ℂ (Submodule.span ℂ S) := hfin
  exact Submodule.finiteDimensional_of_le hspanA

end GlobalTheory.HCFinU

end
