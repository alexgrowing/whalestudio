import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeSpaceFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionFockDegreeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FockDiag

open scoped InnerProductSpace

theorem top_le_span_eigen {S : Type} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    (U : S →ₗ[ℂ] S) (hU : ∀ x, ‖U x‖ = ‖x‖) : ⊤ ≤ Submodule.span ℂ {w | ∃ c : ℂ, U w = c • w} := by
  have hin : ∀ x y, ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ := (LinearMap.norm_map_iff_inner_map_map U).1 hU
  set Ua := LinearMap.adjoint U with hUa
  have h1 : Ua * U = 1 := by
    refine LinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left, hin, Module.End.one_apply]
  have h2 : U * Ua = 1 := mul_eq_one_comm.1 h1
  have hc : Commute U Ua := h2.trans h1.symm
  set A : Module.End ℂ S := U + Ua with hA
  set B : Module.End ℂ S := Complex.I • (U - Ua) with hB
  have hAs : A.IsSymmetric := fun x y => by
    simp only [hA, LinearMap.add_apply, inner_add_left, inner_add_right, LinearMap.adjoint_inner_left,
      LinearMap.adjoint_inner_right, hUa]
    ring
  have hBs : B.IsSymmetric := fun x y => by
    simp only [hB, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right, inner_sub_left,
      inner_sub_right, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, hUa, Complex.conj_I]
    ring
  have hAB : Commute A B := by
    refine Commute.smul_right ?_ _
    exact ((Commute.refl U).sub_right hc).add_left (hc.symm.sub_right (Commute.refl Ua))
  have htop := LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hAs hBs hAB
  rw [← htop]
  refine iSup_le fun a => iSup_le fun b => fun x hx => Submodule.subset_span ⟨(a - Complex.I * b) / 2, ?_⟩
  have ha : A x = a • x := Module.End.mem_eigenspace_iff.1 hx.1
  have hb : B x = b • x := Module.End.mem_eigenspace_iff.1 hx.2
  have e : A x - Complex.I • B x = (2 : ℂ) • U x := by
    simp only [hA, hB, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_sub, smul_smul,
      Complex.I_mul_I, neg_one_smul, sub_neg_eq_add]
    module
  rw [ha, hb, smul_smul] at e
  have e2 : U x = (1 / 2 : ℂ) • ((2 : ℂ) • U x) := by rw [smul_smul]; norm_num
  rw [e2, ← e, smul_sub, smul_smul, smul_smul, ← sub_smul]
  congr 1
  ring

theorem mem_span_eigen {V H : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (hι : Function.Injective ι)
    (T : V →ₗ[ℂ] V) (hT : ∀ v, ‖ι (T v)‖ = ‖ι v‖) (v : V) :
    v ∈ Submodule.span ℂ {w | ∃ c : ℂ, T w = c • w} := by
  set e := LinearEquiv.ofInjective ι hι
  haveI : FiniteDimensional ℂ (LinearMap.range ι) := LinearEquiv.finiteDimensional e
  set U : LinearMap.range ι →ₗ[ℂ] LinearMap.range ι := (e : V →ₗ[ℂ] LinearMap.range ι) ∘ₗ T ∘ₗ (e.symm : LinearMap.range ι →ₗ[ℂ] V)
  have hU : ∀ x, ‖U x‖ = ‖x‖ := fun x => by
    have h1 : ((U x : LinearMap.range ι) : H) = ι (T (e.symm x)) := rfl
    have h2 : ((x : LinearMap.range ι) : H) = ι (e.symm x) := by
      conv_lhs => rw [← e.apply_symm_apply x]
      rfl
    rw [Submodule.coe_norm, Submodule.coe_norm, h1, h2, hT]
  have hx := top_le_span_eigen U hU (Submodule.mem_top : e v ∈ ⊤)
  have hm := Submodule.mem_map_of_mem (f := (e.symm : LinearMap.range ι →ₗ[ℂ] V)) hx
  rw [Submodule.map_span] at hm
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨w, ⟨c, hc⟩, rfl⟩
  refine ⟨c, ?_⟩
  have : e (T (e.symm w)) = c • w := hc
  rw [← map_smul, ← e.symm_apply_eq.2 this.symm]

section Tens

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

noncomputable def archPoint (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)

theorem evI_archPoint (t : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (archPoint t i) = t i := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) = t i
  exact RingEquiv.apply_symm_apply _ _

theorem at_archPoint (t : κ → mixedEmbedding.mixedSpace F) : At (evI F) (archPoint t) := by
  intro u' hu'
  have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
  funext i
  refine Prod.ext ?_ ?_
  · show u'.1 * (archPoint t i).1 = 0
    rw [h0, zero_mul]
  · show u'.2 * (archPoint t i).2 = 0
    simp [archPoint]

theorem tens_inj {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0) (hR : ∀ f : SInf F κ, Rest (evI F) (⇑f) R)
    {f g : SInf F κ} (h : tens (evI F) (⇑f) R = tens (evI F) (⇑g) R) : f = g := by
  refine DFunLike.ext f g fun t => ?_
  have h1 := congrFun h (archPoint t)
  have hR' : R (archPoint t) = R 0 := by
    have := (hR f).1 0 (archPoint t) (at_archPoint t)
    rwa [zero_add] at this
  simp only [tens, evI_archPoint, hR'] at h1
  exact mul_right_cancel₀ hR0 h1

noncomputable def tensL (R : (κ → AF F) → ℂ) : SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := tens (evI F) (⇑f) R
  map_add' f g := by funext x; simp [tens, add_mul]
  map_smul' c f := by funext x; simp [tens, mul_assoc]

end Tens

set_option maxHeartbeats 1000000 in

theorem fockDeg_le_span_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χ₁ χ₂ : Chr F E) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om →
    ∀ k ∈ KInf σ W B.emb, ∀ j : ℕ, fockDeg M B.ψ B.emb j ≤ Submodule.span ℂ {f | f ∈ fockDeg M B.ψ B.emb j ∧
      ∃ c : ℂ, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ = c • f} := by
  intro F E _ _ _ _ _ σ B n d X W M om χ₁ χ₂ r s r' s' hB hX hW hM hWeil k hk j
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin n × Fin d)
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B n d X W M om χ₁ χ₂ hB hM hWeil k hk
  haveI := GlobalTheory.T.fock_degree_space_finiteDimensional F E σ B n d X W M r s r' s' hB hX hW hM j
  set V := fockDeg M B.ψ B.emb j with hV
  have hAV : ∀ f ∈ V, A f ∈ V := fun f hf => GlobalTheory.T.weil_action_fock_degree_formula F E σ B n d X W M om χ₁ χ₂ r s r' s' hB hX hW hM hWeil k hk j f hf (A f) (hA f)
  have huniq : ∀ (f f₁ : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, k)) ⇑f ⇑f₁ → f₁ = A f := fun f f₁ h =>
    tens_inj hR0 hR ((h R (hR f)).symm.trans (hA f R (hR f)))
  let T : V →ₗ[ℂ] V := A.restrict hAV
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hmem : ∀ f : SInf F (Fin n × Fin d), MemLp (tensL R f) 2 μ := fun f =>
    schA_memLp_two F (Fin n × Fin d) μ hμ _ (hR f).2
  let ι : V →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun f => (hmem f).toLp _
      map_add' := fun f g => by
        refine (MemLp.toLp_congr (hmem _) ((hmem f).add (hmem g)) (Filter.EventuallyEq.of_eq ?_)).trans
          (MemLp.toLp_add _ _)
        simp [map_add]
      map_smul' := fun c f => by
        refine (MemLp.toLp_congr (hmem _) ((hmem f).const_smul c) (Filter.EventuallyEq.of_eq ?_)).trans
          (MemLp.toLp_const_smul _ _)
        simp [map_smul] }
  have hι : Function.Injective ι := fun f g h => by
    have h1 : tensL R (f : SInf F (Fin n × Fin d)) =ᵐ[μ] tensL R g := (MemLp.toLp_eq_toLp_iff (hmem f) (hmem g)).1 h
    have h2 := (Continuous.ae_eq_iff_eq μ (GlobalTheory.ThetaUnfold.schA_continuous F (hR f).2)
      (GlobalTheory.ThetaUnfold.schA_continuous F (hR g).2)).1 h1
    exact Subtype.ext (tens_inj hR0 hR h2)
  have hunit := hWeil.1.1.unit μ hμ k
  have hT : ∀ v, ‖ι (T v)‖ = ‖ι v‖ := fun v => by
    show ‖(hmem _).toLp _‖ = ‖(hmem _).toLp _‖
    rw [Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    have e1 : tensL R (A v) = om (1, k) (tensL R v) := (hA v R (hR v)).symm
    have e2 := hunit (tensL R v) (hR v).2
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    show (∫⁻ x, ‖tensL R (A v) x‖ₑ ^ (2 : ENNReal).toReal ∂μ) ^ (1 / (2 : ENNReal).toReal) = _
    rw [e1]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    congr 1
  intro f hf
  have hx := mem_span_eigen ι hι T hT ⟨f, hf⟩
  have hm := Submodule.mem_map_of_mem (f := V.subtype) hx
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨w, ⟨c, hc⟩, rfl⟩
  refine ⟨w.2, c, fun f₁ h => (huniq _ _ h).trans ?_⟩
  exact congrArg Subtype.val hc

end GlobalTheory.FockDiag

end
