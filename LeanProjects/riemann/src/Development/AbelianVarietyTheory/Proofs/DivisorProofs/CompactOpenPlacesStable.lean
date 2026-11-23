import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSphericalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedIdempotentTendstoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorsFormOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerInertSphereStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TruncFix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem truncU_empty {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : truncU ∅ k = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show truncMat (idem ∅) (mat k) = 1
  simp [truncMat, idem]

theorem truncU_of_triv {v : Pl F} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J)
    (hk : ∀ u : AF F, At (evFin F v) u → u • (mat k - 1) = 0) : truncU {v} k = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show truncMat (idem {v}) (mat k) = 1
  rw [truncMat, idem_singleton, hk _ (GlobalTheory.LatVac.at_liftV v 1), add_zero]

theorem tendsto_truncU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J)
    (hk : ∀ u : AF F, At (evI F) u → u • (mat k - 1) = 0) :
    Tendsto (fun T : Finset (Pl F) => truncU T k) atTop (𝓝 k) := by
  have hk' : ∀ u : AF F, At (evI F) u → u • (mat k⁻¹ - 1) = 0 := by
    intro u hu
    have hinv : mat k⁻¹ * mat k = 1 := Units.inv_mul k.1
    have : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
      rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
    rw [this, smul_neg, ← Matrix.mul_smul, hk u hu, Matrix.mul_zero, neg_zero]
  have hent : ∀ A : Matrix (Fin n) (Fin n) (AE F E), (∀ u : AF F, At (evI F) u → u • (A - 1) = 0) →
      Tendsto (fun T : Finset (Pl F) => truncMat (idem T) A) atTop (𝓝 A) := by
    intro A hA
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hc : ∀ u : AF F, At (evI F) u → u • (A - 1) i j = 0 := fun u hu => by
      have := congrFun (congrFun (hA u hu) i) j
      simpa using this
    have h := (GlobalTheory.T.truncated_idempotent_tendsto F E ((A - 1) i j) hc).const_add ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j)
    rw [Matrix.sub_apply, add_sub_cancel] at h
    show Tendsto (fun T : Finset (Pl F) => truncMat (idem T) A i j) atTop (𝓝 (A i j))
    refine h.congr fun T => ?_
    simp [truncMat]
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds (hent _ hk) ?_
  exact (MulOpposite.continuous_op.tendsto _).comp (hent _ hk')

theorem eAt_smul_of_mem {d : ℕ} (W : Spc F E d) (v : Pl F) {z : Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : GlobalTheory.LatVac.liftV v 1 • z = z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    rw [smul_smul, GlobalTheory.ThK.LocalOps.liftV_one_mul]
    congr 1
    have h1 : evFin F v (1 - GlobalTheory.LatVac.liftV v 1) = 0 := by
      rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
    have h2 := ha _ h1
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero, GlobalTheory.ThK.LocalOps.liftV_one_mul] at h2
    exact h2.symm
  | zero => rw [smul_zero]
  | add z z' _ _ h h' => rw [smul_add, h, h']
  | neg z _ h => rw [smul_neg, h]

theorem truncMat_mulVec {d : ℕ} (W : Spc F E d) (v : Pl F) (A : Matrix (Fin d) (Fin d) (AE F E)) {z : Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) (hA : A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    truncMat (idem {v}) A *ᵥ z = A *ᵥ z := by
  have hs : ((GlobalTheory.LatVac.liftV v 1) • (A - 1)) *ᵥ z = (GlobalTheory.LatVac.liftV v 1) • ((A - 1) *ᵥ z) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc]
  rw [truncMat, idem_singleton, Matrix.add_mulVec, Matrix.one_mulVec, hs, Matrix.sub_mulVec,
    Matrix.one_mulVec, smul_sub, eAt_smul_of_mem W v hz, eAt_smul_of_mem W v hA]
  abel

theorem truncU_mem_KAt {d : ℕ} (W : Spc F E d) (v : Pl F) (k : UA σ W.J)
    (h : ∀ z ∈ GlobalTheory.InertSph.latAt W v, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    truncU {v} k ∈ GlobalTheory.InertSph.KAt σ W v := by
  refine ⟨truncU_mem_UAt v k, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mat_truncU, truncMat_mulVec W v _ hz (h z hz).1]; exact (h z hz).1
  · rw [mat_truncU_inv, truncMat_mulVec W v _ hz (h z hz).2]; exact (h z hz).2

open scoped Classical in

theorem eval_mem_adm (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem fix_one {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (om : Rep σ Y W) (hcont : IsContOn (adeleClass F) om) (S T : Finset (Pl F)) (k : UA σ W.J) (hTS : T ⊆ S)
    (hinf : ∀ u : AF F, At (evI F) u → u • (mat k - 1) = 0)
    (hS : ∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat k - 1) = 0)
    (hloc : ∀ v, v ∉ S → Acts (evFin F v) (om (1, truncU {v} k)) (M.vac v) (M.vac v))
    (f : SInf F (Fin n × Fin d)) (φ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ)
    (hSB : ∀ w, φ w ∈ SB (Fin n × Fin d → Fv F w)) (hvac : ∀ w ∉ T, φ w = M.vac w) :
    om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  classical
  have hcof : ∀ᶠ w in cofinite, φ w = M.vac w :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun w hw => by_contra fun h => hw (hvac w h))
  have hstd : ∀ᶠ w in cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    (hcof.and hM.std).mono fun w hw => hw.1.trans hw.2
  have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F _ := GlobalTheory.ConeMeasV.pure_mem_schA hM f φ hSB hcof
  have hfin := fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x
  have hfinT : ∀ T' : Finset (Pl F), om (1, truncU T' k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    intro T'
    refine Finset.induction_on T' ?_ ?_
    · rw [truncU_empty, show ((1 : UA σ Y.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
    · intro v T' hv ih
      rw [truncU_insert hv, show ((1 : UA σ Y.J), truncU {v} k * truncU T' k) =
        ((1 : UA σ Y.J), truncU {v} k) * ((1 : UA σ Y.J), truncU T' k) by simp, map_mul, Module.End.mul_apply, ih]
      by_cases hvS : v ∈ S
      · rw [truncU_of_triv k (hS v hvS), show ((1 : UA σ Y.J), (1 : UA σ W.J)) = 1 from rfl, map_one,
          Module.End.one_apply]
      · have hφv : φ v = M.vac v := hvac v fun h => hvS (hTS h)
        have hA : Acts (evFin F v) (om (1, truncU {v} k)) (φ v) (M.vac v) := by rw [hφv]; exact hloc v hvS
        rw [GlobalTheory.ThK.LocalOps.acts_pure v (om (1, truncU {v} k)) f φ (M.vac v) hpure hfin hA, ← hφv,
          Function.update_eq_self]
  funext x
  have hc : Continuous fun g : UA σ Y.J × UA σ W.J => om g (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x :=
    hcont _ (eval_mem_adm _ x) _ hpure
  have h1 : Tendsto (fun T' : Finset (Pl F) => om (1, truncU T' k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) atTop
      (𝓝 (om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x)) :=
    ((hc.comp (continuous_const.prodMk continuous_id)).tendsto k).comp (tendsto_truncU k hinf)
  simp only [hfinT] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

end GlobalTheory.TruncFix

namespace GlobalTheory.TruncFix

theorem fix_off_bad : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ S₀ : Finset (Pl F), ∀ (S T : Finset (Pl F)) (k : UA σ G.W.J), S₀ ⊆ S → T ⊆ S →
      (∀ u : AF F, At (evI F) u → u • (mat k - 1) = 0) →
      (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat k - 1) = 0) →
      (∀ w, w ∉ S → ∀ γ, (γ * Matrix.transpose (mat k) ∈ latAtV G.V G.W w ↔ γ ∈ latAtV G.V G.W w)) →
      (∀ w, w ∉ S → ∀ γ, (γ * Matrix.transpose (mat k) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) →
      (∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ),
        (∀ w, φ w ∈ SB (Fin a × Fin (a + a') → Fv F w)) → (∀ w ∉ T, φ w = G.M.vac w) →
        om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∧
      (∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
        (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w ∉ T, φ w = G.M'.vac w) →
        om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  obtain ⟨S₁, h₁⟩ := GlobalTheory.T.unramified_places_invariant hKP.base F E σ B a a' G X om om' hT
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.unramified_places_spherical hKP.base F E σ B a a' G X om om' hT
  obtain ⟨m, x, y, hxy, hsum⟩ := GlobalTheory.T.exists_lattice_vectors_form_one F E σ B a G.V _ _ hT.geo.hV (by have := hT.geo.lt; omega)
  refine ⟨S₁ ∪ S₂, fun S T k hS hTS hinf hSk hlat _ => ?_⟩
  have hK : ∀ v, v ∉ S → truncU {v} k ∈ GlobalTheory.InertSph.KAt σ G.W v := fun v hv =>
    truncU_mem_KAt G.W v k (GlobalTheory.T.lattice_stabilizer_inert_sphere F E σ B a (a + a') G.V G.W _ _ hT.geo.hV m x y hxy hsum v k (hlat v hv))
  refine ⟨fun f φ hSB hvac => ?_, fun f φ hSB hvac => ?_⟩
  · exact fix_one G.M B.ψ hT.geo.hM om hT.weil.2.2 S T k hTS hinf hSk
      (fun v hv => h₁ v (fun h => hv (hS (Finset.mem_union_left _ h))) _ (hK v hv)) f φ hSB hvac
  · exact fix_one G.M' B.ψ hT.geo.hM' om' hT.weil'.2.2 S T k hTS hinf hSk
      (fun v hv => h₂ v (fun h => hv (hS (Finset.mem_union_right _ h))) _ (hK v hv)) f φ hSB hvac

end GlobalTheory.TruncFix
