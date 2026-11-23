import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelThetaRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeSpaceFiniteDimensionalStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LowFixCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fockDeg_stable_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hψ : IsStd ψ) (hw : M.IsWeil ψ χX χW om)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {k : UA σ X.J} (hk : k ∈ KInf σ X τ)
    (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) (⇑f) (⇑(A f))) (j : ℕ) :
    fockDeg M ψ τ j ≤ (fockDeg M ψ τ j).comap A := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have hL := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, GlobalTheory.RealLift.SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (GlobalTheory.FockCompactW.heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (mat k * u)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (GlobalTheory.FockCompactW.heisLine_zero M ψ _)
      (GlobalTheory.FockCompactX.sd_intertwine_left hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : mat k * mat k⁻¹ = 1 := by
    change mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), mat k * (mat k⁻¹ * u) = u := fun u => by
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hvac : ∀ f₀, M.IsGauss ψ τ f₀ → M.IsGauss ψ τ (A f₀) := by
    intro f₀ hf₀
    obtain ⟨ε, hε⟩ := hf₀
    refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
    have hv := GlobalTheory.FockCompactX.at_mul_left hu (mat k⁻¹)
    have hv' := GlobalTheory.FockCompactX.at_mul_left hu' (mat k⁻¹)
    have h1 := hint _ hv f₀
    have h2 := hint _ hv' f₀
    rw [hcan] at h1 h2
    have e1 := (hL _ _ _).2.2.1 _ hg h1
    have e2 := (hL _ _ _).2.2.1 _ hg' h2
    have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
    · rw [e1, e2, key, map_smul]
    · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
        rw [← Matrix.map_mul]
        change (mat (k⁻¹ * k)).map _ = 1
        rw [inv_mul_cancel]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
      have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
        calc _ = (mat k⁻¹).map (piInf (τ w)) * X.θ w *
              ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
          _ = (mat k⁻¹).map (piInf (τ w)) * (X.θ w * (mat k).map (piInf (τ w))) *
              (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
      rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.mul_smul]
      congr 1
      simp only [← Matrix.mul_assoc]
      rw [hc]
  induction j with
  | zero =>
    rw [fockDeg_zero]
    exact Submodule.span_le.2 fun f₀ hf₀ => Submodule.mem_comap.2 (Submodule.subset_span (hvac f₀ hf₀))
  | succ i ih =>
    rw [fockDeg_succ]
    refine sup_le (ih.trans (Submodule.comap_mono le_sup_left)) (Submodule.span_le.2 ?_)
    rintro φ₁ ⟨u, hu, φ, hφ, hφ₁⟩
    have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
    rw [e]
    exact Submodule.mem_comap.2 (Submodule.mem_sup_right
      (Submodule.subset_span ⟨mat k * u, GlobalTheory.FockCompactX.at_mul_left hu _, A φ, ih hφ, hint u hu φ⟩))

theorem lowPartInf_le_fixPart : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      lowPartInf B G.M R.p ≤ (fixPart B G.M om (lowDegInf B G.M R.p)).map R.p := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf h
  classical
  have hT := h.triple
  have hψ : IsStd B.ψ := hT.base.std
  have hw := hT.weil
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evI F) := by
    intro u _
    simp [mat]
  have hex : ∀ k : UA σ G.V.J, ∃ A : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
      k ∈ KInf σ G.V B.emb → ∀ v : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (k, 1)) v (A v) := by
    intro k
    by_cases hk : k ∈ KInf σ G.V B.emb
    · obtain ⟨A, hA⟩ := GlobalTheory.FockCompactW.exists_op_of_UAt hψ hw (k, 1) hk.1 h1W
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose A hA using hex
  set V : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) := fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p) with hVdef
  have hVfin : FiniteDimensional ℂ V :=
    GlobalTheory.T.fock_degree_space_finiteDimensional F E σ B a (a + a') G.V G.W G.M _ _ _ _ hT.base hT.geo.hV hT.geo.hW
      hT.geo.hM _
  have hVst : ∀ k ∈ KInf σ G.V B.emb, ∀ v ∈ V, A k v ∈ V := fun k hk v hv =>
    fockDeg_stable_left hψ hw B.emb hk (A k) (hA k hk) _ hv
  let U : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) :=
    Submodule.span ℂ {z | ∃ k ∈ KInf σ G.V B.emb, ∃ v ∈ V, z = A k v - v}
  have hUV : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, v, hv, rfl⟩
    exact V.sub_mem (hVst k hk v hv) hv)
  have hU0 : U ≤ LinearMap.ker R.p := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, v, hv, rfl⟩
    show R.p (A k v - v) = 0
    rw [map_sub, h.real.quot.cpt k hk v (fockDeg_le_pol _ _ _ _ hv) _ (hA k hk v), sub_self])
  intro y hy
  rw [lowPartInf, Submodule.mem_map] at hy
  obtain ⟨f, hf, rfl⟩ := hy
  obtain ⟨u, hu, hfx⟩ := GlobalTheory.KFixedVanish.exists_fixed
    (Measure.addHaar : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) U V hVfin hUV
    ((fun k => A k) '' KInf σ G.V B.emb)
    (by
      rintro _ ⟨k, hk, rfl⟩ v hv
      exact Submodule.subset_span ⟨k, hk, v, hv, rfl⟩)
    (by
      rintro _ ⟨k, hk, rfl⟩ v
      exact GlobalTheory.T.weil_action_preserves_lintegral F E σ a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hw (k, 1) v (A k v) (hA k hk v) _
        inferInstance)
    f hf
  refine ⟨f - u, Submodule.subset_span ⟨V.sub_mem hf (hUV hu), fun k hk => ?_⟩, ?_⟩
  · have h' := hA k hk (f - u)
    rwa [hfx (A k) ⟨k, hk, rfl⟩] at h'
  · rw [map_sub, LinearMap.mem_ker.1 (hU0 hu), sub_zero]

end GlobalTheory.LowFixCover

end
