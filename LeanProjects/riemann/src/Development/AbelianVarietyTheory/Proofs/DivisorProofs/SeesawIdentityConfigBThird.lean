import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundFiniteFamily

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XTermBoundQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem finsupp {B : Base F E} {a a' n₁ d₁ : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M₂ : Model σ X₁ W₁}
    (H₀ : Plane E a n₁) (H' : Plane E (a + a') d₁) (hxy : form σ G.V.J H₀.x H₀.y = 1)
    (hxy' : form σ G.W.J H'.x H'.y = 1) {e : Fn F a (a + a') →ₗ[ℂ] Fn F n₁ d₁}
    (he : IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e) {K : Subgroup (UA σ G.V.J)} (hK : IsStab B K)
    {Φ : Fn F a (a + a')} (hΦ : Φ ∈ PolData B G.M) (h : UA σ G.W.J) :
    ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧
      ∀ k ∈ K, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U →
        e (G.M.co.rho B.ψ (shiftA H₀ H' l) (om (k, h) Φ)) = 0 := by
  have hstd := hT.base.std
  have hΦ' : Φ ∈ schA F (Fin a × Fin (a + a')) := polData_le hT.geo.hM hΦ
  obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B a G.V _ _ hT.base hT.geo.hV
  choose c hc using GlobalTheory.XTermSupp.trace_mul_dual (F := F) (E := E)
  have hO := fun i => GlobalTheory.XTermSupp.rho_om_fixed G.M B.ψ hstd.1 hT.weil hCc h Φ hΦ'
    (inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H₀.y) (incV F H'.x))
  obtain ⟨U, hU, hUm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F B.ψ hstd.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hstd) _
    (Filter.eventually_all.2 hO)
  refine ⟨Set.pi Set.univ fun _ => U, isCompact_univ_pi fun _ => hU, fun k hk l hl => ?_⟩
  by_contra hne
  refine hl fun i _ => hUm _ fun t ht => ?_
  have hfix := ht i k (hsub ((hK k).1 hk))
  have hΨ : om (k, h) Φ ∈ schA F (Fin a × Fin (a + a')) := (IsUWeilPair.isUSplitting hT.weil).pres _ _ hΦ'
  have h1 := congrArg e (GlobalTheory.XTermSupp.rho_comm G.M.co B.ψ (shiftA H₀ H' l) (pairA F 0 t • inclR (F := F) (AF F) (σ (c i)) •
    Matrix.vecMulVec (incV F H₀.y) (incV F H'.x)) (om (k, h) Φ))
  rw [hfix, map_smul, he.inv _ (Or.inl ⟨pairA F 0 t • inclR (F := F) (AF F) (σ (c i)) • incV F H₀.y, by
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]⟩) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΨ),
    GlobalTheory.XTermSupp.symp_shiftA hT.base.cm hT.geo.hW.skew H₀ H' hxy hxy', hc] at h1
  have h2 : pairA F 0 t * GlobalTheory.XTermMaj.crd F E (l : AE F E) i =
      pairA F 0 (t * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) :=
    Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  exact (smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm))

theorem finparts {B : Base F E} {a a' n₁ d₁ : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M₂ : Model σ X₁ W₁}
    {V₂ : Spc F E a} {H₀ : Plane E a n₁} {j₀ j₁ : ℕ} (hH₀ : H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁)
    (H' : Plane E (a + a') d₁) {e : Fn F a (a + a') →ₗ[ℂ] Fn F n₁ d₁}
    (he : IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e) {K : Subgroup (UA σ G.V.J)} (hK : IsStab B K)
    {Φ : Fn F a (a + a')} (hΦ : Φ ∈ PolData B G.M) (h : UA σ G.W.J) :
    ∃ (m : ℕ) (c : Fin m → Fin n₁ × Fin d₁ → Af F) (φ : Fin m → (Fin n₁ × Fin d₁ → Af F) → ℂ),
      (∀ j, φ j ∈ SB _) ∧ ∀ k ∈ K, ∀ (l : (AE F E)ˣ) (x : Fin n₁ × Fin d₁ → AF F),
        e (G.M.co.rho B.ψ (shiftA H₀ H' l) (om (k, h) Φ)) x =
          ∑ j, e (G.M.co.rho B.ψ (shiftA H₀ H' l) (om (k, h) Φ)) (fun q => ((x q).1, c j q)) * φ j (fun q => (x q).2) := by
  have hψ := hT.base.std
  have hΦ' : Φ ∈ schA F (Fin a × Fin (a + a')) := polData_le hT.geo.hM hΦ
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hs : Continuous (M₂.co.e.symm : _ → Matrix (Fin n₁) (Fin d₁) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap M₂.co.e.symm.toLinearMap
  have hc : Continuous fun w => incM F H₀.ι * M₂.co.e.symm w * (incM F H'.ι)ᵀ :=
    (continuous_const.matrix_mul hs).matrix_mul continuous_const
  have hN := (hc.tendsto' 0 0 (by simp)).eventually
    (GlobalTheory.XTermFinParts.eventually_rho_om_eq hT.base hT.geo.hV hK G.M hT.weil hΦ' h)
  obtain ⟨m, c, φ, hφ, hD⟩ := GlobalTheory.XTermFinParts.exists_parts hψ hN
  refine ⟨m, c, φ, hφ, fun k hk l => hD _ fun w hw h0 => ?_⟩
  have hΨ : om (k, h) Φ ∈ schA F _ := (IsUWeilPair.isUSplitting hT.weil).pres (k, h) Φ hΦ'
  have h1 := hw (by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← map_smul, h0, map_zero, Matrix.mul_zero, Matrix.zero_mul]) k hk
  have h2 := he.Heisenberg₂ (M₂.co.e.symm w) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ (shiftA H₀ H' l) _ hΨ)
  rw [GlobalTheory.XTermFinParts.rho_comm G.M.co B.ψ (by
      rw [Matrix.mul_assoc]; exact GlobalTheory.XTermFinParts.symp_eq_zero hH₀ _ _ _ _), h1,
    show M₂.co.rho B.ψ (M₂.co.e.symm w) = schr B.ψ w from congrArg (schr B.ψ) (M₂.co.e.apply_symm_apply w)] at h2
  exact h2.symm

section Decay

open GlobalTheory.XTermDecay

theorem decay {B : Base F E} {a a' n₁ d₁ : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M₂ : Model σ X₁ W₁}
    (H₀ : Plane E a n₁) (H' : Plane E (a + a') d₁) (hxy : form σ G.V.J H₀.x H₀.y = 1)
    (hxy' : form σ G.W.J H'.x H'.y = 1) {e : Fn F a (a + a') →ₗ[ℂ] Fn F n₁ d₁}
    (he : IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e) {K : Subgroup (UA σ G.V.J)} (hK : IsStab B K)
    {Φ : Fn F a (a + a')} (hΦ : Φ ∈ PolData B G.M) (h : UA σ G.W.J)
    (U : Set (Fin (Module.finrank F E) → Af F)) (hU : IsCompact U) (c : Fin n₁ × Fin d₁ → Af F) (N : ℕ)
    (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, ∀ k ∈ K, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
      ∃ f : SInf F (Fin n₁ × Fin d₁), (∀ y, f y = e (G.M.co.rho B.ψ (shiftA H₀ H' l) (om (k, h) Φ))
          (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c q))) ∧
        (s.sup (schwartzSeminormFamily ℂ _ ℂ)) f ≤
          C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B a G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E a G.V hX.lat)) hsub
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  have hΦA : Φ ∈ schA F _ := polData_le hT.geo.hM hΦ
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun k : K => om (k.1, h) Φ)
    (fun k => hw.isUSplitting.pres (k.1, h) Φ hΦA) fun l hl => by
      have hc := (hw.2.2 l hl Φ hΦA).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V.J => (g, h))
      obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨C, fun k => hC k.1 k.2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H₀.x H₀.y H'.x H'.y hxy (by
    rw [form_swap hT.base.cm hT.geo.hW.skew, hxy', map_one])
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H₀.x) (incV F H'.y))
  let U' := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H₀.y) (incV F H'.x))
  have hp : Continuous ⇑(Finset.sup s (schwartzSeminormFamily ℂ (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ)) :=
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  choose C hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H₀.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) (hg j) (f j) (hf j) hU _ hp N
  refine ⟨∑ j, C j, fun k hk l hl => ?_⟩
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ (GlobalTheory.XTermMaj.crd F E (l : AE F E)) hl
  have hS : G.M.co.e (shiftA H₀ H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    rw [shiftA]
    congr 1
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  refine ⟨∑ j, f₁ j, fun y => ?_, ?_⟩
  · have h1 := hdec ⟨k, hk⟩
    simp only at h1
    rw [h1, Darboux.rho, hS]
    change coeL (∑ j, f₁ j) y = (sliceL c ∘ₗ e) (schrL B.ψ _ _) y
    rw [map_sum, map_sum, map_sum]
    exact congrFun (Finset.sum_congr rfl fun j _ => hf₁ j) y
  · rw [Finset.sum_mul]
    exact (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
      (Finset.sum_le_sum fun j _ => hb₁ j)

end Decay

theorem seminorm (hKP : KP) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (hdim : d + 2 * min r s < 2 * n ∨ min r s = 0) (m : ℕ) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hφ : ∀ j, φ j ∈ SB _) :
    ∃ (T : Finset (ℕ × ℕ)) (C : ENNReal), C ≠ ⊤ ∧ ∀ f : Fin m → SInf F (Fin n × Fin d),
      ∫⁻ g₀ in M.dom, ‖thetaSum F (om (g₀, 1) (∑ j, pureA F (f j) (φ j)))‖ₑ ∂M.μ ≤
        C * ∑ j, ENNReal.ofReal ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) (f j)) := by
  choose T C hC hb using fun j =>
    GlobalTheory.WeilSeminorm.lintegral_theta_pure_le hKP F E σ B n d X W M χX χW om r s r' s' hP hdim (φ j) (hφ j) 1
  have hbas := GlobalTheory.T.theta_basic_properties hKP.base F E σ B n d X W M χX χW om r s r' s' hP
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  refine ⟨Finset.univ.biUnion T, ∑ j, C j, ENNReal.sum_ne_top.2 fun j _ => hC j, fun f => ?_⟩
  have memA : ∀ j, pureA F (f j) (φ j) ∈ schA F (Fin n × Fin d) := fun j =>
    Submodule.subset_span ⟨f j, φ j, hφ j, rfl⟩
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  have cont : ∀ j, Continuous fun g => theta om (pureA F (f j) (φ j)) g 1 := fun j =>
    (hbas.1 _ (memA j)).1.comp (continuous_id.prodMk continuous_const)
  calc ∫⁻ g₀ in M.dom, ‖thetaSum F (om (g₀, 1) (∑ j, pureA F (f j) (φ j)))‖ₑ ∂M.μ
      ≤ ∫⁻ g₀ in M.dom, ∑ j, ‖theta om (pureA F (f j) (φ j)) g₀ 1‖ₑ ∂M.μ := by
        refine lintegral_mono fun g₀ => ?_
        rw [map_sum, GlobalTheory.WeilSeminorm.thetaSum_finset_sum _ _ fun j _ => pres _ _ (memA j)]
        exact enorm_sum_le _ _
    _ = ∑ j, ∫⁻ g₀ in M.dom, ‖theta om (pureA F (f j) (φ j)) g₀ 1‖ₑ ∂M.μ :=
        lintegral_finsetSum _ fun j _ => (cont j).enorm.measurable
    _ ≤ ∑ j, (∑ i, C i) * ENNReal.ofReal (((Finset.univ.biUnion T).sup (schwartzSeminormFamily ℂ _ ℂ)) (f j)) := by
        refine Finset.sum_le_sum fun j _ => (hb j (f j)).trans (mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_))
        · exact Finset.single_le_sum (f := C) (fun _ _ => zero_le) (Finset.mem_univ j)
        · exact Seminorm.le_def.1 (Finset.sup_mono (Finset.subset_biUnion_of_mem T (Finset.mem_univ j))) (f j)
    _ = _ := by rw [Finset.mul_sum]

theorem bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ Φ ∈ PolData B G.M, ∀ h : UA σ G.W.J, ∀ (om₂ : Rep σ X₁ G₁.W) (χX χW : Chr F E) (r s r' s' : ℕ), IsPair B M₂ χX χW om₂ r s r' s' → (a + b + 2 * min r s < 2 * n₁ ∨ min r s = 0) → ∀ K : Subgroup (UA σ G.V.J), IsStab (X := G.V) B K → ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∀ N : ℕ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k ∈ K, ∀ l : (AE F E)ˣ, ∫⁻ g₀ in M₂.dom, ‖thetaSum F (om₂ (g₀, 1) (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' l) (om (k, h) Φ))))‖ₑ ∂M₂.μ ≤ C * GlobalTheory.XTermMaj.maj F E N U (l : AE F E) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h
    om₂ χX χW r s r' s' hP hdim K hK
  have hxy : form σ G.V.J H₀.x H₀.y = 1 := hH₀.xy
  have hxy' : form σ G.W.J H'.x H'.y = 1 := hC.hH'.xy
  obtain ⟨U, hU, hU0⟩ := finsupp hT H₀ H' hxy hxy' hev hK hΦ h
  obtain ⟨m, c, φ, hφ, hint⟩ := finparts hT hH₀ H' hev hK hΦ h
  obtain ⟨T, C₁, hC₁t, hC₁⟩ := seminorm hKP hP hdim m φ hφ
  refine ⟨U, hU, fun N => ?_⟩
  choose Cj hCj using fun j : Fin m => decay hT H₀ H' hxy hxy' hev hK hΦ h U hU (c j) N T
  refine ⟨C₁ * ENNReal.ofReal (∑ j, |Cj j|), ENNReal.mul_ne_top hC₁t ENNReal.ofReal_ne_top, ?_⟩
  intro k hk l
  set w : ℝ := (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) with hw
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · choose f hf hfb using fun j => hCj j k hk l hl
    have hD : e₂ (G.M.co.rho B.ψ (shiftA H₀ H' l) (om (k, h) Φ)) = ∑ j, pureA F (f j) (φ j) := by
      funext x
      rw [hint k hk l x, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [pureA, hf j, RingEquiv.symm_apply_apply]
    have hmaj : GlobalTheory.XTermMaj.maj F E N U (l : AE F E) = ENNReal.ofReal w := by
      simp only [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, hw]
    have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) _
    rw [hD, hmaj]
    refine (hC₁ f).trans ?_
    rw [mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => abs_nonneg _), Finset.sum_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hw0)]
    refine Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal ((hfb j).trans ?_)
    gcongr
    exact le_abs_self _
  · rw [hU0 k hk l hl]
    simp only [map_zero, thetaSum, Pi.zero_apply, tsum_zero, enorm_zero, lintegral_zero]
    exact zero_le

end GlobalTheory.XTermBoundQ

end
