import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralIdeleMajorantFinite

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open scoped Classical

noncomputable section

namespace GlobalTheory.ConeDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem eventually_rho_om_eq_of_compact {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (hB : B.IsGood σ)
    {C : Set (UA σ X.J)} (hCc : IsCompact C) (M : Model σ X W) {χ χ' : Chr F E}
    {om : Rep σ X W} (hom : M.IsWeil B.ψ χ χ' om) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (h : UA σ W.J) :
    ∀ᶠ u in 𝓝 (0 : Matrix (Fin n) (Fin d) (AE F E)), GlobalTheory.XTermFinParts.infOne F • u = 0 →
      ∀ k ∈ C, M.co.rho B.ψ u (om (k, h) Φ) = om (k, h) Φ := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous (M.co.e : Matrix (Fin n) (Fin d) (AE F E) → _) :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hm : Continuous fun g : UA σ X.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  have h1 : ∀ᶠ u in 𝓝 (0 : Matrix (Fin n) (Fin d) (AE F E)),
      ∀ m ∈ (fun g : UA σ X.J => mat g⁻¹) '' C,
        GlobalTheory.XTermFinParts.infOne F • M.co.e (m * u * (mat h⁻¹)ᵀ) = 0 → schr B.ψ (M.co.e (m * u * (mat h⁻¹)ᵀ)) Φ = Φ := by
    refine (hCc.image hm).eventually_forall_of_forall_eventually fun m _ => ?_
    have c : Continuous fun p : Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin n) (AE F E) =>
        M.co.e (p.2 * p.1 * (mat h⁻¹)ᵀ) :=
      he.comp ((continuous_snd.matrix_mul continuous_fst).matrix_mul continuous_const)
    exact (c.tendsto' (0, m) 0 (by simp)).eventually (GlobalTheory.XTermFinParts.eventually_schr_eq hB.std hΦ)
  filter_upwards [h1] with u hu h0 k hk
  have h2 := hu (mat k⁻¹) ⟨k, hk, rfl⟩ (by
    rw [← map_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul, map_zero])
  have h3 := (IsUWeilPair.isUSplitting hom).impl (k, h) (mat k⁻¹ * u * (mat h⁻¹)ᵀ) Φ hΦ
  have h4 : actAB (cA σ) (k, h) (mat k⁻¹ * u * (mat h⁻¹)ᵀ) = u := by
    show mat k * (mat k⁻¹ * u * (mat h⁻¹)ᵀ) * (mat h)ᵀ = u
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, GlobalTheory.StabHaar.mat_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  rw [h4] at h3
  rw [← h3]
  exact congrArg _ h2

theorem finsupp_of_compact {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'}
    {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')} (hC : CfgA B G G₁ H H')
    {e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    {Ψ : Fn F (b + 2) (b + 2 + a')} (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')))
    {C : Set (UA σ G.V.J)} (hCc : IsCompact C) :
    ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∀ k ∈ C, ∀ l : (AE F E)ˣ,
      (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U → e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) = 0 := by
  have hstd := hT.base.std
  choose c hc using GlobalTheory.XTermSupp.trace_mul_dual (F := F) (E := E)
  have hO := fun i => GlobalTheory.XTermSupp.rho_om_fixed G.M B.ψ hstd.1 hT.weil hCc 1 Ψ hΨ
    (inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  obtain ⟨U, hU, hUm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F B.ψ hstd.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hstd) _
    (Filter.eventually_all.2 hO)
  refine ⟨Set.pi Set.univ fun _ => U, isCompact_univ_pi fun _ => hU, fun k hk l hl => ?_⟩
  by_contra hne
  refine hl fun i _ => hUm _ fun a ha => ?_
  have hfix := ha i k hk
  have hΨ' : om (k, 1) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (IsUWeilPair.isUSplitting hT.weil).pres _ _ hΨ
  have h1 := congrArg e (GlobalTheory.XTermSupp.rho_comm G.M.co B.ψ (shiftA H H' l) (pairA F 0 a • inclR (F := F) (AF F) (σ (c i)) •
    Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (k, 1) Ψ))
  rw [hfix, map_smul, he.inv _ (Or.inl ⟨pairA F 0 a • inclR (F := F) (AF F) (σ (c i)) • incV F H.y, by
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]⟩) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΨ'),
    GlobalTheory.XTermSupp.symp_shiftA hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy, hc] at h1
  have h2 : pairA F 0 a * GlobalTheory.XTermMaj.crd F E (l : AE F E) i =
      pairA F 0 (a * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) :=
    Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  exact (smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm))

theorem finite_parts_of_compact {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'}
    {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')} (hC : CfgA B G G₁ H H')
    {e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    {Ψ : Fn F (b + 2) (b + 2 + a')} (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')))
    {C : Set (UA σ G.V.J)} (hCc : IsCompact C) :
    ∃ (m : ℕ) (c : Fin m → Fin b × Fin (b + a') → Af F) (φ : Fin m → (Fin b × Fin (b + a') → Af F) → ℂ),
      (∀ j, φ j ∈ SB _) ∧ ∀ k ∈ C, ∀ (l : (AE F E)ˣ) (x : Fin b × Fin (b + a') → AF F),
        e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) x =
          ∑ j, e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) (fun q => ((x q).1, c j q)) * φ j (fun q => (x q).2) := by
  have hψ := hT.base.std
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hs : Continuous (G₁.M.co.e.symm : _ → Matrix (Fin b) (Fin (b + a')) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap G₁.M.co.e.symm.toLinearMap
  have c : Continuous fun w => incM F H.ι * G₁.M.co.e.symm w * (incM F H'.ι)ᵀ :=
    (continuous_const.matrix_mul hs).matrix_mul continuous_const
  have hN := (c.tendsto' 0 0 (by simp)).eventually (eventually_rho_om_eq_of_compact hT.base hCc G.M hT.weil hΨ 1)
  obtain ⟨m, c, φ, hφ, hD⟩ := GlobalTheory.XTermFinParts.exists_parts hψ hN
  refine ⟨m, c, φ, hφ, fun k hk l => hD _ fun w hw h0 => ?_⟩
  have hΨ' : om (k, 1) Ψ ∈ schA F _ := (IsUWeilPair.isUSplitting hT.weil).pres (k, 1) Ψ hΨ
  have h1 := hw (by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← map_smul, h0, map_zero, Matrix.mul_zero, Matrix.zero_mul]) k hk
  have h2 := he.Heisenberg₂ (G₁.M.co.e.symm w) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ (shiftA H H' l) _ hΨ')
  rw [GlobalTheory.XTermFinParts.rho_comm G.M.co B.ψ (by rw [Matrix.mul_assoc]; exact GlobalTheory.XTermFinParts.symp_eq_zero hC.hH _ _ _ _),
    h1, show G₁.M.co.rho B.ψ (G₁.M.co.e.symm w) = schr B.ψ w from
      congrArg (schr B.ψ) (G₁.M.co.e.apply_symm_apply w)] at h2
  exact h2.symm

section Arch

open GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay

theorem arch_decay_of_compact {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'}
    {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')} (hC : CfgA B G G₁ H H')
    {e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    {Ψ : Fn F (b + 2) (b + 2 + a')} (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')))
    {C : Set (UA σ G.V.J)} (hCc : IsCompact C)
    {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) (c : Fin b × Fin (b + a') → Af F) (N : ℕ)
    (s : Finset (ℕ × ℕ)) :
    ∃ D : ℝ, ∀ k ∈ C, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
      ∃ f : SInf F (Fin b × Fin (b + a')), (∀ y, f y = e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ))
          (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c q))) ∧
        (s.sup (schwartzSeminormFamily ℂ _ ℂ)) f ≤
          D * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun k : C => om (k.1, 1) Ψ)
    (fun k => hw.isUSplitting.pres (k.1, 1) Ψ hΨ) fun l hl => by
      have hc := (hw.2.2 l hl Ψ hΨ).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V.J => (g, (1 : UA σ G.W.J)))
      obtain ⟨D, hD⟩ := hCc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨D, fun k => hD k.1 k.2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by
    rw [form_swap hT.base.cm hT.geo.hW.skew, hC.hH'.xy, map_one])
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U' := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x))
  have hp : Continuous ⇑(Finset.sup s (schwartzSeminormFamily ℂ (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) ℂ)) :=
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  choose D₀ hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) (hg j) (f j) (hf j) hU _ hp N
  refine ⟨∑ j, D₀ j, fun k hk l hl => ?_⟩
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ (GlobalTheory.XTermMaj.crd F E (l : AE F E)) hl
  have hS : G.M.co.e (shiftA H H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := by
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
    exact (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans (Finset.sum_le_sum fun j _ => hb₁ j)

end Arch

theorem two_le_exp {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} (h : G.IsGood B) : 2 ≤ (b + 2 - a') / 2 := by
  obtain ⟨k, hk⟩ := h.even
  have h1 := h.lt
  have h2 := h.eBig
  omega

theorem dom : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure → ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ C : Set (UA σ G.V.J), IsCompact C →
      ∀ y₀ : Fin b × Fin (b + a') → AF F, ∃ U ∈ 𝓝 y₀, ∃ Gf : (AE F E)ˣ → ℝ, Integrable Gf μ ∧ ∀ k ∈ C, ∀ (l : (AE F E)ˣ), ∀ y ∈ U,
        ‖e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) y‖ * (absE F E l : ℝ) ^ ((b + 2 - a') / 2) ≤ Gf l := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ μ hμ Ψ hΨ C hCc y₀
  haveI := hμ
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨U, hU, hUz⟩ := finsupp_of_compact hC he hT hΨ hCc
  have hn : 2 ≤ (b + 2 - a') / 2 := two_le_exp hT.geo
  have hs : (1 : ℝ) < (((b + 2 - a') / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < (b + 2 - a') / 2)
  obtain ⟨N, k₀, L, C₁, hk₀, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  have hfin := GlobalTheory.TateConv.lintegral_bound_lt_top F E μ hs hk₀ L C₁
  obtain ⟨m, c, φ, hφ, hdec⟩ := finite_parts_of_compact hC he hT hΨ hCc
  choose D hD using fun j => arch_decay_of_compact hC he hT hΨ hCc hU (c j) N {(0, 0)}
  have hφb : ∀ j, ∃ M : ℝ, ∀ z, ‖φ j z‖ ≤ M := fun j =>
    (hφ j).1.continuous.bounded_above_of_compact_support (hφ j).2
  choose Mφ hMφ using hφb
  set C₀ : ℝ := ∑ j, |D j| * |Mφ j| with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun j _ => by positivity
  set g : (AE F E)ˣ → ENNReal := fun l => GlobalTheory.XTermMaj.maj F E N U (l : AE F E) *
    ENNReal.ofReal ((absE F E l : ℝ) ^ ((((b + 2 - a') / 2 : ℕ) : ℝ))) with hg
  refine ⟨Set.univ, Filter.univ_mem, fun l => C₀ * (g l).toReal, ?_, fun k hk l y _ => ?_⟩
  · refine Integrable.const_mul ?_ C₀
    refine integrable_toReal_of_lintegral_ne_top ?_ (lt_of_le_of_lt (lintegral_mono hb) hfin).ne
    have hcrd : Continuous fun l : (AE F E)ˣ => GlobalTheory.XTermMaj.crd F E (l : AE F E) :=
      (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap).comp Units.continuous_val
    have hfp : Continuous fun l : (AE F E)ˣ => fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2 :=
      continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp hcrd)
    have hval : Continuous fun l : (AE F E)ˣ =>
        (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
      refine Continuous.rpow_const ?_ fun l => Or.inl (by positivity)
      refine continuous_const.add (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun v _ => ?_)
      exact continuous_norm.comp ((continuous_apply v).comp (continuous_fst.comp ((continuous_apply i).comp hcrd)))
    have hm : Measurable fun l : (AE F E)ˣ => GlobalTheory.XTermMaj.maj F E N U (l : AE F E) := by
      have e1 : (fun l : (AE F E)ˣ => GlobalTheory.XTermMaj.maj F E N U (l : AE F E)) =
          ((fun l : (AE F E)ˣ => fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ⁻¹' U).indicator
            (fun l => ENNReal.ofReal
              ((1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)))) := by
        funext l
        simp only [GlobalTheory.XTermMaj.maj, Set.indicator_apply, Set.mem_preimage]
      rw [e1]
      exact (ENNReal.measurable_ofReal.comp hval.measurable).indicator (hU.isClosed.preimage hfp).measurableSet
    have ha : Measurable fun l : (AE F E)ˣ =>
        ENNReal.ofReal ((absE F E l : ℝ) ^ ((((b + 2 - a') / 2 : ℕ) : ℝ))) :=
      ENNReal.measurable_ofReal.comp ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).rpow_const
        fun _ => Or.inr (by positivity)).measurable
    exact (hm.mul ha).aemeasurable
  · have hA : 0 ≤ (absE F E l : ℝ) ^ ((b + 2 - a') / 2) := by positivity
    have hgl : (g l).toReal = (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal * (absE F E l : ℝ) ^ ((b + 2 - a') / 2) := by
      rw [hg, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), Real.rpow_natCast]
    show _ ≤ C₀ * (g l).toReal
    rw [hgl]
    by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
    · set P : ℝ := (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) with hP
      have hP0 : 0 ≤ P := by positivity
      have hmaj : (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal = P := by
        rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, ENNReal.toReal_ofReal hP0]
      rw [hmaj, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hA
      rw [hdec k hk l y]
      refine (norm_sum_le _ _).trans ?_
      rw [hC₀, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      obtain ⟨f, hf1, hf2⟩ := hD j k hk l hl
      have hz := hf1 fun q => InfiniteAdeleRing.ringEquiv_mixedSpace F (y q).1
      simp only [RingEquiv.symm_apply_apply] at hz
      have h1 : ‖e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ)) (fun q => ((y q).1, c j q))‖ ≤ |D j| * P := by
        rw [← hz]
        refine (SchwartzMap.norm_le_seminorm ℂ f _).trans ?_
        rw [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] at hf2
        exact hf2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
      rw [norm_mul]
      calc _ ≤ (|D j| * P) * |Mφ j| :=
            mul_le_mul h1 ((hMφ j _).trans (le_abs_self _)) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [hUz k hk l hl]
      simp only [map_zero, Pi.zero_apply, norm_zero, zero_mul]
      exact mul_nonneg hC₀0 (mul_nonneg ENNReal.toReal_nonneg hA)

end GlobalTheory.ConeDom

end
