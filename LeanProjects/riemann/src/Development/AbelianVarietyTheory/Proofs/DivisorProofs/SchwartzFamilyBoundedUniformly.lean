import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoDecayOfUnif

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaUnifWeight

open GlobalTheory.HeisSchA GlobalTheory.XTermDecay GlobalTheory.DiffDecay GlobalTheory.ThKSoDecay

section Decomp

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_decomp_linear {T : Type} (Ψ : T → (κ → AF F) → ℂ) (hΨ : ∀ t, Ψ t ∈ schA F κ)
    (hb : ∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) (S : Submodule ℂ ((κ → Af F) → ℂ))
    (hS : ∀ t (y : κ → mixedEmbedding.mixedSpace F),
      (fun z : κ → Af F => Ψ t fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (z i)) ∈ S) :
    ∃ (m : ℕ) (g : Fin m → (κ → Af F) → ℂ) (A : Fin m → ((κ → AF F) → ℂ) →ₗ[ℂ] SInf F κ), (∀ j, g j ∈ S) ∧
      (∀ t, Ψ t = ∑ j, pureA F (A j (Ψ t)) (g j)) ∧
      ∀ j (l : SInf F κ →L[ℂ] ℂ), l.toLinearMap ∘ₗ A j ∈ (adeleClass F).adm κ := by
  obtain ⟨W, hW, hsl⟩ := GlobalTheory.T.schwartz_family_finite_dim_span F κ T Ψ hΨ hb
  let W' : Submodule ℂ ((κ → Af F) → ℂ) := W ⊓ S
  haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_left
  let b := Module.finBasis ℂ W'
  choose β hβ using fun j => LinearMap.exists_extend (b.coord j)
  obtain ⟨r, hr⟩ := (coeL (F := F) (κ := κ)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
  have hr' : ∀ f, r (coeL f) = f := fun f => LinearMap.congr_fun hr f
  refine ⟨_, fun j => b j, fun j => r ∘ₗ coefFun (β j), fun j => (b j).2.2, fun t => ?_, fun j l => ?_⟩
  · funext x
    let y : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
    let s : W' := ⟨_, hsl t _, hS t y⟩
    have h1 := congrFun (congrArg Subtype.val (b.sum_repr s)) fun i => (x i).2
    have h2 : ∀ j, r (coefFun (β j) (Ψ t)) y = b.repr s j := fun j => by
      obtain ⟨f, hf⟩ := coefFun_mem (β j) _ (hΨ t)
      rw [← hf, hr']
      exact (congrFun hf y).trans (LinearMap.congr_fun (hβ j) s)
    have h3 : (s : (κ → Af F) → ℂ) (fun i => (x i).2) = Ψ t x := by
      simp only [s, y, RingEquiv.symm_apply_apply]
      rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [Finset.sum_apply]
    refine (h1.trans h3).symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← h2 j]
    rfl
  · refine fun g _ => ⟨β j g • l, fun f => ?_⟩
    simp only [LinearMap.comp_apply, coefFun_pureA, hr', map_smul]
    rfl

def finPart (V : Submodule ℂ ((κ → AF F) → ℂ)) : Submodule ℂ ((κ → Af F) → ℂ) where
  carrier := {φ | ∀ f : SInf F κ, pureA F f φ ∈ V}
  add_mem' := fun {a b} ha hb f => by
    have : pureA F f (a + b) = pureA F f a + pureA F f b := funext fun _ => mul_add _ _ _
    rw [this]
    exact V.add_mem (ha f) (hb f)
  zero_mem' := fun f => by
    have : pureA F f (0 : (κ → Af F) → ℂ) = 0 := funext fun _ => mul_zero _
    rw [this]
    exact V.zero_mem
  smul_mem' := fun c a ha f => by
    have : pureA F f (c • a) = c • pureA F f a := funext fun _ => mul_left_comm _ _ _
    rw [this]
    exact V.smul_mem c (ha f)

end Decomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem slice_mem_finPart {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) : ∀ Φ ∈ M.So B.ψ B.τ₁,
    (fun z : Fin n × Fin d → Af F => Φ fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (z i)) ∈
      finPart (M.So B.ψ B.τ₁) := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, h1, h2, h3, rfl⟩ := hx
    have hall : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈
        finPart (M.So B.ψ B.τ₁) := fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩
    have e := slice_pureA (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) y
    exact e ▸ Submodule.smul_mem _ _ hall
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem theta_unif_weight : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (T : Type) (Ψ : T → Fn F n d), (∀ t, Ψ t ∈ M.So B.ψ B.τ₁) →
    (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) →
    ∃ k : ℕ, ∀ w : T → ℝ, (∀ t, 0 ≤ w t) → (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), ∃ C : ℝ, ∀ t, w t * ‖l (Ψ t)‖ ≤ C) →
      ∃ C : ℝ, ∀ t g h, w t * ‖theta om (Ψ t) g h‖ ≤ C * (ht h : ℝ) ^ k := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair T Ψ hΨ hb
  have hS := hPair.weil.isUSplitting
  obtain ⟨l, -, hlt⟩ := GlobalTheory.T.exists_admissibleForm_adelicThetaSum F (Fin n × Fin d)
  have hsch : M.So B.ψ B.τ₁ ≤ schA F (Fin n × Fin d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    have h3 := (h2.and hPair.good.std).mono fun w hw => hw.1.trans hw.2
    exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩
  have hlin : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ g h, theta om Ψ g h = l (om (g, h) Ψ) :=
    fun Ψ hΨ g h => (hlt _ (hS.pres _ _ hΨ)).symm
  obtain ⟨m, φ, A, hφ, hdec, hA⟩ := exists_decomp_linear Ψ (fun t => hsch (hΨ t)) hb (SB _ ⊓ finPart (M.So B.ψ B.τ₁))
    fun t y => ⟨slice_mem_SB y _ (hsch (hΨ t)), slice_mem_finPart M y _ (hΨ t)⟩
  choose C k hC using fun j => soDecayUnif hP F E σ B n d X W M χX χW om r s r' s' hPair (φ j) (hφ j).1 (hφ j).2 0
  refine ⟨Finset.univ.sup k, fun w hw hwb => ?_⟩
  have hsem : ∀ j, ∃ D : ℝ, ∀ t, w t * semK (Fin n × Fin d) (k j) (A j (Ψ t)) ≤ D := fun j => by
    obtain ⟨D, hD⟩ := bounded_of_weak (fun t => (w t : ℂ) • A j (Ψ t)) (fun l' => by
      obtain ⟨D, hD⟩ := hwb _ (hA j l')
      refine ⟨D, fun t => ?_⟩
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hw t)]
      exact hD t) (semK (Fin n × Fin d) (k j))
      (Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i)
    refine ⟨D, fun t => ?_⟩
    have := hD t
    rwa [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (hw t)] at this
  choose D hD using hsem
  refine ⟨∑ j, |C j| * |D j|, fun t g h => ?_⟩
  have hh := GlobalTheory.ThKSoSpan.one_le_ht h
  have e : theta om (Ψ t) g h = ∑ j, theta om (pureA F (A j (Ψ t)) (φ j)) g h := by
    rw [hlin _ (hsch (hΨ t))]
    conv_lhs => rw [hdec t]
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => (hlin _ (hsch ((hφ j).2 _)) g h).symm
  rw [e, Finset.sum_mul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw t)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := hC j (A j (Ψ t)) g h
  rw [pow_zero, mul_one] at h1
  have h0 : 0 ≤ semK (Fin n × Fin d) (k j) (A j (Ψ t)) := apply_nonneg _ _
  have hk : (ht h : ℝ) ^ k j ≤ (ht h : ℝ) ^ Finset.univ.sup k := pow_le_pow_right₀ hh (Finset.le_sup (Finset.mem_univ j))
  have hwt := hw t
  calc _ ≤ w t * (|C j| * semK (Fin n × Fin d) (k j) (A j (Ψ t)) * (ht h : ℝ) ^ k j) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hwt
        gcongr
        exact le_abs_self _
    _ = |C j| * (w t * semK (Fin n × Fin d) (k j) (A j (Ψ t))) * (ht h : ℝ) ^ k j := by ring
    _ ≤ _ := by
        gcongr
        exact (hD j t).trans (le_abs_self _)

end GlobalTheory.ThetaUnifWeight

end
