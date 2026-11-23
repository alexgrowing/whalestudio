import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedGeneratedByKFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactRightInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralSupportSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingOpenSubgroupStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open Topology GlobalTheory.SplitWeil

theorem fibInt_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (f : cIndSpace (HPG k i t) (hRep τ σ)) (x g : GL (Fin (i + t)) k), fibInt μ (prodPG τ σ (levi k (i + t) x) f) g = fibInt μ f (g * x) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ f x g
  have h : fibV (prodPG τ σ (levi k (i + t) x) f) g = fibV f (g * x) := funext fun v =>
    congrArg f.1.1.1 (show uM k (i + t) (midV k i t v) * levi k (i + t) g * levi k (i + t) x =
      uM k (i + t) (midV k i t v) * levi k (i + t) (g * x) by rw [map_mul, mul_assoc])
  exact congrArg (fun φ => clT τ W (smInt μ φ)) h

theorem fibInt_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (g : GL (Fin (i + t)) k), (∀ f₁ f₂ : cIndSpace (HPG k i t) (hRep τ σ), fibInt μ (f₁ + f₂) g = fibInt μ f₁ g + fibInt μ f₂ g) ∧ ∀ (a : ℂ) (f : cIndSpace (HPG k i t) (hRep τ σ)), fibInt μ (a • f) g = a • fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ g
  have hr := fun f => GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hp := SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ
  refine ⟨fun f₁ f₂ => ?_, fun a f => ?_⟩
  · have h : smInt μ (fibV (f₁ + f₂) g) = smInt μ (fibV f₁ g) + smInt μ (fibV f₂ g) :=
      hp.1 (fibV f₁ g) (fibV f₂ g) (hr f₁).1 (hr f₁).2 (hr f₂).1 (hr f₂).2
    exact (congrArg (clT τ W) h).trans (map_add _ _ _)
  · have e : fibV (a • f) g = (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) ∘ fibV f g :=
      funext fun v => map_smul (evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) g)) a f
    have h1 := hp.2.1 (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) (fibV f g) (hr f).1 (hr f).2
    have h : smInt μ (fibV (a • f) g) = a • smInt μ (fibV f g) := (congrArg (smInt μ) e).trans h1
    exact (congrArg (clT τ W) h).trans (map_smul _ _ _)

theorem exists_nhds_prod {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X → Y → Z) (hF : Continuous fun p : X × Y => F p.1 p.2) (x : X) (y : Y) {U : Set Z} (hU : U ∈ 𝓝 (F x y)) :
    ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ a ∈ A, ∀ b ∈ B, F a b ∈ U := by
  have h : (fun p : X × Y => F p.1 p.2) ⁻¹' U ∈ 𝓝 (x, y) := hF.continuousAt.preimage_mem_nhds hU
  rw [nhds_prod_eq, Filter.mem_prod_iff] at h
  obtain ⟨A, hA, B, hB, hsub⟩ := h
  exact ⟨A, hA, B, hB, fun a ha b hb => hsub (Set.mk_mem_prod ha hb)⟩

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_latt_nhds {n : ℕ} {U : Set (Mir k n)} (hU : U ∈ 𝓝 (1 : Mir k n)) :
    ∃ c : kˣ, ∃ A ∈ 𝓝 (1 : GL (Fin n) k), ∀ y ∈ latt n c, ∀ b ∈ A, uM k n y * levi k n b ∈ U := by
  have hc := GlobalTheory.T.continuous_levi_unipotent_proj k n
  have hcont : Continuous fun p : (Fin n → k) × GL (Fin n) k => uM k n p.1 * levi k n p.2 :=
    (hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd)
  have h00 : uM k n 0 * levi k n 1 = 1 := by rw [uM_zero, map_one, one_mul]
  obtain ⟨A, hA, B, hB, h⟩ := exists_nhds_prod (fun y b => uM k n y * levi k n b) hcont 0 1
    (by rw [h00]; exact hU)
  obtain ⟨c, hcA⟩ := exists_latt_subset hA
  exact ⟨c, B, hB, fun y hy b hb => h y (hcA hy) b hb⟩

theorem exists_level {n : ℕ} {Z : Type} (Zs : Set Z) (hZ : Zs.Finite) (U : Z → Set (Mir k n))
    (hU : ∀ z, U z ∈ 𝓝 (1 : Mir k n)) {A' : Set (GL (Fin n) k)} (hA' : A' ∈ 𝓝 (1 : GL (Fin n) k)) :
    ∃ (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (hK : K₁ ≤ KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) ∧
      (K₁ : Set (GL (Fin n) k)) ⊆ A' ∧ K₁.relIndex (KO k (Fin n)) ≠ 0 ∧
      (∀ κ ∈ KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) ∧ ∀ z ∈ Zs, ∀ p ∈ Bgrp n c K₁ hK, p ∈ U z := by
  have hI : (⋂ z ∈ Zs, U z) ∈ 𝓝 (1 : Mir k n) := (Filter.biInter_mem hZ).2 fun z _ => hU z
  obtain ⟨c, A, hA, hcA⟩ := exists_latt_nhds hI
  obtain ⟨K₁, hK, hopen, hsub, hidx, hnorm⟩ := GlobalTheory.T.exists_normal_open_subgroup_compact k n _ (Filter.inter_mem hA hA')
  refine ⟨c, K₁, hK, hopen, fun x hx => (hsub hx).2, hidx, hnorm, ?_⟩
  rintro z hz _ ⟨y, hy, b, hb, rfl⟩
  exact Set.mem_iInter₂.1 (hcA y hy b (hsub hb).1) z hz

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] (GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W) where
  toFun f := fun g => fibInt μ f g
  map_add' f₁ f₂ := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).1 f₁ f₂
  map_smul' a f := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).2 a f

theorem clT_surjective (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Function.Surjective (clT τ W) :=
  LinearMap.rTensor_surjective W (Submodule.mkQ_surjective _)

theorem exists_bump_fib (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ b : cIndSpace (HPG k i t) (hRep τ σ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, fibInt μ b ((q : GL (Fin (i + t)) k) * b') =
        (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • qRep τ σ q (clT τ W z)) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  have hBo := GlobalTheory.T.fibre_subgroup_open_compact k (i + t) c K₁ hK hopen
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.T.exists_induced_section_supported_open (HPG k i t) (hRep τ σ) (Bgrp (i + t) c K₁ hK) hBo.1 hBo.2 z hz
  have hone : fibInt μ b 1 = (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • clT τ W z := by
    have h1 := GlobalTheory.T.fibre_integral_vanishing_subgroup k i t τ σ c K₁ hK z b hb1 hb2
    have h2 := (SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).2.2.2 _ z (isCompact_latt t c)
      (isOpen_latt t c) (isClosed_latt t c)
    exact (congrArg (fun φ => clT τ W (smInt μ φ)) h1).trans ((congrArg (clT τ W) h2).trans (map_smul _ _ _))
  refine ⟨b, fun q b' hb' => ?_, GlobalTheory.T.fibre_integral_support_subgroup k i t τ σ μ c K₁ hK b hb2⟩
  have e1 : fibInt μ b b' = fibInt μ b 1 := by
    have h := GlobalTheory.T.fibre_integral_vanishing_open_subgroup k i t τ σ c K₁ hK z b hb1 hb2 b' hb' 1
    have h' : fibV b b' = fibV b 1 := (congrArg (fibV b) (one_mul b').symm).trans h
    exact congrArg (fun φ => clT τ W (smInt μ φ)) h'
  exact (GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ b q b').trans
    ((congrArg (qRep τ σ q) (e1.trans hone)).trans (map_smul _ _ _))

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open Topology GlobalTheory.SplitWeil

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem smooth_right_inv {Γ J : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup J] [Module ℂ J]
    (H : Subgroup Γ) (π : Representation ℂ H J) (G : smoothPart (ind H π)) :
    {s : Γ | ∀ x, G.1.1 (x * s) = G.1.1 x} ∈ 𝓝 (1 : Γ) := by
  have h1 : {s : Γ | ind H π s G.1 = G.1} ∈ 𝓝 (1 : Γ) := IsOpen.mem_nhds G.2 (by simp)
  exact Filter.mem_of_superset h1 fun s hs x => congrFun (congrArg Subtype.val hs) x

theorem exists_fib_mem (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W) (a : Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (ha : clT τ W z = a)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ φ ∈ LinearMap.range (fibLin τ σ hτ hσ μ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, φ ((q : GL (Fin (i + t)) k) * b') = qRep τ σ q a) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → φ g = 0 := by
  subst ha
  have hcc0 : (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) ≠ 0 := by
    have h1 : 0 < μ (latt t c : Set (Fin t → k)) := (isOpen_latt t c).measure_pos μ ⟨0, zero_mem _⟩
    have h2 : μ (latt t c : Set (Fin t → k)) ≠ ⊤ := (isCompact_latt t c).measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  refine Exists.elim (exists_bump_fib τ σ hτ hσ μ c K₁ hK hopen z hz) fun b hb => ?_
  refine ⟨(((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • (fibLin τ σ hτ hσ μ b),
    Submodule.smul_mem _ _ ⟨b, rfl⟩, fun q b' hb' => ?_, fun g hg => ?_⟩
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.1 q b' hb')).trans
      (inv_smul_smul₀ hcc0 _)
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.2 g hg)).trans (smul_zero _)

theorem mem_range_fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (Gf : GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (hlaw : ∀ (q : Qp k i t) (g : GL (Fin (i + t)) k), Gf ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (Gf g))
    (hinv : {s : GL (Fin (i + t)) k | ∀ x, Gf (x * s) = Gf x} ∈ 𝓝 (1 : GL (Fin (i + t)) k)) :
    Gf ∈ LinearMap.range (fibLin τ σ hτ hσ μ) := by
  have hfin : (Gf '' (KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite :=
    GlobalTheory.T.finite_image_compact_right_invariant _ GlobalTheory.SplitFlip.isCompact_KO Gf hinv
  obtain ⟨pre, hpre⟩ : ∃ pre : Jacquet τ (MirUin k i) ⊗[ℂ] W → V ⊗[ℂ] W, ∀ a, clT τ W (pre a) = a :=
    ⟨Function.surjInv (clT_surjective τ W), Function.surjInv_eq _⟩
  choose Ust hUst hUfix using GlobalTheory.T.smooth_tensor_fixed_parabolic_near_one k i t τ σ hτ hσ
  obtain ⟨c, K₁, hK, hopen, hsub, hidx, hnorm, hlev⟩ := exists_level _ (hfin.image pre) Ust hUst hinv
  have hfix : ∀ κ ∈ KO k (Fin (i + t)), ∀ h : HPG k i t,
      (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h (pre (Gf κ)) = pre (Gf κ) :=
    fun κ hκ h hh => hUfix _ h (hlev _ ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩ _ hh)
  refine GlobalTheory.T.induced_generated_by_K_finite (Qp k i t) (KO k (Fin (i + t))) K₁ (qRep τ σ) (LinearMap.range (fibLin τ σ hτ hσ μ)) Gf hK hidx hnorm
    (fun g => ?_) ?_ ?_ hlaw (fun g b hb => hsub hb g) ?_
  · obtain ⟨q, κ, hκ, e⟩ := GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact k i t g
    exact ⟨q, κ, hκ, e⟩
  · rintro _ ⟨f, rfl⟩ x
    exact ⟨prodPG τ σ (levi k (i + t) x) f, funext fun g => fibInt_translate k i t τ σ μ f x g⟩
  · rintro _ ⟨f, rfl⟩ q g
    exact GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ f q g
  · intro κ hκ
    exact exists_fib_mem τ σ hτ hσ μ c K₁ hK hopen (pre (Gf κ)) (Gf κ) (hpre _) (hfix κ hκ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG

open Topology GlobalTheory.SplitWeil FibOnto

theorem exists_fibInt_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ G : smoothPart (ind (Qp k i t) (qRep τ σ)), ∃ f : cIndSpace (HPG k i t) (hRep τ σ), ∀ g, fibInt μ f g = G.1.1 g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ G
  have hM := mem_range_fibLin τ σ hτ hσ μ G.1.1 G.1.2 (smooth_right_inv _ _ G)
  exact ⟨Classical.choose hM, fun g => congrFun (Classical.choose_spec hM) g⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
