import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoDecayOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace UpperTheory.SoBound
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

private def mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : AF F :=
  (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) b : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

private theorem evI_mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : evI F (mkA a b) = a := by
  simp [evI, mkA]

private theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : (κ → Af F) → ℂ) :
    pureA F f (a + b) = pureA F f a + pureA F f b := by
  funext x; simp [pureA, mul_add]

private theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (a : (κ → Af F) → ℂ) :
    pureA F f (c • a) = c • pureA F f a := by
  funext x; simp [pureA]; ring

private theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 := by
  funext x; simp [pureA]

private theorem pureA_mkA {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a : (κ → Af F) → ℂ)
    (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : pureA F f a (fun i => mkA (y i) (z i)) = f y * a z := by
  simp only [pureA]
  congr 1
  congr 1
  funext i
  exact evI_mkA (y i) (z i)

private theorem thetaSum_finset_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ i ∈ s, Φ i ∈ schA F κ) : thetaSum F (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaSum F (Φ i) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (h a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end UpperTheory.SoBound

end

open GlobalTheory.ThKSoDecay UpperTheory.SoBound in
theorem UpperTheory.theta_schwartz_bruhat_bound :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
                 (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
                 ∀ (m : ℕ) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ), (∀ j, φ j ∈ SB (Fin n × Fin d → Af F)) →
                 ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ → ∀ g h,
                   ‖theta om (∑ j, pureA F (w j) (φ j)) g h‖ ≤ C * (∑ j, GlobalTheory.ThKSoDecay.semK (Fin n × Fin d) k (w j)) * (ht h : ℝ) ^ k := by
  classical
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair m φ hφ
  have hU := soDecayUnif hP F E σ B n d X W M χX χW om r s r' s' hPair
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    hPair.weil.isUSplitting.pres
  let So := M.So B.ψ B.τ₁
  let T' : Submodule ℂ ((Fin n × Fin d → Af F) → ℂ) :=
    { carrier := {a | ∀ g : SInf F (Fin n × Fin d), pureA F g a ∈ So}
      add_mem' := fun ha hb g => by rw [pureA_add]; exact So.add_mem (ha g) (hb g)
      zero_mem' := fun g => by rw [pureA_zero]; exact So.zero_mem
      smul_mem' := fun c a ha g => by rw [pureA_smul]; exact So.smul_mem c (ha g) }
  let T := SB (Fin n × Fin d → Af F) ⊓ T'
  have hslice : ∀ Φ ∈ So, ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      (fun z : Fin n × Fin d → Af F => Φ (fun i => mkA (y i) (z i))) ∈ T' := by
    intro Φ hΦ y
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, ψ, h1, h2, h3, rfl⟩ := hΦ
      let a : (Fin n × Fin d → Af F) → ℂ := fun z => ∏ᶠ v, ψ v fun i => evFin F v (mkA 0 (z i))
      have e1 : (fun z : Fin n × Fin d → Af F => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g ψ (fun i => mkA (y i) (z i))) = g y • a := by
        funext z
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, a]
        congr 1
        congr 1
        funext i
        exact evI_mkA (y i) (z i)
      have e2 : ∀ g' : SInf F (Fin n × Fin d), pureA F g' a = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' ψ := fun g' => by
        funext x
        rfl
      rw [e1]
      refine T'.smul_mem _ fun g' => ?_
      rw [e2]
      exact Submodule.subset_span ⟨g', ψ, h1, h2, h3, rfl⟩
    | zero =>
      have e0 : (fun z : Fin n × Fin d → Af F => (0 : (Fin n × Fin d → AF F) → ℂ) (fun i => mkA (y i) (z i))) = 0 := rfl
      rw [e0]
      exact T'.zero_mem
    | add Φ Ψ _ _ hΦ hΨ => exact T'.add_mem hΦ hΨ
    | smul c Φ _ hΦ => exact T'.smul_mem c hΦ
  obtain ⟨Cm, hC⟩ := Submodule.exists_isCompl T
  have hdec : ∀ j, ∃ t ∈ T, ∃ c ∈ Cm, t + c = φ j := fun j =>
    Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top)
  choose t htT c hcC htc using hdec
  have hcSB : ∀ j, c j ∈ SB (Fin n × Fin d → Af F) := fun j => by
    have : c j = φ j - t j := by rw [← htc j]; abel
    rw [this]; exact Submodule.sub_mem _ (hφ j) (htT j).1
  have hred : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) := by
    intro w hw
    have e : ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) + ∑ j, pureA F (w j) (c j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← pureA_add, htc j]
    have hΨ : ∑ j, pureA F (w j) (c j) ∈ So := by
      have : ∑ j, pureA F (w j) (c j) = ∑ j, pureA F (w j) (φ j) - ∑ j, pureA F (w j) (t j) := by
        rw [e]; abel
      rw [this]
      exact So.sub_mem hw (So.sum_mem fun j _ => (htT j).2 (w j))
    have h0 : ∀ y, ∑ j, w j y • c j = 0 := by
      intro y
      have h1 : ∑ j, w j y • c j ∈ T := by
        refine ⟨SB _ |>.sum_mem fun j _ => (SB _).smul_mem _ (hcSB j), ?_⟩
        have := hslice _ hΨ y
        have e' : (fun z : Fin n × Fin d → Af F => (∑ j, pureA F (w j) (c j)) (fun i => mkA (y i) (z i))) =
            ∑ j, w j y • c j := by
          funext z
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureA_mkA]
        rwa [e'] at this
      have h2 : ∑ j, w j y • c j ∈ Cm := Cm.sum_mem fun j _ => Cm.smul_mem _ (hcC j)
      have := hC.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨h1, h2⟩)
      exact (Submodule.mem_bot ℂ).1 this
    rw [e, add_eq_left]
    funext x
    have := congrFun (h0 fun i => evI F (x i)) (fun i => (x i).2)
    simpa [pureA, Finset.sum_apply, evI] using this
  have hmem : ∀ (a : (Fin n × Fin d → Af F) → ℂ), a ∈ SB (Fin n × Fin d → Af F) → ∀ g : SInf F (Fin n × Fin d),
      pureA F g a ∈ schA F (Fin n × Fin d) := fun a ha g => Submodule.subset_span ⟨g, a, ha, rfl⟩
  have hbd : ∀ j, ∃ (C0 : ℝ) (k0 : ℕ), 0 ≤ C0 ∧ ∀ (g : SInf F (Fin n × Fin d)) x h,
      ‖theta om (pureA F g (t j)) x h‖ ≤ C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0 := by
    intro j
    obtain ⟨C0, k0, hC0⟩ := hU (t j) (htT j).1 (htT j).2 0
    refine ⟨max C0 0, k0, le_max_right _ _, fun g x h => ?_⟩
    have hh : (0 : ℝ) ≤ (ht h : ℝ) ^ k0 := pow_nonneg (NNReal.coe_nonneg _) _
    have := hC0 g x h
    rw [pow_zero, mul_one] at this
    refine this.trans ?_
    have hs : 0 ≤ semK (Fin n × Fin d) k0 g := apply_nonneg _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hs) hh
  choose C k hC0 hCb using hbd
  refine ⟨∑ j, C j, Finset.univ.sup k, Finset.sum_nonneg fun j _ => hC0 j, fun w hw x h => ?_⟩
  rw [hred w hw]
  have e : theta om (∑ j, pureA F (w j) (t j)) x h = ∑ j, theta om (pureA F (w j) (t j)) x h := by
    simp only [theta]
    rw [map_sum]
    exact thetaSum_finset_sum _ _ fun j _ => hpres _ _ (hmem _ (htT j).1 (w j))
  rw [e, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (hCb j (w j) x h).trans ?_)
  have hk : k j ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ j)
  have hle' : semK (F := F) (Fin n × Fin d) (k j) ≤ semK (F := F) (Fin n × Fin d) (Finset.univ.sup k) :=
    Finset.sup_mono (Finset.Iic_subset_Iic.2 (Prod.mk_le_mk.2 ⟨hk, hk⟩))
  have hCj : C j ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ j)
  have hh : (1 : ℝ) ≤ (ht h : ℝ) := GlobalTheory.ThKSoSpan.one_le_ht h
  have hS : 0 ≤ ∑ i, C i := (hC0 j).trans hCj
  exact mul_le_mul (mul_le_mul hCj (hle' (w j)) (apply_nonneg _ _) hS) (pow_le_pow_right₀ hh hk)
    (pow_nonneg (zero_le_one.trans hh) _) (mul_nonneg hS (apply_nonneg _ _))
