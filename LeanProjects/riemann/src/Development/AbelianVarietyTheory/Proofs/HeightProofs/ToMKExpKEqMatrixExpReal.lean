import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

section MatrixExtension

open scoped Matrix.Norms.Operator

def mxDer (X : Mx n) (F : Mx n → ℂ) : Mx n → ℂ := fun M => fderiv ℝ F M (M * X)

def mxDerW (l : List (Mx n)) (F : Mx n → ℂ) : Mx n → ℂ :=
  l.foldr (fun X G => mxDer X G) F

theorem contDiff_mxDer (X : Mx n) {F : Mx n → ℂ} (hF : ContDiff ℝ ⊤ F) : ContDiff ℝ ⊤ (mxDer X F) := by
  unfold mxDer
  exact (hF.fderiv_right le_top).clm_apply (contDiff_id.mul contDiff_const)

theorem contDiff_mxDerW (l : List (Mx n)) {F : Mx n → ℂ} (hF : ContDiff ℝ ⊤ F) :
    ContDiff ℝ ⊤ (mxDerW l F) := by
  induction l with
  | nil => exact hF
  | cons X l ih => exact contDiff_mxDer X ih

theorem hasDerivAt_exp_ofReal_smul (X : Mx n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = fun t : ℝ => NormedSpace.exp (t • X) := by
    funext t; rw [Complex.coe_smul]
  rw [e]; exact h

theorem rder_eq_mxDerW {ε : Fin n → Bool} (l : List (Mx n)) (hl : ∀ X ∈ l, inK ε X) {F : Mx n → ℂ}
    (hF : ContDiff ℝ ⊤ F) {φ : KG ε → ℂ} (hφ : ∀ k, φ k = F (toMK k)) (k : KG ε) :
    rder ε l φ k = mxDerW l F (toMK k) := by
  induction l generalizing k with
  | nil => exact hφ k
  | cons X l ih =>
    have hX : inK ε X := hl X List.mem_cons_self
    have hl' : ∀ Y ∈ l, inK ε Y := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    rw [rder_cons]
    have e : (fun t : ℝ => rder ε l φ (k * expK ε X t)) =
        (mxDerW l F) ∘ (fun t : ℝ => toMK k * NormedSpace.exp ((t : ℂ) • X)) := by
      funext t
      simp only [Function.comp, ih hl' (k * expK ε X t), toMK_mul, toMK_expK hX]
    rw [e]
    have hd : HasDerivAt (fun t : ℝ => toMK k * NormedSpace.exp ((t : ℂ) • X)) (toMK k * X) 0 :=
      (hasDerivAt_exp_ofReal_smul X).const_mul (toMK k)
    have hF' := ((contDiff_mxDerW l hF).differentiable (by simp)) (toMK k)
    have h2 := hF'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd (by simp [NormedSpace.exp_zero])
    rw [h2.deriv]
    rfl

def mxCoord (c : Fin n × Fin n × Bool) (M : Mx n) : ℂ :=
  if c.2.2 then M c.1 c.2.1 else star (M c.1 c.2.1)

theorem contDiff_mxCoord (c : Fin n × Fin n × Bool) : ContDiff ℝ ⊤ (mxCoord (n := n) c) := by
  let L : Mx n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ c.1 c.2.1)
  have hL : ContDiff ℝ ⊤ fun M : Mx n => M c.1 c.2.1 := L.contDiff
  unfold mxCoord
  split_ifs
  · exact hL
  · exact (Complex.conjCLE.contDiff.comp hL : _)

theorem exists_ext_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    ∃ F : Mx n → ℂ, ContDiff ℝ ⊤ F ∧ ∀ k, φ k = F (toMK k) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, -, rfl⟩ := hx
    refine ⟨fun M => (s.map fun c => mxCoord c M).prod, ?_, fun k => rfl⟩
    induction s with
    | nil => simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Mx n => (1 : ℂ))
    | cons c s ih => simpa using (contDiff_mxCoord c).mul ih
  | zero => exact ⟨0, contDiff_const, fun k => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, e⟩ := hx
    obtain ⟨G, hG, e'⟩ := hy
    exact ⟨F + G, hF.add hG, fun k => by simp [e, e']⟩
  | smul a x _ hx =>
    obtain ⟨F, hF, e⟩ := hx
    exact ⟨a • F, hF.const_smul a, fun k => by simp [e]⟩

theorem mxDer_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (b : ι → Mx n) (F : Mx n → ℂ) (M : Mx n) :
    mxDer (∑ j ∈ s, c j • b j) F M = ∑ j ∈ s, c j • mxDer (b j) F M := by
  simp only [mxDer, Matrix.mul_sum, Matrix.mul_smul, map_sum, map_smul]

theorem mxDer_sum (X : Mx n) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (G : ι → Mx n → ℂ)
    (hG : ∀ i ∈ s, ContDiff ℝ ⊤ (G i)) :
    mxDer X (fun M => ∑ i ∈ s, c i • G i M) = fun M => ∑ i ∈ s, c i • mxDer X (G i) M := by
  funext M
  have h : HasFDerivAt (fun M => ∑ i ∈ s, c i • G i M) (∑ i ∈ s, c i • fderiv ℝ (G i) M) M :=
    HasFDerivAt.fun_sum fun i hi => ((((hG i hi).differentiable (by simp)) M).hasFDerivAt).const_smul (c i)
  simp only [mxDer, h.fderiv, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]

end MatrixExtension

end GlobalTheory.KFourier

end

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

section Expansion

open scoped Matrix.Norms.Operator

theorem mxDerW_expand {r : ℕ} (b : Fin r → Mx n) (cf : Mx n → Fin r → ℝ) {F : Mx n → ℂ}
    (hF : ContDiff ℝ ⊤ F) : ∀ (k : ℕ) (x : Fin k → Mx n), (∀ i, x i = ∑ j, cf (x i) j • b j) →
    mxDerW (List.ofFn x) F = fun M => ∑ σ : Fin k → Fin r,
      (∏ i, cf (x i) (σ i)) • mxDerW (List.ofFn fun i => b (σ i)) F M := by
  intro k
  induction k with
  | zero =>
    intro x _
    funext M
    simp
  | succ k ih =>
    intro x hx
    have ih' := ih (fun i => x i.succ) (fun i => hx i.succ)
    funext M
    rw [List.ofFn_succ]
    show mxDer (x 0) (mxDerW (List.ofFn fun i => x i.succ) F) M = _
    rw [ih', mxDer_sum (x 0) Finset.univ _ _ (fun σ _ => contDiff_mxDerW _ hF)]
    rw [← (Fin.consEquiv fun _ => Fin r).sum_comp, Fintype.sum_prod_type]
    have hx0 := hx 0
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have key : ∀ G, mxDer (x 0) G M = ∑ j, cf (x 0) j • mxDer (b j) G M := fun G => by
      conv_lhs => rw [hx0]
      exact mxDer_sum_smul _ _ _ _ _
    rw [key, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, mul_comm]
    rfl

end Expansion

end GlobalTheory.KFourier

end

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

section Basis

def kSub (ε : Fin n → Bool) : Submodule ℝ (Mx n) where
  carrier := {X | inK ε X}
  zero_mem' := by
    show inG ε 0 ∧ (0 : Mx n) * Jm ε = Jm ε * 0
    refine ⟨?_, by simp⟩
    show (0 : Mx n)ᴴ * Jm ε + Jm ε * 0 = 0
    simp
  add_mem' := by
    intro X Y hX hY
    obtain ⟨hX1, hX2⟩ := hX
    obtain ⟨hY1, hY2⟩ := hY
    refine ⟨?_, ?_⟩
    · show (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
      have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX1
      have h2 : Yᴴ * Jm ε + Jm ε * Y = 0 := hY1
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
          = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
        _ = 0 := by rw [h1, h2, add_zero]
    · rw [Matrix.add_mul, Matrix.mul_add, hX2, hY2]
  smul_mem' := by
    intro c X hX
    obtain ⟨hX1, hX2⟩ := hX
    refine ⟨?_, ?_⟩
    · show (c • X)ᴴ * Jm ε + Jm ε * (c • X) = 0
      have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX1
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1,
        smul_zero]
    · show (c • X) * Jm ε = Jm ε * (c • X)
      rw [Matrix.smul_mul, Matrix.mul_smul, hX2]

theorem norm_entry_le_of_hs {X : Mx n} (h : hs X ≤ 1) (i j : Fin n) : ‖X i j‖ ≤ 1 := by
  have h1 : ‖X i j‖ ^ 2 ≤ ∑ j', ‖X i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖X i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖X i j'‖ ^ 2 ≤ hs X :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖X i' j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (X i j)]

theorem eq_sum_re_im (X : Mx n) :
    X = ∑ a : Fin n, ∑ b : Fin n, ((X a b).re • (Matrix.single a b (1 : ℂ) : Mx n) +
      (X a b).im • (Matrix.single a b Complex.I : Mx n)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
  congr 1
  rw [Complex.real_smul, Complex.real_smul, mul_one]
  exact (Complex.re_add_im _).symm

theorem abs_linear_le (ψ : Mx n →ₗ[ℝ] ℝ) {X : Mx n} (h : hs X ≤ 1) :
    |ψ X| ≤ ∑ a : Fin n, ∑ b : Fin n, (|ψ (Matrix.single a b (1 : ℂ))| + |ψ (Matrix.single a b Complex.I)|) := by
  conv_lhs => rw [eq_sum_re_im X]
  simp only [map_sum, map_add, map_smul, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have h1 := norm_entry_le_of_hs h a b
  have hre : |(X a b).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h1
  have him : |(X a b).im| ≤ 1 := (Complex.abs_im_le_norm _).trans h1
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have := abs_nonneg (ψ (Matrix.single a b (1 : ℂ)))
  have := abs_nonneg (ψ (Matrix.single a b Complex.I))
  nlinarith [abs_nonneg (X a b).re, abs_nonneg (X a b).im]

theorem exists_basis_kSub (ε : Fin n → Bool) : ∃ (r : ℕ) (b : Fin r → Mx n) (cf : Mx n → Fin r → ℝ) (A : ℝ),
    0 ≤ A ∧ (∀ j, inK ε (b j)) ∧ (∀ X, inK ε X → X = ∑ j, cf X j • b j) ∧
      (∀ X, inK ε X → hs X ≤ 1 → ∀ j, |cf X j| ≤ A) := by
  let B := Module.finBasis ℝ (kSub ε)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (kSub ε).subtype (Submodule.ker_subtype _)
  let ψ : Fin (Module.finrank ℝ (kSub ε)) → (Mx n →ₗ[ℝ] ℝ) := fun j => (B.coord j).comp g
  let A : ℝ := ∑ j, ∑ a : Fin n, ∑ b : Fin n,
    (|ψ j (Matrix.single a b (1 : ℂ))| + |ψ j (Matrix.single a b Complex.I)|)
  have hg' : ∀ X (hX : inK ε X), g X = ⟨X, hX⟩ := fun X hX =>
    LinearMap.congr_fun hg ⟨X, hX⟩
  refine ⟨Module.finrank ℝ (kSub ε), fun j => (B j : Mx n), fun X j => ψ j X, A, ?_, fun j => (B j).2, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      add_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro X hX
    have := congrArg Subtype.val (B.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at this
    simpa [ψ, hg' X hX] using this.symm
  · intro X _ h1 j
    refine (abs_linear_le (ψ j) h1).trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ a : Fin n, ∑ b : Fin n,
      (|ψ j (Matrix.single a b (1 : ℂ))| + |ψ j (Matrix.single a b Complex.I)|))
      (fun j _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)

end Basis

end GlobalTheory.KFourier

end

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

theorem rder_bound_basisWords : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ), ∃ (U : List (List (Mx n))) (C : ℝ),
    0 ≤ C ∧ (∀ u ∈ U, ∀ X ∈ u, inK ε X) ∧ ∀ (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d →
      ∀ w : List (Mx n), w.length ≤ m → (∀ X ∈ w, inK ε X ∧ hs X ≤ 1) →
        ‖GlobalTheory.KFourier.rder ε w φ 1‖ ≤ C * (U.map fun u => ‖GlobalTheory.KFourier.rder ε u φ 1‖).sum := by
  intro n ε m
  obtain ⟨r, b, cf, A, hA, hb, hrep, hcf⟩ := exists_basis_kSub ε
  let word : ∀ k, (Fin k → Fin r) → List (Mx n) := fun k σ => List.ofFn fun i => b (σ i)
  let U : List (List (Mx n)) := (List.range (m + 1)).flatMap fun k =>
    (Finset.univ : Finset (Fin k → Fin r)).toList.map (word k)
  have hword : ∀ k σ, ∀ X ∈ word k σ, inK ε X := by
    intro k σ X hX
    simp only [word, List.mem_ofFn] at hX
    obtain ⟨i, rfl⟩ := hX
    exact hb _
  refine ⟨U, (max 1 A) ^ m, by positivity, ?_, ?_⟩
  · intro u hu X hX
    simp only [U, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨k, -, σ, -, rfl⟩ := hu
    exact hword k σ X hX
  · intro d φ hφ w hw hwK
    obtain ⟨F, hF, hφF⟩ := exists_ext_of_mem hφ
    have hx : ∀ i : Fin w.length, w.get i = ∑ j, cf (w.get i) j • b j := fun i =>
      hrep _ (hwK _ (List.get_mem w i)).1
    have e1 : rder ε w φ 1 = mxDerW w F (toMK 1) :=
      rder_eq_mxDerW w (fun X hX => (hwK X hX).1) hF hφF 1
    have e2 := mxDerW_expand b cf hF w.length w.get hx
    rw [List.ofFn_get] at e2
    have e3 : ∀ k (σ : Fin k → Fin r), mxDerW (word k σ) F (toMK 1) = rder ε (word k σ) φ 1 :=
      fun k σ => (rder_eq_mxDerW _ (hword k σ) hF hφF 1).symm
    have hcoef : ∀ σ : Fin w.length → Fin r, |∏ i, cf (w.get i) (σ i)| ≤ (max 1 A) ^ m := by
      intro σ
      rw [Finset.abs_prod]
      calc ∏ i, |cf (w.get i) (σ i)| ≤ ∏ _i : Fin w.length, max 1 A :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
              (hcf _ (hwK _ (List.get_mem w i)).1 (hwK _ (List.get_mem w i)).2 _).trans (le_max_right _ _)
        _ = (max 1 A) ^ w.length := by simp
        _ ≤ (max 1 A) ^ m := pow_le_pow_right₀ (le_max_left _ _) hw
    have hsum : ∑ σ : Fin w.length → Fin r, ‖rder ε (word w.length σ) φ 1‖ ≤
        (U.map fun u => ‖rder ε u φ 1‖).sum := by
      have e4 : (U.map fun u => ‖rder ε u φ 1‖).sum = ((List.range (m + 1)).map fun k =>
          ∑ σ : Fin k → Fin r, ‖rder ε (word k σ) φ 1‖).sum := by
        simp only [U, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map]
        congr 1
        refine List.map_congr_left fun k _ => ?_
        show ((List.map (word k) Finset.univ.toList).map fun u => ‖rder ε u φ 1‖).sum = _
        rw [List.map_map, Finset.sum_map_toList]
        rfl
      rw [e4]
      exact List.single_le_sum (fun x hx => by
          obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
          exact Finset.sum_nonneg fun _ _ => norm_nonneg _) _
        (List.mem_map.2 ⟨w.length, List.mem_range.2 (by omega), rfl⟩)
    rw [e1, e2]
    calc ‖∑ σ : Fin w.length → Fin r, (∏ i, cf (w.get i) (σ i)) • mxDerW (List.ofFn fun i => b (σ i)) F (toMK 1)‖
        ≤ ∑ σ : Fin w.length → Fin r, ‖(∏ i, cf (w.get i) (σ i)) • mxDerW (List.ofFn fun i => b (σ i)) F (toMK 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ σ : Fin w.length → Fin r, (max 1 A) ^ m * ‖rder ε (word w.length σ) φ 1‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          have := e3 w.length σ
          simp only [word] at this
          rw [this]
          exact mul_le_mul_of_nonneg_right (hcoef σ) (norm_nonneg _)
      _ = (max 1 A) ^ m * ∑ σ : Fin w.length → Fin r, ‖rder ε (word w.length σ) φ 1‖ := by
          rw [Finset.mul_sum]
      _ ≤ (max 1 A) ^ m * (U.map fun u => ‖rder ε u φ 1‖).sum :=
          mul_le_mul_of_nonneg_left hsum (by positivity)

end GlobalTheory.KFourier

end
