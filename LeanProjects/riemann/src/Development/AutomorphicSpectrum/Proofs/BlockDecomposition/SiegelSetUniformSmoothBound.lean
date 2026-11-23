import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLogNearOneUnitaryGroupOfFormLinearBound

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay.Mean

open GlobalTheory.LeviHC GlobalTheory.LeviHC.LineLie GlobalTheory.SmoothForms

section OnePlace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem norm_le_of_entries {X : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i j, ‖X i j‖ ≤ r) :
    ‖X‖ ≤ n * r := by
  have key : ‖X‖₊ ≤ (n : ℝ≥0) * r.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖X i j‖₊ ≤ ∑ _j : Fin n, r.toNNReal :=
          Finset.sum_le_sum fun j _ => by
            rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hr]
            exact h i j
      _ = (n : ℝ≥0) * r.toNNReal := by simp
  have key' := NNReal.coe_le_coe.mpr key
  simpa [Real.coe_toNNReal _ hr] using key'

theorem expMap_zero (h : IsCMExt F E σ) (τ : EmbOver E w) :
    expMap (jA (J.map τ.1)) (secA σ J τ) 0 = 1 := by
  show secA σ J τ (NormedSpace.exp ((jA (J.map τ.1)) 0)) = 1
  rw [map_zero, NormedSpace.exp_zero, ← map_one (archMat σ J τ), secA_archMat h, map_one]

theorem expMap_add (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Z : LieL (J.map τ.1)) (s t : ℝ) :
    expMap (jA (J.map τ.1)) (secA σ J τ) ((s + t) • Z) =
      expMap (jA (J.map τ.1)) (secA σ J τ) (s • Z) * expMap (jA (J.map τ.1)) (secA σ J τ) (t • Z) := by
  obtain ⟨y1, e1, a1⟩ := isLineOf_expMap h hJ τ Z s
  obtain ⟨y2, e2, a2⟩ := isLineOf_expMap h hJ τ Z t
  obtain ⟨y3, e3, a3⟩ := isLineOf_expMap h hJ τ Z (s + t)
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply archMat_injective h τ
  rw [map_mul, a1, a2, a3, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t)

theorem one_place (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → ℝ → GAd σ J) (K : Set (GArch σ J w)) (C δ₁ : ℝ),
      (∀ i, IsRealLine σ J (b i)) ∧ IsCompact K ∧ 1 ∈ K ∧ 0 < δ₁ ∧ 0 ≤ C ∧
      ∀ (y : GArch σ J w) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → (∀ i j, ‖(archMat σ J τ y - 1) i j‖ ≤ δ) →
        y ∈ K ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g : GAd σ J) (c : ι → ℝ),
          (∀ i, ∀ x ∈ K, ‖lineDer (b i) ψ (g * embArch σ J w x)‖ ≤ c i) →
          ‖ψ (g * embArch σ J w y) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  have hA := isUnit_det_map hJ τ.1
  obtain ⟨δ₁, C₀, h1, hlog⟩ := GlobalTheory.UnitaryLog.exists_log_unitary n (J.map τ.1) hA
  haveI : FiniteDimensional ℝ (LieL (J.map τ.1)) := inferInstance
  haveI : ProperSpace (LieL (J.map τ.1)) := FiniteDimensional.proper_real _
  let b := Module.finBasis ℝ (LieL (J.map τ.1))
  obtain ⟨K₀, hK₀, hco⟩ := GlobalTheory.CuspGeo.MeanValue.exists_coord_bound b
  choose yOf hy1 hy2 using fun Y : LieL (J.map τ.1) => isLineOf_expMap h hJ τ Y 1
  simp only [one_smul] at hy1 hy2
  have hyc : Continuous yOf := (GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff.2 (by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun Y => archMat σ J τ (yOf Y) i j
    simp only [hy2]
    have : Continuous fun Y : LieL (J.map τ.1) => NormedSpace.exp Y.1 :=
      (NormedSpace.exp_continuous).comp continuous_subtype_val
    exact (continuous_apply j).comp ((continuous_apply i).comp this))
  have hy0 : yOf 0 = 1 := archMat_injective h τ (by
    rw [hy2, map_one]; simp)
  set C₁ : ℝ := n * |C₀| with hC₁
  have hC₁0 : 0 ≤ C₁ := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  refine ⟨_, inferInstance, fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • b i),
    yOf '' Metric.closedBall 0 (C₁ * δ₁), K₀ * C₁, δ₁, fun i => (isLineOf_expMap h hJ τ (b i)).isRealLine h,
    (isCompact_closedBall _ _).image hyc, ⟨0, ?_, hy0⟩, h1, mul_nonneg hK₀ hC₁0, fun y δ h0 hδ hy => ?_⟩
  · simpa using mul_nonneg hC₁0 h1.le
  have hU : (archMat σ J τ y)ᴴ * J.map τ.1 * archMat σ J τ y = J.map τ.1 := by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h τ y).2
  obtain ⟨X, hX, hE, hB⟩ := hlog (archMat σ J τ y) δ hU hδ hy
  let Z : LieL (J.map τ.1) := ⟨X, hX⟩
  have hZ : ‖Z‖ ≤ C₁ * δ := by
    have := norm_le_of_entries (mul_nonneg (abs_nonneg C₀) h0) fun i j =>
      (hB i j).trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) h0)
    rw [hC₁, mul_assoc]
    exact this
  have hyZ : yOf Z = y := archMat_injective h τ (by rw [hy2, ← hE])
  have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • Z ∈ Metric.closedBall (0 : LieL (J.map τ.1)) (C₁ * δ₁) := fun t ht => by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (hZ.trans (mul_le_mul_of_nonneg_left hδ hC₁0))
  refine ⟨⟨Z, by simpa using hball 1 (by simp), hyZ⟩, fun ψ hψ g c hc => ?_⟩
  rw [← hyZ, ← hy1 Z]
  refine GlobalTheory.CuspGeo.MeanValue.norm_sub_le _ (expMap_zero h τ) (expMap_add h hJ τ) b (sm_of_isSm h hJ τ hψ) g Z _
    (fun i => (hco Z i).trans ?_) c fun i t ht => ?_
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ hK₀
  · have := hc i (yOf (t • Z)) ⟨_, hball t ht, rfl⟩
    rw [← hy1] at this
    exact this

end OnePlace

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def pt (a : ∀ w, GArch σ J w) : GAd σ J := ofInf σ J (embArchPi σ J a)

theorem pt_mul_single [DecidableEq (InfinitePlace F)] (a : ∀ w, GArch σ J w) (w : InfinitePlace F) (x : GArch σ J w) :
    pt (a * Pi.mulSingle w x) = pt a * embArch σ J w x := by
  show ofInf σ J (embArchPi σ J (a * Pi.mulSingle w x)) = ofInf σ J (embArchPi σ J a) * embArch σ J w x
  rw [map_mul, map_mul, embArchPi_mulSingle]
  rfl

theorem pt_one : pt (1 : ∀ w, GArch σ J w) = 1 := by
  simp only [pt, map_one]

theorem pt_proj {u : GAd σ J} (hu : u ∈ infPts σ J) : pt (fun w => projArch σ J w u) = u := by
  refine GAd_ext σ J (fun w' => ?_) (fun v => ?_)
  · rw [pt, projArch_ofInf, projInfArch_embArchPi]
  · rw [pt, proj_ofInf, mem_infPts_iff_forall.mp hu v]

theorem continuous_pt : Continuous (pt : (∀ w, GArch σ J w) → GAd σ J) := by
  show Continuous fun a => ofInf σ J (embArchPi σ J a)
  exact (continuous_ofInf σ J).comp (continuous_embArchPi σ J)

open Classical in

theorem telescope {ι : InfinitePlace F → Type} [∀ w, Fintype (ι w)] {b : ∀ w, ι w → ℝ → GAd σ J}
    {K : ∀ w, Set (GArch σ J w)} {C : InfinitePlace F → ℝ} (h1 : ∀ w, 1 ∈ K w) {ψ : GAd σ J → ℂ} (g : GAd σ J)
    {y : ∀ w, GArch σ J w} (hyK : ∀ w, y w ∈ K w) {δ : ℝ} {c : ∀ w, ι w → ℝ}
    (hstep : ∀ w (g : GAd σ J), (∀ i, ∀ x ∈ K w, ‖lineDer (b w i) ψ (g * embArch σ J w x)‖ ≤ c w i) →
      ‖ψ (g * embArch σ J w (y w)) - ψ g‖ ≤ C w * δ * ∑ i, c w i)
    (hc : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c w i)
    (S : Finset (InfinitePlace F)) :
    ‖ψ (g * pt fun w => if w ∈ S then y w else 1) - ψ g‖ ≤ ∑ w ∈ S, C w * δ * ∑ i, c w i := by
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (fun w => if w ∈ (∅ : Finset (InfinitePlace F)) then y w else 1) = (1 : ∀ w, GArch σ J w) := by
      funext w
      simp
    rw [h0, pt_one, mul_one, sub_self, norm_zero, Finset.sum_empty]
  | @insert v S hv ih =>
    set a : ∀ w, GArch σ J w := fun w => if w ∈ S then y w else 1 with ha
    have hsplit : (fun w => if w ∈ insert v S then y w else 1) = a * Pi.mulSingle v (y v) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha, Finset.mem_insert, hw, false_or]
    have hK : ∀ x ∈ K v, a * Pi.mulSingle v x ∈ Set.pi Set.univ K := by
      intro x hx
      rw [Set.mem_univ_pi]
      intro w
      by_cases hw : w = v
      · subst hw
        simp [ha, hv, hx]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, mul_one, ha]
        split_ifs
        · exact hyK w
        · exact h1 w
    have step := hstep v (g * pt a) (fun i x hx => by
      rw [mul_assoc, ← pt_mul_single]
      exact hc v i _ ⟨_, hK x hx, rfl⟩)
    rw [hsplit, pt_mul_single, Finset.sum_insert hv, ← mul_assoc]
    calc _ = ‖(ψ (g * pt a * embArch σ J v (y v)) - ψ (g * pt a)) + (ψ (g * pt a) - ψ g)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add step ih)

end Places

theorem mean_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (b : Fin m → ℝ → GAd σ J) (Ω₀ : Set (GAd σ J)) (C δ₁ : ℝ), (∀ i, IsRealLine σ J (b i)) ∧ IsCompact Ω₀ ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g u : GAd σ J) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseInf σ J u δ → ∀ c : Fin m → ℝ, (∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ c i) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  have τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  choose ι hι b K C d hb hK h1K hd hC key using fun w => one_place (J := J) h hJ (τ w)
  letI : ∀ w, Fintype (ι w) := hι
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ > 0, ∀ w, δ₁ ≤ d w := by
    obtain ⟨w₀, h0⟩ := Finite.exists_min d
    exact ⟨d w₀, hd w₀, h0⟩
  let e := Fintype.equivFin (Σ w, ι w)
  have hCs : 0 ≤ ∑ w, C w := Finset.sum_nonneg fun w _ => hC w
  refine ⟨_, fun i => b (e.symm i).1 (e.symm i).2, pt '' Set.pi Set.univ K, ∑ w, C w, δ₁, fun i => hb _ _,
    (isCompact_univ_pi hK).image continuous_pt, hδ₁, hCs, fun ψ hψ g u δ h0 hδ hu c hc => ?_⟩
  let c' : ∀ w, ι w → ℝ := fun w i => c (e ⟨w, i⟩)
  have hc' : ∀ w i, ∀ x ∈ pt '' Set.pi Set.univ K, ‖lineDer (b w i) ψ (g * x)‖ ≤ c' w i := fun w i x hx => by
    have aux : ∀ p q : Σ w, ι w, p = q → lineDer (b p.1 p.2) ψ = lineDer (b q.1 q.2) ψ := by
      rintro _ _ rfl; rfl
    have := hc (e ⟨w, i⟩) x hx
    rwa [aux _ ⟨w, i⟩ (e.symm_apply_apply _)] at this
  have hnn : ∀ w i, 0 ≤ c' w i := fun w i =>
    (norm_nonneg _).trans (hc' w i 1 ⟨1, fun w _ => h1K w, pt_one⟩)
  have hclose := fun w => key w (projArch σ J w u) δ h0 (hδ.trans (hle w)) (hu.2 w (τ w))
  have T := telescope (b := b) (K := K) (C := C) h1K (ψ := ψ) g (y := fun w => projArch σ J w u)
    (fun w => (hclose w).1) (δ := δ) (c := c') (fun w g' hg' => (hclose w).2 ψ hψ g' (c' w) hg') hc' Finset.univ
  have hfull : (fun w => if w ∈ (Finset.univ : Finset (InfinitePlace F)) then projArch σ J w u else 1) =
      fun w => projArch σ J w u := by
    funext w; simp
  rw [hfull, pt_proj hu.1] at T
  refine T.trans ?_
  have hsum : ∑ i, c i = ∑ w, ∑ i, c' w i := by
    rw [← Equiv.sum_comp e c, Fintype.sum_sigma]
  have hT : ∀ w, ∑ i, c' w i ≤ ∑ i, c i := fun w => by
    rw [hsum]
    exact Finset.single_le_sum (f := fun w => ∑ i, c' w i)
      (fun w _ => Finset.sum_nonneg fun i _ => hnn w i) (Finset.mem_univ w)
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hT w) (mul_nonneg (hC w) h0)

end GlobalTheory.CompanionTheory.RapidDecay.Mean

end
