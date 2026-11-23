import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyTransformPreservesForm

noncomputable section

open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.Ux10

theorem block2_det_lower_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A 0 C D).det = A.det * D.det := by
  unfold blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

theorem block2_det_upper_triangular {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A B 0 D).det = A.det * D.det := by
  unfold blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem det_upper {p : ℕ} (u : G.UT p → ℂ) : (G.upper u).det = 1 := by
  have h : (G.upper u).BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    simp [G.upper, G.strictUpper, ne_of_gt hij, not_lt.mpr (le_of_lt hij)]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [G.upper, G.strictUpper]

theorem det_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) : (lowW σ v).det = 1 := by
  have h : (lowW σ v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have : ¬ (j < i ∧ σ.symm j < σ.symm i) := fun h => absurd h.1 (not_lt.mpr (le_of_lt hij'))
    simp [lowW, ne_of_lt hij', this]
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [lowW]

theorem detZj : DetZj := by
  intro p s σ d η Z
  unfold ZjH Zj headH hMat G.detM
  rw [Matrix.det_mul, Matrix.det_mul, block2_det_lower_triangular, block2_det_lower_triangular, block2_det_upper_triangular]
  simp only [Matrix.det_mul, det_upper, det_lowW, Matrix.det_one]
  ring

theorem permutationMatrix_eq_permMatrix {p : ℕ} (σ : Equiv.Perm (Fin p)) : wP σ = σ.permMatrix ℂ := by
  ext a b
  simp [wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

theorem det_hMat_ne {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) :
    (hMat σ d).det ≠ 0 := by
  unfold hMat
  rw [Matrix.det_mul, permutationMatrix_eq_permMatrix, Matrix.det_permutation, Matrix.det_diagonal]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem Rn_mem (hR : RadicalParam) (k j ρ : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have h : Rn k j ρ x ∈ Rset k j ρ := (hR k j ρ).2.1 ▸ Set.mem_range_self x
  exact h.1

theorem gaXi_mem (hM : SliceMem) (hR : RadicalParam) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (hZ : G.detM Z ≠ 0) {γ : B.Mat k ρ}
    (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  have hdet : (ZjH σ d ξ.2 Z).det ≠ 0 := by
    rw [detZj]; exact mul_ne_zero (det_hMat_ne σ d hd) hZ
  unfold gaXi
  refine BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_inv (Rn_mem hR _ _ _ _)) ((hM k (p + s) ρ).1 _ _ hdet hγ))
    (Rn_mem hR _ _ _ _)

theorem DjU_gaXi (hZh : ZhSlice) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ) :
    DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ) = (hMat σ d).det * G.detM Z := by
  unfold DjU gaXi
  rw [hZh, detZj]

theorem phiSupport_of (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) : PhiSupport := by
  intro k p s ρ σ d z z' E _ _ F₁ A₁ B₁ Q K hd hS Z hZ hK γ hγ
  have key : ∀ ξ : Xi k p s ρ σ, F₁ (gaXi k ρ σ d ξ Z γ) = 0 := by
    intro ξ
    by_contra hne
    have := hS.2.1 _ (gaXi_mem hM hR σ d hd ξ Z hZ hγ) hne
    rw [DjU_gaXi hZh] at this
    exact hK this
  unfold PhiFun
  simp [key]

end Formalism.FourierDecayAlt.P.Ux10

open MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.Ux10

section meas

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma tendsto_inv_succ_nhdsNE : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  · show ((n : ℝ) + 1)⁻¹ ≠ 0
    positivity

lemma aesm_deriv {G : α → ℝ → E} {G' : α → E} (hd : ∀ ξ, HasDerivAt (G ξ) (G' ξ) 0)
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun ξ => G ξ t) μ) : AEStronglyMeasurable G' μ := by
  have hm0 : AEStronglyMeasurable (fun ξ => G ξ 0) μ := hm.self_of_nhds
  have hev : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (fun ξ => G ξ (((n : ℝ) + 1)⁻¹)) μ :=
    (tendsto_inv_succ_nhdsNE.mono_right nhdsWithin_le_nhds).eventually hm
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (n : ℕ) ξ => ((((n + n₀ : ℕ) : ℝ) + 1)⁻¹)⁻¹ • (G ξ (0 + (((n + n₀ : ℕ) : ℝ) + 1)⁻¹) - G ξ 0)) ?_ ?_
  · intro n
    have h1 := hn₀ (n + n₀) (by omega)
    simp only [zero_add]
    exact (h1.sub hm0).const_smul _
  · refine Eventually.of_forall fun ξ => ?_
    exact ((hd ξ).tendsto_slope_zero).comp (tendsto_inv_succ_nhdsNE.comp (tendsto_add_atTop_nat n₀))

lemma aesm_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {F : α → X → E} {x : X} (hd : ∀ ξ, DifferentiableAt ℝ (F ξ) x)
    (hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fun ξ => F ξ y) μ) :
    AEStronglyMeasurable (fun ξ => fderiv ℝ (F ξ) x) μ := by
  classical
  set b := Module.finBasis ℝ X with hb
  have e : (fun ξ => fderiv ℝ (F ξ) x) = fun ξ =>
      ∑ j, (LinearMap.toContinuousLinearMap (b.coord j)).smulRight (fderiv ℝ (F ξ) x (b j)) := by
    funext ξ
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap']
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Module.Basis.coord_apply]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  have hl : HasDerivAt (fun t : ℝ => x + t • b j) (b j) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (b j)).const_add x
    simpa using h
  have hj : AEStronglyMeasurable (fun ξ => fderiv ℝ (F ξ) x (b j)) μ := by
    refine aesm_deriv (G := fun ξ t => F ξ (x + t • b j)) (fun ξ => ?_) ?_
    · exact (hd ξ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    · have ht : Tendsto (fun t : ℝ => x + t • b j) (𝓝 0) (𝓝 x) := by
        have := hl.continuousAt.tendsto
        simpa using this
      exact ht.eventually hm
  have hc : Continuous fun e : E => (LinearMap.toContinuousLinearMap (b.coord j)).smulRight e :=
    (ContinuousLinearMap.smulRightL ℝ X E (LinearMap.toContinuousLinearMap (b.coord j))).continuous
  exact hc.comp_aestronglyMeasurable hj

end meas

section pint

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem pint {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {U : Set X} (hU : IsOpen U)
    (b : α → ℝ) (hb : Integrable b μ) :
    ∀ (N : ℕ) (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (F : α → X → E'),
      (∀ ξ, ContDiffOn ℝ N (F ξ) U) → (∀ y ∈ U, AEStronglyMeasurable (fun ξ => F ξ y) μ) →
      (∀ i ≤ N, ∀ y ∈ U, ∀ ξ, ‖iteratedFDeriv ℝ i (F ξ) y‖ ≤ b ξ) →
      ContDiffOn ℝ N (fun y => ∫ ξ, F ξ y ∂μ) U ∧
      ∀ i ≤ N, ∀ y ∈ U, ∀ b' : α → ℝ, Integrable b' μ → (∀ ξ, ‖iteratedFDeriv ℝ i (F ξ) y‖ ≤ b' ξ) →
        ‖iteratedFDeriv ℝ i (fun y => ∫ ξ, F ξ y ∂μ) y‖ ≤ ∫ ξ, b' ξ ∂μ := by
  intro N
  induction N with
  | zero =>
    intro E' _ _ _ F hc hm hbd
    have h0 : ∀ y ∈ U, ∀ ξ, ‖F ξ y‖ ≤ b ξ := fun y hy ξ => by
      simpa [norm_iteratedFDeriv_zero] using hbd 0 le_rfl y hy ξ
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      refine continuousOn_of_dominated (F := fun y ξ => F ξ y) (bound := b) hm
        (fun y hy => Eventually.of_forall fun ξ => h0 y hy ξ) hb (Eventually.of_forall fun ξ => ?_)
      exact (hc ξ).continuousOn
    · intro i hi y hy b' hb' hbd'
      have hi0 : i = 0 := by omega
      subst hi0
      rw [norm_iteratedFDeriv_zero]
      refine norm_integral_le_of_norm_le hb' (Eventually.of_forall fun ξ => ?_)
      simpa [norm_iteratedFDeriv_zero] using hbd' ξ
  | succ N ih =>
    intro E' _ _ _ F hc hm hbd
    have hdiff : ∀ ξ, ∀ y ∈ U, DifferentiableAt ℝ (F ξ) y := fun ξ y hy =>
      ((hc ξ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
    have hc' : ∀ ξ, ContDiffOn ℝ N (fun y => fderiv ℝ (F ξ) y) U := fun ξ =>
      (hc ξ).fderiv_of_isOpen hU (by push_cast; exact le_rfl)
    have hm' : ∀ y ∈ U, AEStronglyMeasurable (fun ξ => fderiv ℝ (F ξ) y) μ := fun y hy =>
      aesm_fderiv (fun ξ => hdiff ξ y hy) (Filter.eventually_of_mem (hU.mem_nhds hy) hm)
    have hbd' : ∀ i ≤ N, ∀ y ∈ U, ∀ ξ, ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ (F ξ) y) y‖ ≤ b ξ :=
      fun i hi y hy ξ => by rw [norm_iteratedFDeriv_fderiv]; exact hbd (i + 1) (by omega) y hy ξ
    obtain ⟨ihc, ihb⟩ := ih (X →L[ℝ] E') (fun ξ y => fderiv ℝ (F ξ) y) hc' hm' hbd'
    have hint : ∀ y ∈ U, Integrable (fun ξ => F ξ y) μ := fun y hy =>
      hb.mono' (hm y hy) (Eventually.of_forall fun ξ => by
        simpa [norm_iteratedFDeriv_zero] using hbd 0 (by omega) y hy ξ)
    have hder : ∀ y ∈ U, HasFDerivAt (fun y => ∫ ξ, F ξ y ∂μ) (∫ ξ, fderiv ℝ (F ξ) y ∂μ) y := by
      intro y hy
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y ξ => F ξ y)
        (F' := fun y ξ => fderiv ℝ (F ξ) y) (bound := b) (hU.mem_nhds hy) ?_ (hint y hy) (hm' y hy) ?_ hb ?_
      · filter_upwards [hU.mem_nhds hy] with z hz using hm z hz
      · refine Eventually.of_forall fun ξ z hz => ?_
        have h1 := hbd 1 (by omega) z hz ξ
        rwa [norm_iteratedFDeriv_one] at h1
      · exact Eventually.of_forall fun ξ z hz => (hdiff ξ z hz).hasFDerivAt
    have hfd : ∀ y ∈ U, fderiv ℝ (fun y => ∫ ξ, F ξ y ∂μ) y = ∫ ξ, fderiv ℝ (F ξ) y ∂μ :=
      fun y hy => (hder y hy).fderiv
    refine ⟨?_, ?_⟩
    · rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun y hy => (hder y hy).differentiableAt.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
      exact ihc.congr fun y hy => hfd y hy
    · intro i hi y hy b' hb' hbd''
      cases i with
      | zero =>
        rw [norm_iteratedFDeriv_zero]
        refine norm_integral_le_of_norm_le hb' (Eventually.of_forall fun ξ => ?_)
        simpa [norm_iteratedFDeriv_zero] using hbd'' ξ
      | succ j =>
        rw [← norm_iteratedFDeriv_fderiv]
        have heq : (fderiv ℝ (fun y => ∫ ξ, F ξ y ∂μ)) =ᶠ[𝓝 y] (fun y => ∫ ξ, fderiv ℝ (F ξ) y ∂μ) := by
          filter_upwards [hU.mem_nhds hy] with z hz using hfd z hz
        rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
        exact ihb j (by omega) y hy b' hb' fun ξ => by rw [norm_iteratedFDeriv_fderiv]; exact hbd'' ξ

end pint

section struct

variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem ALd {Ω : Set 𝔤} (hΩ : IsOpen Ω) (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ))
    (ha : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a i) Ω) :
    ∀ (m : ℕ) (L : List ι → 𝔤 → E),
      (∀ w : List ι, w.length ≤ m → ContinuousOn (L w) Ω) →
      (∀ w : List ι, w.length < m → ∀ Y ∈ Ω, HasFDerivAt (L w) (∑ i, (a i Y).smulRight (L (i :: w) Y)) Y) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (L []) Ω := by
  intro m
  induction m with
  | zero =>
    intro L hc _
    rw [Nat.cast_zero, contDiffOn_zero]
    exact hc [] le_rfl
  | succ m ih =>
    intro L hc hd
    have hL : ∀ j : ι, ContDiffOn ℝ (m : WithTop ℕ∞) (L [j]) Ω := by
      intro j
      have := ih (fun w => L (w ++ [j])) (fun w hw => hc _ (by simp; omega))
        (fun w hw Y hY => by simpa using hd (w ++ [j]) (by simp; omega) Y hY)
      simpa using this
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun Y hY => (hd [] (by simp) Y hY).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hcd : ContDiffOn ℝ (m : WithTop ℕ∞) (fun Y => ∑ i, (a i Y).smulRight (L [i] Y)) Ω :=
      ContDiffOn.sum fun i _ => ((ha i).of_le (by exact_mod_cast le_top)).smulRight (hL i)
    exact hcd.congr fun Y hY => (hd [] (by simp) Y hY).fderiv

end struct

end Formalism.FourierDecayAlt.P.Ux10

open Matrix Filter Topology

namespace Formalism.FourierDecayAlt.P.Ux10

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}

lemma cdm_iff {F : X → Mat k r} :
    ContDiffOn ℝ n F s ↔ ∀ i j, ContDiffOn ℝ n (fun x => F x i j) s := by
  have := @contDiffOn_pi ℝ _ X _ _ s n (Fin (2 * r + k + 1)) _ (fun _ => Fin (2 * r + k + 1) → ℂ) _ _ F
  exact this.trans (forall_congr' fun i => contDiffOn_pi)

lemma cdm_mul {F G : X → Mat k r} (hF : ContDiffOn ℝ n F s) (hG : ContDiffOn ℝ n G s) :
    ContDiffOn ℝ n (fun x => F x * G x) s := by
  rw [cdm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hF i l).mul (hG l j)

lemma cd_det {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (fun x => (F x).det) s := by
  rw [cdm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hF _ _)

lemma cdm_updateRow {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (j : Fin (2 * r + k + 1))
    (b : Fin (2 * r + k + 1) → ℂ) : ContDiffOn ℝ n (fun x => (F x).updateRow j b) s := by
  rw [cdm_iff] at hF ⊢
  intro a l
  by_cases ha : a = j
  · subst ha; simp only [updateRow_self]; exact contDiffOn_const
  · simp only [updateRow_ne ha]; exact hF a l

lemma cdm_inv {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (hu : ∀ x ∈ s, IsUnit (F x).det) :
    ContDiffOn ℝ n (fun x => (F x)⁻¹) s := by
  rw [cdm_iff]
  intro i j
  have e : (fun x => (F x)⁻¹ i j)
      = fun x => ((F x).det)⁻¹ * ((F x).updateRow j (Pi.single i 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((cd_det hF).inv fun x hx => (hu x hx).ne_zero).mul (cd_det (cdm_updateRow hF j _))

end smooth

lemma hpk_herm : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1

lemma hpk_sq' : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1

def prj (Z : Mat k r) : Mat k r := (1 / 2 : ℂ) • (Z - Hpk k r * Zᴴ * Hpk k r)

lemma prj_lie (Z : Mat k r) : inLie k r (prj Z) := by
  unfold inLie prj
  have hH := (hpk_herm (k := k) (r := r))
  have hHH := (hpk_sq' (k := k) (r := r))
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH,
    conjTranspose_conjTranspose]
  have h1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hHH, Matrix.mul_one]
  have h2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2, ← smul_add]
  simp

lemma prj_of_lie {Z : Mat k r} (hZ : inLie k r Z) : prj Z = Z := by
  unfold prj
  have h0 : Zᴴ * Hpk k r = -(Hpk k r * Z) := eq_neg_of_add_eq_zero_left hZ
  have h1 : Hpk k r * Zᴴ * Hpk k r = -Z := by
    rw [Matrix.mul_assoc, h0, Matrix.mul_neg, ← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]
  rw [h1, sub_neg_eq_add, ← two_smul ℂ Z, smul_smul]
  norm_num

lemma prj_add (Z Z' : Mat k r) : prj (Z + Z') = prj Z + prj Z' := by
  unfold prj
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1; abel

lemma prj_rsmul (c : ℝ) (Z : Mat k r) : prj (c • Z) = c • prj Z := by
  unfold prj
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c Z, RCLike.real_smul_eq_coe_smul (K := ℂ) c,
    conjTranspose_smul]
  simp only [RCLike.star_def, RCLike.conj_ofReal]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_smul, smul_smul]
  congr 1; ring

lemma prj_zero : prj (0 : Mat k r) = 0 := by simp [prj]

lemma prj_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) :
    prj (∑ i ∈ s, c i • Z i) = ∑ i ∈ s, c i • prj (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prj_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, prj_add, prj_rsmul, ih]

def kap (Y : Mat k r) : Mat k r := (1 + Y) * (1 - Y)⁻¹

def iot (Z : Mat k r) : Mat k r := (Z - 1) * (Z + 1)⁻¹

lemma kap_mem {Y : Mat k r} (hY : inLie k r Y) (hu : IsUnit (1 - Y).det) : kap Y ∈ GV k r := by
  first | exact UpperTheory.Reformulated.B.Qk20.kap_mem .. | (apply UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk20.kap_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk20.kap_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r Y hY hu | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r Y hY | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r Y | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k r | exact @UpperTheory.Reformulated.B.Qk20.kap_mem k

lemma iot_facts {h : Mat k r} (hh : h ∈ GV k r) (hu : IsUnit (h + 1).det) :
    inLie k r (iot h) ∧ IsUnit (1 - iot h).det ∧ kap (iot h) = h := by
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  set D := h + 1 with hD
  set C := h - 1 with hC
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hu
  have hDD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hZD : iot h * D = C := by
    unfold iot; rw [Matrix.mul_assoc, hDD, Matrix.mul_one]

  have h1Z : 1 - iot h = (2 : ℂ) • D⁻¹ := by
    have : (1 - iot h) * D = (2 : ℂ) • (1 : Mat k r) := by
      rw [Matrix.sub_mul, Matrix.one_mul, hZD, hD, hC]
      rw [two_smul]; abel
    calc 1 - iot h = (1 - iot h) * D * D⁻¹ := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
      _ = (2 : ℂ) • D⁻¹ := by rw [this, Matrix.smul_mul, Matrix.one_mul]
  have hu1 : IsUnit (1 - iot h).det := by
    rw [h1Z, Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 two_ne_zero)).mul (Matrix.isUnit_nonsing_inv_det _ hu)
  refine ⟨?_, hu1, ?_⟩
  ·
    have hDu : IsUnit (Dᴴ).det := by rw [det_conjTranspose]; exact hu.star
    have e1 : Cᴴ * Hpk k r * D = hᴴ * Hpk k r - Hpk k r * h := by
      rw [hC, hD, conjTranspose_sub, conjTranspose_one]
      calc (hᴴ - 1) * Hpk k r * (h + 1) = hᴴ * Hpk k r * h + hᴴ * Hpk k r - Hpk k r * h - Hpk k r := by
            noncomm_ring
        _ = hᴴ * Hpk k r - Hpk k r * h := by rw [hh']; abel
    have e2 : Dᴴ * Hpk k r * C = -(hᴴ * Hpk k r - Hpk k r * h) := by
      rw [hC, hD, conjTranspose_add, conjTranspose_one]
      calc (hᴴ + 1) * Hpk k r * (h - 1) = hᴴ * Hpk k r * h - hᴴ * Hpk k r + Hpk k r * h - Hpk k r := by
            noncomm_ring
        _ = -(hᴴ * Hpk k r - Hpk k r * h) := by rw [hh']; abel
    have e3 : Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D = 0 := by
      have : Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D
          = (iot h * D)ᴴ * Hpk k r * D + Dᴴ * Hpk k r * (iot h * D) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      rw [this, hZD, e1, e2, add_neg_cancel]
    have hDH : (Dᴴ)⁻¹ * Dᴴ = 1 := Matrix.nonsing_inv_mul _ hDu
    show (iot h)ᴴ * Hpk k r + Hpk k r * iot h = 0
    calc (iot h)ᴴ * Hpk k r + Hpk k r * iot h
        = (Dᴴ)⁻¹ * (Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D) * D⁻¹ := by
          simp only [← Matrix.mul_assoc, hDH, Matrix.one_mul]
          rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
      _ = 0 := by rw [e3, Matrix.mul_zero, Matrix.zero_mul]
  ·
    have hp : (1 + iot h) * D = h * ((1 - iot h) * D) := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hZD, hD, hC]; noncomm_ring
    have hq : 1 + iot h = h * (1 - iot h) := by
      calc 1 + iot h = (1 + iot h) * D * D⁻¹ := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
        _ = h * (1 - iot h) := by rw [hp, ← Matrix.mul_assoc, Matrix.mul_assoc _ D, hDD', Matrix.mul_one]
    unfold kap
    rw [hq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]

section smooth2

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}

lemma cdm_conjT {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (fun x => (F x)ᴴ) s := by
  rw [cdm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn (hF j i)

lemma cdm_prj {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) : ContDiffOn ℝ n (fun x => prj (F x)) s := by
  unfold prj
  exact (hF.sub (cdm_mul (cdm_mul contDiffOn_const (cdm_conjT hF)) contDiffOn_const)).const_smul _

end smooth2

abbrev J (k r : ℕ) : Type := Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool

def Eb (i : J k r) : Mat k r :=
  Matrix.of fun p q => if p = i.1 ∧ q = i.2.1 then (if i.2.2 then Complex.I else 1) else 0

def Mv (Y : J k r → ℝ) : Mat k r :=
  Matrix.of fun p q => ((Y (p, q, false) : ℝ) : ℂ) + ((Y (p, q, true) : ℝ) : ℂ) * Complex.I

def co (Z : Mat k r) : J k r → ℝ := fun i => if i.2.2 then (Z i.1 i.2.1).im else (Z i.1 i.2.1).re

lemma Mv_co (Z : Mat k r) : Mv (co Z) = Z := by
  ext p q
  simp [Mv, co, Complex.re_add_im]

lemma Mv_sum (Y : J k r → ℝ) : Mv Y = ∑ i, Y i • Eb i := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eb, Matrix.of_apply, Mv, smul_ite, smul_zero, ite_and]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Complex.real_smul, mul_one, if_true, if_false, Bool.false_eq_true]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [add_comm]
  all_goals first | (intro b _ hb; simp [Ne.symm hb]) | simp

lemma co_add (Z Z' : Mat k r) (i : J k r) : co (Z + Z') i = co Z i + co Z' i := by
  unfold co; split_ifs <;> simp

lemma co_smul (c : ℝ) (Z : Mat k r) (i : J k r) : co (c • Z) i = c * co Z i := by
  unfold co; split_ifs <;> simp [Complex.real_smul]

lemma co_zero (i : J k r) : co (0 : Mat k r) i = 0 := by
  unfold co; split_ifs <;> simp

lemma co_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) (i : J k r) :
    co (∑ b ∈ s, c b • Z b) i = ∑ b ∈ s, c b * co (Z b) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [co_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, co_add, co_smul, ih]

lemma cd_co {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
    {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (i : J k r) : ContDiffOn ℝ n (fun x => co (F x) i) s := by
  rw [cdm_iff] at hF
  unfold co
  by_cases h : i.2.2 = true
  · simp only [h, if_true]; exact Complex.imCLM.contDiff.comp_contDiffOn (hF _ _)
  · simp only [h]; exact Complex.reCLM.contDiff.comp_contDiffOn (hF _ _)

lemma cd_Mv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Mv : (J k r → ℝ) → Mat k r) := by
  rw [← contDiffOn_univ, cdm_iff]
  intro p q
  simp only [Mv, Matrix.of_apply]
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (p, q, false))).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (p, q, true))).mul contDiff_const)).contDiffOn

def Lt (i : J k r) : Mat k r := (nrm (true, prj (Eb i))).2

lemma Lt_unit (i : J k r) : unitLie k r (Lt i) := nrm_unit (prj_lie _)

lemma prj_Eb (i : J k r) : prj (Eb i) = ‖prj (Eb i)‖ • Lt i := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact nrm_smul _

def kc (i : J k r) (Z : Mat k r) : ℝ := co Z i * ‖prj (Eb i)‖

lemma expandL {Z : Mat k r} (hZ : inLie k r Z) : Z = ∑ i, kc i Z • Lt i := by
  conv_lhs => rw [← prj_of_lie hZ, ← Mv_co Z, Mv_sum, prj_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_Eb, smul_smul]
  rfl

lemma kc_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) (i : J k r) :
    kc i (∑ b ∈ s, c b • Z b) = ∑ b ∈ s, c b * kc i (Z b) := by
  unfold kc; rw [co_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

def chart (g0 : Mat k r) (Y : J k r → ℝ) : Mat k r := kap (prj (Mv Y)) * g0

def Dom (k r : ℕ) : Set (J k r → ℝ) := {Y | IsUnit (1 - prj (Mv Y)).det}

lemma cd_prjMv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : J k r → ℝ => prj (Mv Y)) Set.univ :=
  cdm_prj cd_Mv.contDiffOn

lemma dom_open : IsOpen (Dom k r) := by
  have hc : Continuous (fun Y : J k r → ℝ => (1 - prj (Mv Y)).det) := by
    rw [← continuousOn_univ]
    exact (cd_det (contDiffOn_const.sub cd_prjMv)).continuousOn
  have : Dom k r = {Y : J k r → ℝ | (1 - prj (Mv Y)).det ≠ (fun _ => (0 : ℂ)) Y} := by
    ext Y; simp [Dom, isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne_fun hc continuous_const

lemma zero_mem_dom : (0 : J k r → ℝ) ∈ Dom k r := by
  have h0 : Mv (0 : J k r → ℝ) = 0 := by ext p q; simp [Mv]
  simp [Dom, h0, prj_zero]

lemma chart_cd (g0 : Mat k r) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart g0) (Dom k r) := by
  have hP := cd_prjMv (k := k) (r := r)
  unfold chart kap
  exact cdm_mul (cdm_mul (contDiffOn_const.add (hP.mono (Set.subset_univ _)))
    (cdm_inv (contDiffOn_const.sub (hP.mono (Set.subset_univ _))) fun Y hY => hY)) contDiffOn_const

lemma chart_mem {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) :
    chart g0 Y ∈ GV k r :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (kap_mem (prj_lie _) hY) hg0

lemma chart_diff (g0 : Mat k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) : DifferentiableAt ℝ (chart g0) Y :=
  ((chart_cd g0).differentiableOn (by simp)).differentiableAt (dom_open.mem_nhds hY)

def mulB (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => mulL A
      map_add' := fun A B => by ext g : 1; simp [mulL_apply, Matrix.add_mul]
      map_smul' := fun c A => by ext g : 1; simp [mulL_apply] }

lemma mulB_apply (A B : Mat k r) : mulB k r A B = A * B := rfl

def cT (k r : ℕ) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun c A => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
          conjTranspose_smul]
        simp only [RCLike.star_def, RCLike.conj_ofReal] }

lemma cT_apply (A : Mat k r) : cT k r A = Aᴴ := rfl

lemma tangent {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) (W : J k r → ℝ) :
    inLie k r (-(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹) := by
  set c := chart g0 Y with hc
  set T := fderiv ℝ (chart g0) Y W with hT
  have hcG : c ∈ GV k r := chart_mem hg0 hY
  have hcu : IsUnit c.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hcG
  set γ : ℝ → Mat k r := fun t => chart g0 (Y + t • W) with hγ
  have hline : HasDerivAt (fun t : ℝ => Y + t • W) W 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const W).const_add Y
    rw [one_smul] at h
    exact h
  have hγd : HasDerivAt γ T 0 :=
    (chart_diff g0 hY).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hγ0 : γ 0 = c := by simp [hγ, hc]
  have h1 : HasDerivAt (fun t => cT k r (γ t)) (cT k r T) 0 :=
    (cT k r).hasFDerivAt.comp_hasDerivAt 0 hγd
  have h2 : HasDerivAt (fun t => mulB k r (cT k r (γ t)) (Hpk k r))
      (mulB k r (cT k r (γ 0)) 0 + mulB k r (cT k r T) (Hpk k r)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h1) (fun _ => hasDerivAt_const _ _)
  have h3 : HasDerivAt (fun t => mulB k r (mulB k r (cT k r (γ t)) (Hpk k r)) (γ t))
      (mulB k r (mulB k r (cT k r (γ 0)) (Hpk k r)) T +
        mulB k r (mulB k r (cT k r (γ 0)) 0 + mulB k r (cT k r T) (Hpk k r)) (γ 0)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h2) (fun _ => hγd)
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), Y + t • W ∈ Dom k r :=
    ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt (x := (0:ℝ))).preimage_mem_nhds
      (dom_open.mem_nhds (by simpa using hY))
  have h4 : HasDerivAt (fun t => mulB k r (mulB k r (cT k r (γ t)) (Hpk k r)) (γ t)) 0 0 := by
    refine (hasDerivAt_const (0:ℝ) (Hpk k r)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    have hm : γ t ∈ GV k r := chart_mem hg0 ht
    exact hm
  have hz := h3.unique h4
  simp only [mulB_apply, cT_apply, hγ0, Matrix.mul_zero, zero_add] at hz

  have hci : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv _ hcu
  have hci' : (c⁻¹)ᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, hci, conjTranspose_one]
  show (-T * c⁻¹)ᴴ * Hpk k r + Hpk k r * (-T * c⁻¹) = 0
  have : (-T * c⁻¹)ᴴ * Hpk k r + Hpk k r * (-T * c⁻¹)
      = -((c⁻¹)ᴴ * (cᴴ * Hpk k r * T + Tᴴ * Hpk k r * c) * c⁻¹) := by
    rw [conjTranspose_mul, conjTranspose_neg]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hci']
    simp only [Matrix.mul_assoc, hci, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [this, hz, Matrix.mul_zero, Matrix.zero_mul, neg_zero]

def ebv (b : J k r) : J k r → ℝ := fun j => if b = j then 1 else 0

def sC (g0 : Mat k r) (i b : J k r) (Y : J k r → ℝ) : ℝ :=
  kc i (-(fderiv ℝ (chart g0) Y (ebv b)) * (chart g0 Y)⁻¹)

def aC (g0 : Mat k r) (i : J k r) (Y : J k r → ℝ) : (J k r → ℝ) →L[ℝ] ℝ :=
  ∑ b, sC g0 i b Y • ContinuousLinearMap.proj b

lemma aC_apply (g0 : Mat k r) (i : J k r) (Y W : J k r → ℝ) :
    aC g0 i Y W = kc i (-(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹) := by
  have hW : W = ∑ b, W b • ebv b := pi_eq_sum_univ W
  have e1 : -(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹ =
      ∑ b, W b • (-(fderiv ℝ (chart g0) Y (ebv b)) * (chart g0 Y)⁻¹) := by
    conv_lhs => rw [hW]
    rw [map_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ← smul_neg, Matrix.smul_mul]
  rw [e1, kc_sum]
  simp only [aC, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, sC]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma aC_cd {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (i : J k r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (aC g0 i) (Dom k r) := by
  have h1 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => fderiv ℝ (chart g0) Y (ebv b)) (Dom k r) :=
    fun b => ((chart_cd g0).fderiv_of_isOpen dom_open (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => (chart g0 Y)⁻¹) (Dom k r) :=
    cdm_inv (chart_cd g0) fun Y hY => Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (chart_mem hg0 hY)
  have h3 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sC g0 i b) (Dom k r) := by
    intro b
    unfold sC kc
    exact (cd_co (cdm_mul (h1 b).neg h2) i).mul contDiffOn_const
  unfold aC
  exact ContDiffOn.sum fun b _ => (h3 b).smul contDiffOn_const

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma hasFDeriv_chart {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {H : Mat k r → E}
    (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) :
    HasFDerivAt (fun Y' => H (chart g0 Y'))
      (∑ i, (aC g0 i Y).smulRight (op true (Lt i) H (chart g0 Y))) Y := by
  set c := chart g0 Y with hc
  have hcG : c ∈ GV k r := chart_mem hg0 hY
  have hcu : IsUnit c.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hcG
  obtain ⟨U, h', hU, hcU, hcd, hff⟩ := hH c hcG
  have hdiff : DifferentiableAt ℝ h' c :=
    (hcd.differentiableOn (cast_ne_zero 0)).differentiableAt (hU.mem_nhds hcU)
  have hchd := chart_diff g0 hY
  have hcomp : HasFDerivAt (fun Y' => h' (chart g0 Y'))
      ((fderiv ℝ h' c).comp (fderiv ℝ (chart g0) Y)) Y :=
    hdiff.hasFDerivAt.comp Y hchd.hasFDerivAt
  have heq : (fun Y' => H (chart g0 Y')) =ᶠ[𝓝 Y] (fun Y' => h' (chart g0 Y')) := by
    filter_upwards [hchd.continuousAt.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY]
      with Y' h1 h2
    exact hff _ h1 (chart_mem hg0 h2)
  refine (hcomp.congr_of_eventuallyEq heq).congr_fderiv ?_
  ext1 W
  rw [ContinuousLinearMap.comp_apply, _root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  have hop : ∀ i, op true (Lt i) H c = fderiv ℝ h' c (-(Lt i * c)) := fun i =>
    op_eq_op' 0 true hU hcd hff (Lt_unit i).1 c hcU hcG
  simp_rw [hop, ← map_smul, ← map_sum]
  congr 1
  set Xv := -(fderiv ℝ (chart g0) Y W) * c⁻¹ with hXv
  have hXl : inLie k r Xv := tangent hg0 hY W
  have hA : ∀ i, aC g0 i Y W = kc i Xv := fun i => aC_apply g0 i Y W
  have hXc : Xv * c = -(fderiv ℝ (chart g0) Y W) := by
    rw [hXv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hcu, Matrix.mul_one]
  calc fderiv ℝ (chart g0) Y W = -(Xv * c) := by rw [hXc, neg_neg]
    _ = -((∑ i, kc i Xv • Lt i) * c) := by rw [← expandL hXl]
    _ = ∑ i, aC g0 i Y W • -(Lt i * c) := by
        simp only [hA, Finset.sum_mul, Matrix.smul_mul, smul_neg, Finset.sum_neg_distrib]

lemma continuous_gN : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

lemma cont_chart {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {H : Mat k r → E}
    (hH : CkOn ((0 : ℕ) : ℕ∞) (GV k r) H) : ContinuousOn (fun Y => H (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContinuousAt.continuousWithinAt
  obtain ⟨U, h', hU, hcU, hcd, hff⟩ := hH _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContinuousAt (fun Y' => h' (chart g0 Y')) Y :=
    ContinuousAt.comp (g := h') (hcd.continuousOn.continuousAt (hU.mem_nhds hcU)) hchc
  refine h1.congr ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact (hff _ h1 (chart_mem hg0 h2)).symm

def rho (g0 : Mat k r) (x : Mat k r) : J k r → ℝ := co (iot (x * g0⁻¹))

def Sr (g0 : Mat k r) : Set (Mat k r) := {x | IsUnit (x * g0⁻¹ + 1).det}

lemma sr_open (g0 : Mat k r) : IsOpen (Sr g0) := by
  have hc : Continuous (fun x : Mat k r => (x * g0⁻¹ + 1).det) :=
    ((continuous_id.matrix_mul continuous_const).add continuous_const).matrix_det
  have : Sr g0 = {x : Mat k r | (x * g0⁻¹ + 1).det ≠ (fun _ => (0 : ℂ)) x} := by
    ext x; simp [Sr, isUnit_iff_ne_zero]
  rw [this]
  exact isOpen_ne_fun hc continuous_const

lemma rho_cd (g0 : Mat k r) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rho g0) (Sr g0) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Mat k r => x * g0⁻¹) (Sr g0) :=
    cdm_mul contDiffOn_id contDiffOn_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => iot (x * g0⁻¹)) (Sr g0) := by
    unfold iot
    exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun x hx => hx)
  exact contDiffOn_pi.2 fun i => cd_co h2 i

end Formalism.FourierDecayAlt.P.Ux10

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.Ux10

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma meas_alt {h : α → Mat k r → E} {mm : ℕ} (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ))
    (hm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => h ξ g) μ) :
    ∀ w : List (Bool × Mat k r), AllLie w → w.length ≤ mm → ∀ g ∈ GV k r,
      AEStronglyMeasurable (fun ξ => W w (h ξ) g) μ := by
  intro w
  induction w with
  | nil => intro _ _ g hg; exact hm g hg
  | cons x w ih =>
    intro hw hl g hg
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hl' : w.length + 1 ≤ mm := by simpa using hl
    have hC : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W w (h ξ)) := fun ξ =>
      smooth_on_of_word_derivatives w hw' 1 (ckOn_mono (by omega) (hh ξ))
    refine aesm_deriv (G := fun ξ t => W w (h ξ) (cv x.1 x.2 t g)) (fun ξ => ?_)
      (Eventually.of_forall fun t => ih hw' (by omega) _ (cv_mem hx hg t))
    exact (ckOn_diff 0 x.1 (hC ξ) hx hg).hasDerivAt

lemma step_int {b : Bool} {X : Mat k r} (hX : inLie k r X) [CompleteSpace E] (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    (hGm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => G ξ g) μ) (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ g ∈ GV k r, ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ g ∈ GV k r, ∀ ξ, ‖op b X (G ξ) g‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ g ∈ GV k r, Φ g = ∫ ξ, ψ ξ • G ξ g ∂μ) :
    ∀ g ∈ GV k r, op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by
  intro g hg
  have hcurve : ∀ t, cv b X t g ∈ GV k r := fun t => cv_mem hX hg t
  have hd : ∀ ξ, ∀ g₁ ∈ GV k r, HasDerivAt (fun s : ℝ => G ξ (cv b X s g₁)) (op b X (G ξ) g₁) 0 :=
    fun ξ g₁ hg₁ => (ckOn_diff 0 b (hG1 ξ) hX hg₁).hasDerivAt
  have hd1m : ∀ g₁ ∈ GV k r, AEStronglyMeasurable (fun ξ => op b X (G ξ) g₁) μ := fun g₁ hg₁ =>
    aesm_deriv (G := fun ξ t => G ξ (cv b X t g₁)) (fun ξ => hd ξ g₁ hg₁)
      (Eventually.of_forall fun t => hGm _ (cv_mem hX hg₁ t))
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (bound := β)
    (F := fun t ξ => ψ ξ • G ξ (cv b X t g)) (x₀ := 0) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun t => hψm.smul (hGm _ (hcurve t)))
    (hβ.mono' (hψm.smul (hGm _ (hcurve 0))) (Eventually.of_forall fun ξ => (hsm ξ _).trans (hb0 _ (hcurve 0) ξ)))
    (F' := fun t ξ => ψ ξ • op b X (G ξ) (cv b X t g))
    (hψm.smul (hd1m _ (hcurve 0)))
    (Eventually.of_forall fun ξ t _ => (hsm ξ _).trans (hb1 _ (hcurve t) ξ)) hβ
    (Eventually.of_forall fun ξ t _ => by
      have e : (fun t' : ℝ => G ξ (cv b X t' g)) = fun t' => G ξ (cv b X (t' - t) (cv b X t g)) := by
        funext t'; rw [← cv_add]; congr 2; ring
      have h2 : HasDerivAt (fun s => G ξ (cv b X s (cv b X t g))) (op b X (G ξ) (cv b X t g)) (t - t) := by
        rw [sub_self]; exact hd ξ _ (hcurve t)
      have h3 := (h2.comp_sub_const t t)
      rw [← e] at h3
      exact h3.const_smul (ψ ξ))
  have e1 : (fun t : ℝ => Φ (cv b X t g)) = fun t => ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ := by
    funext t; exact hΦ _ (hcurve t)
  show deriv (fun t : ℝ => Φ (cv b X t g)) 0 = _
  rw [e1, key.2.deriv]
  simp only [cv_zero]

section exch

variable [CompleteSpace E]

theorem exch_dLR (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1) (hψm : AEStronglyMeasurable ψ μ) (h : α → Mat k r → E) (mm : ℕ)
    (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ))
    (hm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => h ξ g) μ) (β : α → ℝ) (hβ : Integrable β μ)
    (hbd : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ mm →
      ∀ g ∈ GV k r, ∀ ξ, ‖dLR u v (h ξ) g‖ ≤ β ξ) :
    ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ mm →
      ∀ g ∈ GV k r, dLR u v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ) g = ∫ ξ, ψ ξ • dLR u v (h ξ) g ∂μ := by
  have hC : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length + 1 ≤ mm → ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (dLR u v (h ξ)) := by
    intro u v hu hv hl ξ
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) 1 (ckOn_mono (by rw [length_lr]; omega) (hh ξ))
  have hM : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ mm → ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => dLR u v (h ξ) g) μ := by
    intro u v hu hv hl g hg
    simp_rw [dLR_eq]
    exact meas_alt hh hm _ (allLie_lr hu hv) (by rw [length_lr]; exact hl) g hg
  have base : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ mm →
      ∀ g ∈ GV k r, dLR [] v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ) g = ∫ ξ, ψ ξ • dLR [] v (h ξ) g ∂μ := by
    intro v
    induction v with
    | nil => intro _ _ g _; rfl
    | cons X v ih =>
      intro hv hl g hg
      have hv' : ∀ Y ∈ v, unitLie k r Y := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
      have hX := hv X List.mem_cons_self
      have hl' : v.length + 1 ≤ mm := by simpa using hl
      show op false X (dLR [] v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ)) g = ∫ ξ, ψ ξ • op false X (dLR [] v (h ξ)) g ∂μ
      exact step_int (b := false) hX.1 ψ hψ hψm (fun ξ => dLR [] v (h ξ)) (hC [] v (by simp) hv' (by simpa using hl'))
        (hM [] v (by simp) hv' (by simp; omega)) β hβ (hbd [] v (by simp) hv' (by simp; omega))
        (hbd [] (X :: v) (by simp) hv (by simpa using hl)) _ (ih hv' (by omega)) g hg
  intro u
  induction u with
  | nil => intro v _ hv hl; exact base v hv (by simpa using hl)
  | cons X u ih =>
    intro v hu hv hl g hg
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    have hl' : u.length + v.length + 1 ≤ mm := by simp at hl; omega
    show op true X (dLR u v (fun g' => ∫ ξ, ψ ξ • h ξ g' ∂μ)) g = ∫ ξ, ψ ξ • op true X (dLR u v (h ξ)) g ∂μ
    exact step_int (b := true) hX.1 ψ hψ hψm (fun ξ => dLR u v (h ξ)) (hC u v hu' hv hl')
      (hM u v hu' hv (by omega)) β hβ (hbd u v hu' hv (by omega)) (hbd (X :: u) v hu hv hl) _
      (ih v hu' hv (by omega)) g hg

end exch

section ck

variable [CompleteSpace E]

theorem ck_of_chart {F : Mat k r → E} {mm : ℕ}
    (h : ∀ g0 ∈ GV k r, ∃ δ > 0, Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r ∧
      ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Metric.ball 0 δ)) :
    CkOn ((mm : ℕ) : ℕ∞) (GV k r) F := by
  intro g0 hg0
  obtain ⟨δ, hδ, -, hAL⟩ := h g0 hg0
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  set U := Sr g0 ∩ rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball
  have hg0U : g0 ∈ U := by
    have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
    refine ⟨?_, ?_⟩
    · show IsUnit (g0 * g0⁻¹ + 1).det
      rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
    · show rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ
      have h3 : rho g0 g0 = 0 := by
        funext i
        simp only [rho, hg1, iot, sub_self, Matrix.zero_mul]
        exact co_zero i
      rw [h3]; exact Metric.mem_ball_self hδ
  refine ⟨U, fun x => F (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · have h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (rho g0) U :=
      ((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)
    exact hAL.comp h4 (by intro x hx; exact hx.2)
  · intro x hx hxG
    have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
    obtain ⟨hl, -, hk⟩ := iot_facts hh hx.1
    show F x = F (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)
    rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

theorem int_ck (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1) (hψm : AEStronglyMeasurable ψ μ) (h : α → Mat k r → E) (mm : ℕ)
    (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ))
    (hm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => h ξ g) μ) (β : α → ℝ) (hβ : Integrable β μ)
    (hbd : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ mm →
      ∀ g ∈ GV k r, ∀ ξ, ‖dLR u v (h ξ) g‖ ≤ β ξ) :
    CkOn ((mm : ℕ) : ℕ∞) (GV k r) (fun g => ∫ ξ, ψ ξ • h ξ g ∂μ) := by
  apply ck_of_chart
  intro g0 hg0
  obtain ⟨δ0, hδ0, hball⟩ := Metric.mem_nhds_iff.1 (dom_open.mem_nhds (zero_mem_dom (k := k) (r := r)))
  set δ := δ0 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hcl : Metric.closedBall (0 : J k r → ℝ) δ ⊆ Dom k r :=
    (Metric.closedBall_subset_ball (by rw [hδ]; linarith)).trans hball
  have hΩ : Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r := Metric.ball_subset_closedBall.trans hcl
  have hcomp : IsCompact (Metric.closedBall (0 : J k r → ℝ) δ) := isCompact_closedBall _ _
  have hac : ContinuousOn (fun Y => ∑ i, ‖aC g0 i Y‖) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    continuousOn_finsetSum _ fun i _ => ((aC_cd hg0 i).continuousOn.mono hcl).norm
  obtain ⟨Ba, hBa⟩ := hcomp.exists_bound_of_continuousOn hac
  have hBa' : ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∑ i, ‖aC g0 i Y‖ ≤ Ba := by
    intro Y hY
    have h1 := hBa Y (Metric.ball_subset_closedBall hY)
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  have hBa0 : 0 ≤ Ba := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hBa' 0 (Metric.mem_ball_self hδp))
  have hunit : ∀ w : List (J k r), ∀ X ∈ w.map Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Lt_unit i
  have hckw : ∀ ξ (w : List (J k r)) (m : ℕ), m + w.length ≤ mm →
      CkOn ((m : ℕ) : ℕ∞) (GV k r) (dLR (w.map Lt) [] (h ξ)) := by
    intro ξ w m hm'
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) m (ckOn_mono (by rw [length_lr]; simp; omega) (hh ξ))
  have hM : ∀ (w : List (J k r)), w.length ≤ mm → ∀ g ∈ GV k r,
      AEStronglyMeasurable (fun ξ => dLR (w.map Lt) [] (h ξ) g) μ := by
    intro w hw g hg
    simp_rw [dLR_eq]
    exact meas_alt hh hm _ (allLie_lr (hunit w) (by simp)) (by rw [length_lr]; simpa using hw) g hg
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hbw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ,
      ‖ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ := fun w hw Y hY ξ =>
    (hsm ξ _).trans (hbd _ [] (hunit w) (by simp) (by simpa using hw) _ (chart_mem hg0 (hΩ hY)) ξ)
  have hmw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ := fun w hw Y hY =>
    hψm.smul (hM w hw _ (chart_mem hg0 (hΩ hY)))
  set L : List (J k r) → (J k r → ℝ) → E :=
    fun w Y => ∫ ξ, ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y) ∂μ with hL
  have hLc : ∀ w : List (J k r), w.length ≤ mm → ContinuousOn (L w) (Metric.ball (0 : J k r → ℝ) δ) := by
    intro w hw
    refine continuousOn_of_dominated (F := fun Y ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) (bound := β)
      (fun Y hY => hmw w hw Y hY) (fun Y hY => Eventually.of_forall fun ξ => hbw w hw Y hY ξ) hβ
      (Eventually.of_forall fun ξ => ?_)
    exact ((cont_chart hg0 (hckw ξ w 0 (by omega))).mono hΩ).const_smul (ψ ξ)
  have hLd : ∀ w : List (J k r), w.length < mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      HasFDerivAt (L w) (∑ i, (aC g0 i Y).smulRight (L (i :: w) Y)) Y := by
    intro w hw Y hY
    have hD : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ,
        HasFDerivAt (fun Y'' => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y''))
          (∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))) Y' := by
      intro ξ Y' hY'
      have h1 := (hasFDeriv_chart hg0 (hckw ξ w 1 (by omega)) (hΩ hY')).const_smul (ψ ξ)
      refine h1.congr_fderiv ?_
      ext1 W
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
        ContinuousLinearMap.smulRight_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
      rfl
    have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ =>
      (norm_nonneg _).trans (hbd [] [] (by simp) (by simp) (by simp) g0 hg0 ξ)
    have hF'm : AEStronglyMeasurable (fun ξ => ∑ i, (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).continuous.comp_aestronglyMeasurable
        (hmw (i :: w) (by simp; omega) Y hY)
    have hbF' : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ, ‖∑ i, (aC g0 i Y').smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ ≤ Ba * β ξ := by
      intro ξ Y' hY'
      calc _ ≤ ∑ i, ‖(aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, ‖aC g0 i Y'‖ * β ξ := Finset.sum_le_sum fun i _ => by
            rw [ContinuousLinearMap.norm_smulRight_apply]
            exact mul_le_mul_of_nonneg_left (hbw (i :: w) (by simp; omega) Y' hY' ξ) (norm_nonneg _)
        _ = (∑ i, ‖aC g0 i Y'‖) * β ξ := by rw [Finset.sum_mul]
        _ ≤ Ba * β ξ := mul_le_mul_of_nonneg_right (hBa' Y' hY') (hβ0 ξ)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
      (F := fun Y' ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y'))
      (F' := fun Y' ξ => ∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y')))
      (bound := fun ξ => Ba * β ξ) (Metric.isOpen_ball.mem_nhds hY)
      (by filter_upwards [Metric.isOpen_ball.mem_nhds hY] with Y' hY' using hmw w hw.le Y' hY')
      (hβ.mono' (hmw w hw.le Y hY) (Eventually.of_forall fun ξ => hbw w hw.le Y hY ξ))
      hF'm (Eventually.of_forall fun ξ Y' hY' => hbF' ξ Y' hY') (hβ.const_mul Ba)
      (Eventually.of_forall fun ξ Y' hY' => hD ξ Y' hY')
    refine key.congr_fderiv ?_
    have hint : ∀ i, Integrable (fun ξ => ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y)) μ := fun i =>
      hβ.mono' (hmw (i :: w) (by simp; omega) Y hY)
        (Eventually.of_forall fun ξ => hbw (i :: w) (by simp; omega) Y hY ξ)
    have hI : ∀ i, Integrable (fun ξ => (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := fun i =>
      (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integrable_comp (hint i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integral_comp_comm (hint i)
  have hAL := ALd (𝔤 := J k r → ℝ) (E := E) Metric.isOpen_ball (aC g0) (fun i => (aC_cd hg0 i).mono hΩ) mm L
    hLc hLd
  exact ⟨δ, hδp, hΩ, hAL.congr fun Y _ => rfl⟩

end ck

end Formalism.FourierDecayAlt.P.Ux10

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.Ux10

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants

section cont

variable {X : Type*} [TopologicalSpace X]

@[fun_prop]
lemma cont_strictUpper {d : ℕ} {f : X → G.UT d → ℂ} (hf : Continuous f) :
    Continuous fun x => G.strictUpper (f x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : i < j
  · simp only [G.strictUpper, Matrix.of_apply, h, dite_true]
    exact (continuous_apply _).comp hf
  · simp only [G.strictUpper, Matrix.of_apply, h, dite_false]
    exact continuous_const

@[fun_prop]
lemma cont_fromRows {m₁ m₂ n : Type*} {A : X → Matrix m₁ n ℂ} {B : X → Matrix m₂ n ℂ} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => Matrix.fromRows (A x) (B x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i
  · simp only [Matrix.fromRows_apply_inl]; exact (continuous_apply_apply i j).comp hA
  · simp only [Matrix.fromRows_apply_inr]; exact (continuous_apply_apply i j).comp hB

@[fun_prop]
lemma cont_fromCols {m n₁ n₂ : Type*} {A : X → Matrix m n₁ ℂ} {B : X → Matrix m n₂ ℂ} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => Matrix.fromCols (A x) (B x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases j with j | j
  · simp only [Matrix.fromCols_apply_inl]; exact (continuous_apply_apply i j).comp hA
  · simp only [Matrix.fromCols_apply_inr]; exact (continuous_apply_apply i j).comp hB

lemma cont_skewOf {j : ℕ} : Continuous (fun q : (G.UT j → ℂ) × (Fin j → ℝ) => skewOf q) := by
  unfold skewOf
  fun_prop

lemma cont_Rn (k j ρ : ℕ) : Continuous (fun x : RC k j ρ => Rn k j ρ x) := by
  have := cont_skewOf (j := j)
  unfold Rn blk3
  fun_prop

@[fun_prop]
lemma cont_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) {f : X → LW σ → ℂ} (hf : Continuous f) :
    Continuous fun x => lowW σ (f x) := by
  have : Continuous fun x => (Matrix.of fun a b => if h : b < a ∧ σ.symm b < σ.symm a then f x ⟨(a, b), h⟩ else 0 :
      Matrix (Fin p) (Fin p) ℂ) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    by_cases h : b < a ∧ σ.symm b < σ.symm a
    · simp only [Matrix.of_apply, h, dite_true]
      exact (continuous_apply _).comp hf
    · simp only [Matrix.of_apply, h, dite_false]
      exact continuous_const
  unfold lowW
  fun_prop

lemma cont_inv {n : Type*} [Fintype n] [DecidableEq n] {A : X → Matrix n n ℂ} (hA : Continuous A)
    (hdet : ∀ x, (A x).det ≠ 0) : Continuous fun x => (A x)⁻¹ :=
  continuous_iff_continuousAt.2 fun x =>
    (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hdet x))).comp hA.continuousAt

lemma cont_ZjH {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (Z : G.Mat s) :
    Continuous fun η : XiH p s σ => ZjH σ d η Z := by
  unfold ZjH Zj headH blk2 G.upper
  fun_prop

lemma cont_gaXi {k p s ρ : ℕ} (hR : RadicalParam) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Z : G.Mat s) (hZ : G.detM Z ≠ 0) (γ : B.Mat k ρ) :
    Continuous fun ξ : Xi k p s ρ σ => gaXi k ρ σ d ξ Z γ := by
  have h1 : Continuous fun ξ : Xi k p s ρ σ => (Rn k (p + s) ρ ξ.1.1)⁻¹ :=
    cont_inv ((cont_Rn k (p + s) ρ).comp (continuous_fst.comp continuous_fst)) fun ξ =>
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (Rn_mem hR k (p + s) ρ ξ.1.1)).ne_zero
  have h2 : Continuous fun ξ : Xi k p s ρ σ => (ZjH σ d ξ.2 Z)ᴴ⁻¹ := by
    refine cont_inv (((cont_ZjH σ d Z).comp continuous_snd).matrix_conjTranspose) fun ξ => ?_
    rw [Matrix.det_conjTranspose, detZj]
    exact star_ne_zero.2 (mul_ne_zero (det_hMat_ne σ d hd) hZ)
  have h3 : Continuous fun ξ : Xi k p s ρ σ => ZjH σ d ξ.2 Z := (cont_ZjH σ d Z).comp continuous_snd
  have h4 : Continuous fun ξ : Xi k p s ρ σ => Rn k (p + s) ρ ξ.1.2 :=
    (cont_Rn k (p + s) ρ).comp (continuous_snd.comp continuous_fst)
  unfold gaXi mMap blk3
  fun_prop

end cont

section psi

variable {X : Type*} [TopologicalSpace X]

@[fun_prop]
lemma cont_ell {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {f : X → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hf : Continuous f) : Continuous fun x => ell k r z (f x) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dite_true]; exact (continuous_apply_apply _ _).comp hf
  · have h3 : Continuous fun x => f x *ᵥ z := hf.matrix_mulVec continuous_const
    have h2 : Continuous fun x => (f x *ᵥ z) (eI k r a) := continuous_pi_iff.1 h3 _
    refine h2.congr fun x => ?_
    simp only [h, dite_false]

@[fun_prop]
lemma cont_subS {p : ℕ} {f : X → Matrix (Fin p) (Fin p) ℂ} (hf : Continuous f) : Continuous fun x => subS (f x) := by
  unfold subS
  refine continuous_finsetSum _ fun i _ => ?_
  by_cases h : i.val + 1 < p
  · simp only [h, dite_true]; exact (continuous_apply_apply _ _).comp hf
  · simp only [h, dite_false]; exact continuous_const

@[fun_prop]
lemma cont_supS {p : ℕ} {f : X → Matrix (Fin p) (Fin p) ℂ} (hf : Continuous f) : Continuous fun x => supS (f x) := by
  unfold supS
  refine continuous_finsetSum _ fun i _ => ?_
  by_cases h : i.val + 1 < p
  · simp only [h, dite_true]; exact (continuous_apply_apply _ _).comp hf
  · simp only [h, dite_false]; exact continuous_const

@[fun_prop]
lemma cont_cornerA {p s : ℕ} {f : X → Fin s → Fin p → ℂ} (hf : Continuous f) : Continuous fun x => cornerA (f x) := by
  unfold cornerA
  by_cases h : 0 < s ∧ 0 < p
  · simp only [h, dite_true]; exact (continuous_apply_apply _ _).comp hf
  · simp only [h, dite_false]; exact continuous_const

@[fun_prop]
lemma cont_cornerB {p s : ℕ} {f : X → Fin p → Fin s → ℂ} (hf : Continuous f) : Continuous fun x => cornerB (f x) := by
  unfold cornerB
  by_cases h : 0 < s ∧ 0 < p
  · simp only [h, dite_true]; exact (continuous_apply_apply _ _).comp hf
  · simp only [h, dite_false]; exact continuous_const

@[fun_prop]
lemma continuous_psi_comp {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    {f : X → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hf : Continuous f) :
    Continuous fun x => Formalism.QuantumDeterminants.psi k r z c (f x) := by
  unfold Formalism.QuantumDeterminants.psi
  fun_prop

@[fun_prop]
lemma cont_upper {d : ℕ} {f : X → G.UT d → ℂ} (hf : Continuous f) : Continuous fun x => G.upper (f x) := by
  unfold G.upper
  fun_prop

lemma cont_psiH {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) : Continuous fun η : XiH p s σ => psiH β σ η := by
  unfold psiH G.psi
  fun_prop

lemma cont_psiStar (k : ℕ) {p s : ℕ} (ρ : ℕ) (σ : Equiv.Perm (Fin p)) (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ) :
    Continuous fun ξ : Xi k p s ρ σ => psiStar k ρ σ z z' ξ := by
  have h1 : Continuous fun ξ : Xi k p s ρ σ => Formalism.QuantumDeterminants.psi k (p + s + ρ) z cStd (Rn k (p + s) ρ ξ.1.1) :=
    continuous_psi_comp z cStd ((cont_Rn k (p + s) ρ).comp (continuous_fst.comp continuous_fst))
  have h2 : Continuous fun ξ : Xi k p s ρ σ => Formalism.QuantumDeterminants.psi k (p + s + ρ) z' cStd (Rn k (p + s) ρ ξ.1.2) :=
    continuous_psi_comp z' cStd ((cont_Rn k (p + s) ρ).comp (continuous_snd.comp continuous_fst))
  have h3 : Continuous fun ξ : Xi k p s ρ σ => psiH betaU σ ξ.2 := (cont_psiH betaU σ).comp continuous_snd
  unfold psiStar
  exact (h1.mul (continuous_star.comp h2)).mul h3

lemma norm_psiStar (k : ℕ) {p s : ℕ} (ρ : ℕ) (σ : Equiv.Perm (Fin p)) (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ)
    (ξ : Xi k p s ρ σ) : ‖psiStar k ρ σ z z' ξ‖ = 1 := by
  unfold psiStar Formalism.QuantumDeterminants.psi psiH G.psi
  rw [norm_mul, norm_mul, norm_star, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal,
    Complex.norm_exp_I_mul_ofReal]
  norm_num

end psi

section cd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma block3_middle_contDiffOn {k j ρ : ℕ} (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin j) (Fin j) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A31 : Matrix (Fin j) (Fin j) ℂ)
    (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun γ : B.Mat k ρ => blk3 (k := k) (j := j) (ρ := ρ) A11 A12 A13 A21 γ A23 A31 A32 A33) Set.univ := by
  have hid : ∀ a b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun γ : B.Mat k ρ => γ a b) Set.univ :=
    cdm_iff.1 contDiffOn_id
  rw [cdm_iff]
  intro i l
  simp only [blk3, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (eB k j ρ).symm i = x
  generalize (eB k j ρ).symm l = y
  rcases x with (a | a) | a <;> rcases y with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr] <;>
    first | exact contDiffOn_const | exact hid a b

lemma cd_gaXi {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : Xi k p s ρ σ) (Z : G.Mat s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun γ : B.Mat k ρ => gaXi k ρ σ d ξ Z γ) Set.univ := by
  unfold gaXi mMap
  exact cdm_mul (cdm_mul contDiffOn_const (block3_middle_contDiffOn _ _ _ _ _ _ _ _)) contDiffOn_const

lemma ckOn_slice (hM : SliceMem) (hR : RadicalParam) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {F₁ : B.Mat k (p + s + ρ) → E}
    {Q : ℕ∞} (hF : B.CkOn Q (B.GV k (p + s + ρ)) F₁) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (hZ : G.detM Z ≠ 0) :
    B.CkOn Q (B.GV k ρ) (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) := by
  intro γ₀ hγ₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF _ (gaXi_mem hM hR σ d hd ξ Z hZ hγ₀)
  have hcd := cd_gaXi (k := k) σ d ξ Z
  refine ⟨(fun γ => gaXi k ρ σ d ξ Z γ) ⁻¹' U, fun γ => f' (gaXi k ρ σ d ξ Z γ),
    hU.preimage (continuousOn_univ.1 hcd.continuousOn), hgU, ?_, ?_⟩
  · exact hc.comp ((hcd.of_le (by exact_mod_cast le_top)).mono (Set.subset_univ _)) (fun x hx => hx)
  · intro γ hγ hγG
    exact hff _ hγ (gaXi_mem hM hR σ d hd ξ Z hZ hγG)

end cd

end Formalism.FourierDecayAlt.P.Ux10

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.Ux10

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma slice_vanish (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F₁ : B.Mat k (p + s + ρ) → E} {A₁ B₁ : ℝ} {Q : ℕ} {K : Set ℝ} (hS : Star k (p + s) ρ F₁ A₁ Q B₁ K)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (hZ : G.detM Z ≠ 0) (hK : ‖(hMat σ d).det * G.detM Z‖ ∉ K) :
    ∀ γ ∈ B.GV k ρ, F₁ (gaXi k ρ σ d ξ Z γ) = 0 := by
  intro γ hγ
  by_contra hne
  have := hS.2.1 _ (gaXi_mem hM hR σ d hd ξ Z hZ hγ) hne
  rw [DjU_gaXi hZh] at this
  exact hK this

lemma one_le_wt {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) : 1 ≤ wt ξ := by
  have h1 : ∀ x : ℝ, 0 ≤ x → 1 ≤ 1 + x := fun x hx => by linarith
  unfold wt wtH
  refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (h1 _ (norm_nonneg _))
    (h1 _ (norm_nonneg _))) ?_
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (h1 _ (norm_nonneg _)) (h1 _ (norm_nonneg _))) (h1 _ (norm_nonneg _))) (h1 _ (norm_nonneg _))

lemma dLR_vanish {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ g ∈ B.GV k r, f g = 0) (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.unitLie k r X)
    (hv : ∀ X ∈ v, B.unitLie k r X) : ∀ g ∈ B.GV k r, B.dLR u v f g = 0 := by
  intro g hg
  have h1 := W_congr (lr u v) (allLie_lr hu hv) (f := f) (f₂ := fun _ => (0 : E)) hf g hg
  rw [dLR_eq, h1, ← dLR_eq]
  have h2 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero (E := E) u v
  exact congrFun h2 g

theorem slice_bound (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) (hC : DerivativeCost) (hS : CoordinateDecay)
    {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (hs : 1 ≤ s)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Set.Ioi 0) (m mm Q : ℕ) (A₁ : ℝ) (hQ : m + 1 + mm ≤ Q)
    (ha : 0 < a1 (p + s + ρ) A₁ m mm) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F₁ : B.Mat k (p + s + ρ) → E) (B₁ : ℝ),
      Star k (p + s) ρ F₁ A₁ Q B₁ K → ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s), G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ,
      ∀ u v : List (B.Mat k ρ), unitW k ρ u → unitW k ρ v → u.length + v.length ≤ mm → ∀ q ≤ m + 1,
        ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) Z‖ ≤
          Cb * B₁ * ((1 + ‖Z‖) ^ (-a1 (p + s + ρ) A₁ m mm) * B.gN γ ^ (-a1 (p + s + ρ) A₁ m mm)) *
            wt ξ ^ (-a1 (p + s + ρ) A₁ m mm) := by
  set a := a1 (p + s + ρ) A₁ m mm with ha_def
  set R : ℝ := ((p + s + ρ : ℕ) : ℝ) with hRdef
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  set As := A₁ - 5 * R * ((m : ℝ) + 1) - 2 * R * (mm : ℝ) with hAsdef
  have hden : 0 < 8 * (2 * R + 1) := by positivity
  have hAa : As / (8 * (2 * R + 1)) = a := by rw [ha_def]; unfold a1; rfl
  have hAs0 : 0 ≤ As := by
    have : As = a * (8 * (2 * R + 1)) := by rw [← hAa]; field_simp
    rw [this]; positivity
  obtain ⟨C₃, hC₃⟩ := hC k p s ρ σ d hd hs K hK hK0 Q
  obtain ⟨C₂, hC₂⟩ := hS k p s ρ σ d hd hs K hK hK0 As hAs0
  refine ⟨|C₃| * |C₂|, by positivity, ?_⟩
  intro E _ _ F₁ B₁ hStar ξ Z hZ γ hγ u v hu hv hl q hq
  have hB₁ : 0 ≤ B₁ := by
    have := hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) 1 Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_one
    exact le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) this
  have hγ1 : 1 ≤ B.gN γ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hγ
  have hw1 : 1 ≤ wt ξ := one_le_wt ξ
  have hZ1 : 1 ≤ 1 + ‖Z‖ := by linarith [norm_nonneg Z]
  by_cases hKZ : ‖(hMat σ d).det * G.detM Z‖ ∈ K
  · obtain ⟨-, hb⟩ := hC₃ E F₁ A₁ B₁ hStar ξ u v q hu hv (by omega) Z γ hZ hγ
    have hg := gaXi_mem hM hR σ d hd ξ Z hZ hγ
    have hg1 : 1 ≤ B.gN (gaXi k ρ σ d ξ Z γ) := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    have hDj : ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K := by rw [DjU_gaXi hZh]; exact hKZ
    have hs22 := hC₂ ξ Z γ hγ hDj
    have hexp : -A₁ + 5 * R * (q : ℝ) + 2 * R * ((u.length + v.length : ℕ) : ℝ) ≤ -As := by
      have hq' : (q : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hq
      have hl' : ((u.length + v.length : ℕ) : ℝ) ≤ (mm : ℝ) := by exact_mod_cast hl
      rw [hAsdef]; nlinarith
    calc _ ≤ C₃ * B₁ * B.gN (gaXi k ρ σ d ξ Z γ) ^
            (-A₁ + 5 * R * (q : ℝ) + 2 * R * ((u.length + v.length : ℕ) : ℝ)) := hb
      _ ≤ |C₃| * B₁ * B.gN (gaXi k ρ σ d ξ Z γ) ^ (-As) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hB₁) (Real.rpow_le_rpow_of_exponent_le hg1 hexp)
            (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ ≤ |C₃| * B₁ * (|C₂| * (wt ξ * (1 + ‖Z‖) * B.gN γ) ^ (-a)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine hs22.trans ?_
          rw [hAa]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by positivity) _)
      _ = |C₃| * |C₂| * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN γ ^ (-a)) * wt ξ ^ (-a) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
          ring
  · have hO : IsOpen {Z' : G.Mat s | G.detM Z' ≠ 0 ∧ ‖(hMat σ d).det * G.detM Z'‖ ∉ K} := by
      have hc : Continuous (fun Z' : G.Mat s => G.detM Z') := by unfold G.detM; fun_prop
      exact (isOpen_ne_fun hc continuous_const).inter
        (hK.isClosed.isOpen_compl.preimage (continuous_norm.comp (continuous_const.mul hc)))
    have hev : (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) =ᶠ[𝓝 Z]
        fun _ => (0 : E) := by
      filter_upwards [hO.mem_nhds ⟨hZ, hKZ⟩] with Z' hZ'
      exact dLR_vanish (slice_vanish hM hR hZh σ d hd hStar ξ Z' hZ'.1 hZ'.2) u v hu hv γ hγ
    rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity

end Formalism.FourierDecayAlt.P.Ux10

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.Ux10

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma fin_step {x g a T c I : ℝ} (hg : 0 < g) (hx : x ≤ c * (T * g ^ (-a)) * I) :
    g ^ a * x ≤ c * I * T := by
  have hga : g ^ a * g ^ (-a) = 1 := by rw [← Real.rpow_add hg]; simp
  calc g ^ a * x ≤ g ^ a * (c * (T * g ^ (-a)) * I) := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hg.le _)
    _ = (g ^ a * g ^ (-a)) * (c * I * T) := by ring
    _ = c * I * T := by rw [hga, one_mul]

theorem phi_bound_parts_of_radical_and_slice (hR : RadicalParam) (hZh : ZhSlice) : PointwiseIntegralBoundFromComponents := by
  intro hM hC hS hI k p s ρ σ d hd hs K hK hK0 m mm Q A₁ hQ ha
  set a := a1 (p + s + ρ) A₁ m mm with ha_def
  have hn0 : 0 ≤ 2 * ((p + s + ρ : ℕ) : ℝ) * ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) := by positivity
  have ha0 : 0 < a := lt_of_le_of_lt hn0 ha
  obtain ⟨Cb, hCb0, hbd⟩ := slice_bound hM hR hZh hC hS σ d hd hs hK hK0 m mm Q A₁ hQ ha0
  obtain ⟨C₃, hC₃⟩ := hC k p s ρ σ d hd hs K hK hK0 Q
  have hInt : Integrable (fun ξ : Xi k p s ρ σ => wt ξ ^ (-a)) (muXi k p s ρ σ) := hI k p s ρ σ a hs ha
  set I := ∫ ξ, wt ξ ^ (-a) ∂(muXi k p s ρ σ) with hIdef
  refine ⟨Cb * I, ?_⟩
  intro z z' E _ _ _ F₁ B₁ hStar
  have hB₁ : 0 ≤ B₁ := by
    have := hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) 1 Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_one
    exact le_trans (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) this
  have hψ : ∀ ξ, ‖psiStar k ρ σ z z' ξ‖ ≤ 1 := fun ξ => (norm_psiStar k ρ σ z z' ξ).le
  have : BorelSpace (XiH p s σ) := Prod.borelSpace
  have : BorelSpace (RC k (p + s) ρ × RC k (p + s) ρ) := Prod.borelSpace
  have : BorelSpace (Xi k p s ρ σ) := Prod.borelSpace
  have : SecondCountableTopology (Xi k p s ρ σ) := inferInstance
  have hψm : AEStronglyMeasurable (fun ξ => psiStar k ρ σ z z' ξ) (muXi k p s ρ σ) :=
    (cont_psiStar k ρ σ z z').aestronglyMeasurable
  have hck : ∀ ξ (Z : G.Mat s), G.detM Z ≠ 0 →
      B.CkOn ((mm : ℕ) : ℕ∞) (B.GV k ρ) (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) :=
    fun ξ Z hZ => ckOn_mono (by omega) (ckOn_slice hM hR σ d hd hStar.1 ξ Z hZ)
  have hcont1 : ContinuousOn F₁ (B.GV k (p + s + ρ)) :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono (by simp) hStar.1)
  have hmeas : ∀ (Z : G.Mat s), G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ,
      AEStronglyMeasurable (fun ξ => F₁ (gaXi k ρ σ d ξ Z γ)) (muXi k p s ρ σ) := by
    intro Z hZ γ hγ
    exact (hcont1.comp_continuous (cont_gaXi hR σ d hd Z hZ γ)
      fun ξ => gaXi_mem hM hR σ d hd ξ Z hZ hγ).aestronglyMeasurable
  have hsm : ∀ ξ (e : E), ‖psiStar k ρ σ z z' ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hwt0 : ∀ ξ : Xi k p s ρ σ, 0 ≤ wt ξ ^ (-a) := fun ξ =>
    Real.rpow_nonneg (le_trans zero_le_one (one_le_wt ξ)) _
  have hTle : ∀ (Z : G.Mat s) (g : B.Mat k ρ), g ∈ B.GV k ρ → (1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a) ≤ 1 :=
    fun Z g hg => mul_le_one₀
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg Z]) (by linarith))
      (Real.rpow_nonneg (le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg) (by linarith))
  have hweak : ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (g : B.Mat k ρ), g ∈ B.GV k ρ →
      Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a)) * wt ξ ^ (-a) ≤ Cb * B₁ * wt ξ ^ (-a) := by
    intro ξ Z g hg
    have h1 := hTle Z g hg
    have h2 : 0 ≤ Cb * B₁ := mul_nonneg hCb0 hB₁
    calc Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a)) * wt ξ ^ (-a)
        ≤ Cb * B₁ * 1 * wt ξ ^ (-a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) (hwt0 ξ)
      _ = Cb * B₁ * wt ξ ^ (-a) := by ring
  have hbγ : ∀ (Z : G.Mat s), G.detM Z ≠ 0 → ∀ u v : List (B.Mat k ρ), (∀ X ∈ u, B.unitLie k ρ X) →
      (∀ X ∈ v, B.unitLie k ρ X) → u.length + v.length ≤ mm → ∀ g ∈ B.GV k ρ, ∀ ξ,
      ‖B.dLR u v (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) g‖ ≤ Cb * B₁ * wt ξ ^ (-a) := by
    intro Z hZ u v hu hv hl g hg ξ
    have h0 := hbd E F₁ B₁ hStar ξ Z hZ g hg u v hu hv hl 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (hweak ξ Z g hg)
  have hβ : Integrable (fun ξ => Cb * B₁ * wt ξ ^ (-a)) (muXi k p s ρ σ) := hInt.const_mul _
  have hexch : ∀ (Z : G.Mat s), G.detM Z ≠ 0 → ∀ u v : List (B.Mat k ρ), (∀ X ∈ u, B.unitLie k ρ X) →
      (∀ X ∈ v, B.unitLie k ρ X) → u.length + v.length ≤ mm → ∀ g ∈ B.GV k ρ,
      B.dLR u v (PhiFun k ρ σ d z z' F₁ Z) g =
        ∫ ξ, psiStar k ρ σ z z' ξ • B.dLR u v (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) g ∂(muXi k p s ρ σ) :=
    fun Z hZ => exch_dLR (μ := muXi k p s ρ σ) (fun ξ => psiStar k ρ σ z z' ξ) hψ hψm
      (fun ξ γ => F₁ (gaXi k ρ σ d ξ Z γ)) mm (fun ξ => hck ξ Z hZ) (fun g hg => hmeas Z hZ g hg) _ hβ (hbγ Z hZ)
  refine ⟨fun Z γ hZ hγ => ?_, fun Z hZ => ?_, fun u v hu hv hl γ hγ => ?_⟩
  · refine hβ.mono' (hψm.smul (hmeas Z hZ γ hγ)) (Eventually.of_forall fun ξ => ?_)
    exact (hsm ξ _).trans (hbγ Z hZ [] [] (by simp) (by simp) (by simp) γ hγ ξ)
  · refine ⟨int_ck (μ := muXi k p s ρ σ) (fun ξ => psiStar k ρ σ z z' ξ) hψ hψm
      (fun ξ γ => F₁ (gaXi k ρ σ d ξ Z γ)) mm (fun ξ => hck ξ Z hZ) (fun g hg => hmeas Z hZ g hg) _ hβ (hbγ Z hZ), ?_⟩
    intro u v hu hv hl g hg
    rw [hexch Z hZ u v hu hv hl g hg]
    have hb' : ∀ ξ, ‖psiStar k ρ σ z z' ξ • B.dLR u v (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) g‖ ≤
        Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a)) * wt ξ ^ (-a) := fun ξ => by
      refine (hsm ξ _).trans ?_
      have h0 := hbd E F₁ B₁ hStar ξ Z hZ g hg u v hu hv hl 0 (by omega)
      rwa [norm_iteratedFDeriv_zero] at h0
    have hnorm := norm_integral_le_of_norm_le (hInt.const_mul (Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN g ^ (-a))))
      (Eventually.of_forall hb')
    rw [integral_const_mul] at hnorm
    have hg0 : 0 < B.gN g := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
    have := fin_step (c := Cb * B₁) (T := (1 + ‖Z‖) ^ (-a)) hg0 hnorm
    calc _ ≤ Cb * B₁ * I * (1 + ‖Z‖) ^ (-a) := this
      _ = Cb * I * B₁ * (1 + ‖Z‖) ^ (-a) := by ring
  · have hcD : Continuous (fun Z' : G.Mat s => G.detM Z') := by unfold G.detM; fun_prop
    have hUo : IsOpen {Z : G.Mat s | G.detM Z ≠ 0} := isOpen_ne_fun hcD continuous_const
    have hcda : ∀ ξ (i : ℕ), i ≤ m + 1 → ∀ Z' : G.Mat s, G.detM Z' ≠ 0 →
        ContDiffAt ℝ i (fun Z'' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) Z' :=
      fun ξ i hi Z' hZ' => (hC₃ E F₁ A₁ B₁ hStar ξ u v i hu hv (by omega) Z' γ hZ' hγ).1
    have hcd : ∀ ξ, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
        (fun Z' : G.Mat s => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ)
        {Z | G.detM Z ≠ 0} := fun ξ Z' hZ' =>
      ((hcda ξ (m + 1) le_rfl Z' hZ').const_smul (psiStar k ρ σ z z' ξ)).contDiffWithinAt
    have hmZ : ∀ Z' ∈ {Z : G.Mat s | G.detM Z ≠ 0}, AEStronglyMeasurable
        (fun ξ => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) (muXi k p s ρ σ) := by
      intro Z' hZ'
      refine hψm.smul ?_
      simp_rw [dLR_eq]
      exact meas_alt (fun ξ => hck ξ Z' hZ') (fun g hg => hmeas Z' hZ' g hg) _ (allLie_lr hu hv)
        (by rw [length_lr]; exact hl) γ hγ
    have hdf : ∀ ξ (i : ℕ), i ≤ m + 1 → ∀ Z' : G.Mat s, G.detM Z' ≠ 0 →
        ‖iteratedFDeriv ℝ i (fun Z'' : G.Mat s => psiStar k ρ σ z z' ξ •
          B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) Z'‖ ≤
          Cb * B₁ * ((1 + ‖Z'‖) ^ (-a) * B.gN γ ^ (-a)) * wt ξ ^ (-a) := by
      intro ξ i hi Z' hZ'
      have e := iteratedFDeriv_const_smul_apply (a := psiStar k ρ σ z z' ξ) (hcda ξ i hi Z' hZ')
      have e2 : (fun Z'' : G.Mat s => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) =
          psiStar k ρ σ z z' ξ • (fun Z'' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z'' γ')) γ) := rfl
      rw [e2, e, norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)).trans
        (hbd E F₁ B₁ hStar ξ Z' hZ' γ hγ u v hu hv hl i hi)
    obtain ⟨hcont, hbnd⟩ := pint hUo (fun ξ => Cb * B₁ * wt ξ ^ (-a)) hβ (m + 1) E
      (fun ξ Z' => psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) hcd hmZ
      (fun i hi Z' hZ' ξ => (hdf ξ i hi Z' hZ').trans (hweak ξ Z' γ hγ))
    have heqU : ∀ Z' ∈ {Z : G.Mat s | G.detM Z ≠ 0}, B.dLR u v (PhiFun k ρ σ d z z' F₁ Z') γ =
        ∫ ξ, psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ ∂(muXi k p s ρ σ) :=
      fun Z' hZ' => hexch Z' hZ' u v hu hv hl γ hγ
    refine ⟨hcont.congr heqU, fun q hq Z hZ => ?_⟩
    have hev : (fun Z' : G.Mat s => B.dLR u v (PhiFun k ρ σ d z z' F₁ Z') γ) =ᶠ[𝓝 Z]
        (fun Z' => ∫ ξ, psiStar k ρ σ z z' ξ • B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ
          ∂(muXi k p s ρ σ)) := by
      filter_upwards [hUo.mem_nhds hZ] with Z' hZ' using heqU Z' hZ'
    rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds]
    have hn := hbnd q hq Z hZ _ (hInt.const_mul (Cb * B₁ * ((1 + ‖Z‖) ^ (-a) * B.gN γ ^ (-a))))
      (fun ξ => hdf ξ q hq Z hZ)
    rw [integral_const_mul] at hn
    have hg0 : 0 < B.gN γ := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hγ)
    have := fin_step (c := Cb * B₁) (T := (1 + ‖Z‖) ^ (-a)) hg0 hn
    calc _ ≤ Cb * B₁ * I * (1 + ‖Z‖) ^ (-a) := this
      _ = Cb * I * B₁ * (1 + ‖Z‖) ^ (-a) := by ring

end Formalism.FourierDecayAlt.P.Ux10

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.U

theorem Ux10.phi_bound_parts_of_radical_parametrisation (hR : RadicalParam) : PointwiseIntegralBoundFromComponents :=
  Ux10.phi_bound_parts_of_radical_and_slice hR hat_z_on_slice

theorem Ux10.phiSupport_of_parts (hM : SliceMem) (hR : RadicalParam) : PhiSupport :=
  Ux10.phiSupport_of hM hR hat_z_on_slice

theorem Ux10.size_decay_of_slice_membership (hM : SliceMem) : CoordinateDecay :=
  norm_decay_of_coordinate_sizes
    (coordinate_sizes_of_parts hM block3_apply_embedding aux_statement_17 hat_z_on_slice level_determinant_z)

theorem Ux10.derivative_cost_of_slice_and_radical (hM : SliceMem) (hR : RadicalParam) (hCP : DerivativeCostFromComponents) : DerivativeCost :=
  hCP hM hR slice_right_coordinates slice_left_coordinates slice_z_coordinates directions_in_parabolic
    (coordinate_sizes_of_parts hM block3_apply_embedding aux_statement_17 hat_z_on_slice level_determinant_z)

theorem Ux10.phi_bound_of_slice_radical_cost (hM : SliceMem) (hR : RadicalParam) (hCP : DerivativeCostFromComponents) : PointwiseIntegralBound :=
  Ux10.phi_bound_parts_of_radical_parametrisation hR hM (Ux10.derivative_cost_of_slice_and_radical hM hR hCP) (Ux10.size_decay_of_slice_membership hM) weight_integrability

theorem phi_bound_of_parts : Formalism.FourierDecayAlt.U.PointwiseIntegralBoundFromComponents := Ux10.phi_bound_parts_of_radical_parametrisation radical_parametrisation

theorem phi_support_determinant : Formalism.FourierDecayAlt.U.PhiSupport := Ux10.phiSupport_of_parts slice_membership radical_parametrisation

theorem Ux10.phi_bound_of_derivative_cost_parts (hCP : DerivativeCostFromComponents) : PointwiseIntegralBound :=
  Ux10.phi_bound_of_slice_radical_cost slice_membership radical_parametrisation hCP

end Formalism.FourierDecayAlt.P
