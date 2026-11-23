import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvLeSizeQAboveOrthogonalSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubquotientCoveringRadiusRealPlacesStatement

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.Count.CentralCover

section Form

variable {K : Type} [Field K] [StarRing K] {n : ℕ}

local notation "h" => Formalism.UG.hform (starRingEnd K)

theorem hform_eq (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    h J x y = star x ⬝ᵥ J *ᵥ y := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

def adj (J M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := J⁻¹ * Mᴴ * J

theorem adj_left {J : Matrix (Fin n) (Fin n) K} (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) K)
    (u v : Fin n → K) : h J (M *ᵥ u) v = h J u (adj J M *ᵥ v) := by
  rw [hform_eq, hform_eq, adj, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, star_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec (star u) Mᴴ]

theorem adj_right {J : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) K)
    (u v : Fin n → K) : h J (adj J M *ᵥ u) v = h J u (M *ᵥ v) := by
  rw [PerpStep.hform_swap hJ, ← adj_left hd, ← PerpStep.hform_swap hJ]

theorem mem_of_perp_perp {J : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (W : Submodule K (Fin n → K)) (y : Fin n → K)
    (hy : ∀ p ∈ perpSet (starRingEnd K) J W, h J p y = 0) : y ∈ W := by
  by_contra hn
  obtain ⟨f, hf, hW⟩ := W.exists_dual_map_eq_bot_of_notMem hn inferInstance
  set c : Fin n → K := fun j => f (Pi.single j 1) with hc
  have key : ∀ z, h J (star (c ᵥ* J⁻¹)) z = f z := by
    intro z
    rw [hform_eq, star_star, dotProduct_mulVec, vecMul_vecMul,
      Matrix.nonsing_inv_mul _ (Ne.isUnit hd), vecMul_one]
    conv_rhs => rw [← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (Pi.single j (z j) : Fin n → K) = z j • (Pi.single j 1 : Fin n → K) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  refine hf ?_
  rw [← key]
  refine hy _ fun w hw => ?_
  have h0 : f w = 0 := by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rwa [hW, Submodule.mem_bot] at this
  rw [PerpStep.hform_swap hJ, key, h0, star_zero]

theorem eq_zero_of_perp {J : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (y : Fin n → K) (hy : ∀ p, h J p y = 0) : y = 0 :=
  (Submodule.mem_bot K).1 (mem_of_perp_perp hJ hd ⊥ y fun p _ => hy p)

theorem adj_of_skew {J Z : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) (hZ : IsSkew (starRingEnd K) J Z) : adj J Z = -Z := by
  refine Matrix.ext_iff_mulVec.2 fun u => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_perp hJ hd _ fun p => ?_
  have h1 := hZ p u
  rw [adj_left hd, hform_eq, hform_eq] at h1
  rw [hform_eq, neg_mulVec, sub_neg_eq_add, mulVec_add, dotProduct_add, h1]

theorem range_of_inCen {J Z : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) {W : Submodule K (Fin n → K)} (hZ : InCen (starRingEnd K) J W Z)
    (u : Fin n → K) : Z *ᵥ u ∈ W := by
  refine mem_of_perp_perp hJ hd W _ fun p hp => ?_
  have h1 := hZ.1.1 p u
  rw [hZ.2 p hp] at h1
  simpa [hform_eq] using h1

theorem inCen_sub_adj {J Φ : Matrix (Fin n) (Fin n) K} (hJ : Formalism.UG.IsHerm (starRingEnd K) J)
    (hd : J.det ≠ 0) {W : Submodule K (Fin n → K)} (hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd K) J W)
    (h1 : ∀ u, Φ *ᵥ u ∈ W) (h2 : ∀ p ∈ perpSet (starRingEnd K) J W, Φ *ᵥ p = 0) :
    InCen (starRingEnd K) J W (Φ - adj J Φ) := by
  have h3 : ∀ u, (Φ - adj J Φ) *ᵥ u ∈ W := by
    intro u
    rw [sub_mulVec]
    refine sub_mem (h1 u) (mem_of_perp_perp hJ hd W _ fun p hp => ?_)
    rw [← adj_left hd, h2 p hp]
    simp [hform_eq]
  have h4 : ∀ p ∈ perpSet (starRingEnd K) J W, (Φ - adj J Φ) *ᵥ p = 0 := by
    intro p hp
    rw [sub_mulVec, h2 p hp, eq_zero_of_perp hJ hd (adj J Φ *ᵥ p) fun u => ?_, sub_zero]
    rw [← adj_left hd]
    exact hp _ (h1 u)
  refine ⟨⟨fun u u' => ?_, fun u => hW _ (h3 u), fun u _ => h3 u, fun u hu => h4 u (hW u hu)⟩, h4⟩
  have e1 := adj_left hd Φ u u'
  have e2 := adj_right hJ hd Φ u u'
  simp only [hform_eq] at e1 e2 ⊢
  simp only [sub_mulVec, star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
  rw [e1, e2]
  ring

theorem adj_map {J : Matrix (Fin n) (Fin n) K} (hd : J.det ≠ 0) (φ : K →+* ℂ)
    (hs : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) (M : Matrix (Fin n) (Fin n) K) :
    (adj J M).map φ = adj (J.map φ) (M.map φ) := by
  have e1 : (J.map φ)⁻¹ = J⁻¹.map φ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hd), Matrix.map_one φ φ.map_zero φ.map_one]
  have e2 : Mᴴ.map φ = (M.map φ)ᴴ := by
    ext i j
    simp [hs]
  rw [adj, adj, Matrix.map_mul, Matrix.map_mul, e1, e2]

end Form

section Norm

variable {n : ℕ}

theorem hs_nonneg' (a : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs a := by
  unfold hs; positivity

theorem hs_sub_le (a b : Matrix (Fin n) (Fin n) ℂ) : hs (a - b) ≤ 2 * hs a + 2 * hs b := by
  unfold hs
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 : ‖(a - b) i j‖ ≤ ‖a i j‖ + ‖b i j‖ := norm_sub_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a i j‖ - ‖b i j‖)]

theorem hs_flip (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : hs (Jm ε * aᴴ * Jm ε) = hs a := by
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp

theorem hs_adj (ε : Fin n → Bool) {J A G : Matrix (Fin n) (Fin n) ℂ} (hd : J.det ≠ 0)
    (hGA : G * A = 1) (hG : Gᴴ * J * G = Jm ε) (D : Matrix (Fin n) (Fin n) ℂ) :
    hs (A * adj J D * G) = hs (A * D * G) := by
  have e1 : J * G = Aᴴ * Jm ε := by
    rw [← hG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, hGA, conjTranspose_one,
      Matrix.one_mul]
  have e2 : A = Jm ε * Gᴴ * J := by
    have : Jm ε * (Gᴴ * J * G) * A = A := by rw [hG, Jm_mul_self, Matrix.one_mul]
    rw [← this]
    simp only [Matrix.mul_assoc, hGA, Matrix.mul_one]
  have e3 : A * J⁻¹ = Jm ε * Gᴴ := by
    rw [e2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.mul_one]
  rw [← hs_flip ε (A * D * G)]
  congr 1
  calc A * adj J D * G = (A * J⁻¹) * Dᴴ * (J * G) := by simp only [adj, Matrix.mul_assoc]
    _ = _ := by rw [e1, e3]; simp only [conjTranspose_mul, Matrix.mul_assoc]

end Norm

section Main

variable (I : AutInst) (x : I.GA)

theorem det_map_ne (v : InfinitePlace I.F) : (I.J.map (I.φ v)).det ≠ 0 := by
  have := (I.φ v).map_det I.J
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact (map_ne_zero _).2 I.J_det

theorem herm_map (v : InfinitePlace I.F) : Formalism.UG.IsHerm (starRingEnd ℂ) (I.J.map (I.φ v)) := by
  ext i j
  have h1 : star (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  have h2 := I.cm.cmUnram.2.1 (I.φ v) (I.J j i)
  change starRingEnd ℂ (I.φ v (I.J j i)) = I.φ v (I.J i j)
  rw [← h1, h2]

theorem normAt_sub_adj (D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :
    normAt I x (fun v => D v - adj (I.J.map (I.φ v)) (D v)) ≤ 2 * normAt I x D := by
  unfold normAt
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num),
    Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => ?_)
  have hx : uMat (x.1 v) * uMat (x.1 v)⁻¹ = 1 := Units.mul_inv _
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hU : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  have key := hs_adj (I.ε v) (A := uMat (x.1 v)⁻¹ * (I.P v)⁻¹) (G := I.P v * uMat (x.1 v))
    (det_map_ne I v)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uMat (x.1 v)), hx, Matrix.one_mul, hP])
    (by rw [← hU, ← I.P_spec v]; simp only [conjTranspose_mul, Matrix.mul_assoc]) (D v)
  have h2 := hs_sub_le (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * D v * (I.P v * uMat (x.1 v)))
    (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * adj (I.J.map (I.φ v)) (D v) * (I.P v * uMat (x.1 v)))
  rw [key, ← Matrix.sub_mul, ← Matrix.mul_sub] at h2
  simp only [Matrix.mul_assoc] at h2 ⊢
  linarith

end Main

theorem main : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → hi ^ 2 ≤ rho / 4 → ∀ Z ∈ cenReal I R, ∃ Z₀ ∈ cenInt I x R, normAt I x (Z - diagEmb I Z₀) ≤ ((I.n : ℝ) ^ 2 * I.f) * I.rd * rho / (16 * Real.sqrt I.f) := by
  intro I x R hi rho hR hRp hhi hls hrho Z hZ
  obtain ⟨-, hA, hsp, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨hS, hrk, -⟩ := (PerpStep.main I x).2.2.2 R R hR hR le_rfl
  obtain ⟨-, htop, hperp, -⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  have hmem : ∀ y, y ∈ perpIn I x R ↔
      y ∈ lamX I x ∧ ∀ s ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
    intro y
    rw [PerpStep.perpIn_eq, PerpStep.mem_perp]
  obtain ⟨Φ, hΦS, hΦA, D, hD, hn⟩ := GlobalTheory.T.subquotient_covering_radius_real_places I x (lamX I x) (perpIn I x R) R hi⁻¹ hi hA hS
    (Submodule.FG.of_le hA hR.1) (inv_pos.2 hhi) hhi (GlobalTheory.T.inv_le_sizeQ_above_orthogonal_saturated I x R hi hR hhi hls) hls
    (fun v => (1 / 2 : ℂ) • Z v)
    (by
      intro v y hy
      have : (fun i => I.φ v (y i)) ∈ (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      rw [hperp v] at this
      rw [smul_mulVec, (hZ v).2 _ this, smul_zero])
    (by
      intro v y _
      rw [smul_mulVec]
      exact Submodule.smul_mem _ _ (range_of_inCen (herm_map I v) (det_map_ne I v) (hZ v) _))
  have hD' : ∀ v, D v = (1 / 2 : ℂ) • Z v - Φ.map (I.φ v) := fun v =>
    Matrix.ext_iff_mulVec.2 fun u => hD v u (by rw [htop v]; trivial)
  set W := Submodule.span I.E (R : Set (Fin I.n → I.E)) with hWdef
  have hpW : ∀ y, (∀ s ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0) →
      y ∈ perpSet (starRingEnd I.E) I.J W := by
    intro y hy w hw
    induction hw using Submodule.span_induction with
    | mem s hs => exact hy s hs
    | zero => simp [hform_eq]
    | add a b _ _ ha hb =>
      rw [hform_eq] at ha hb ⊢
      rw [star_add, add_dotProduct, ha, hb, add_zero]
    | smul c a _ ha =>
      rw [hform_eq] at ha ⊢
      rw [star_smul, smul_dotProduct, ha, smul_zero]
  have hWW : ∀ w ∈ W, w ∈ perpSet (starRingEnd I.E) I.J W := by
    intro w hw
    refine hpW w fun s hs => ?_
    rw [PerpStep.hform_swap I.J_herm, hpW s ((hmem s).1 (hRp hs)).2 w hw, star_zero]
  have h1 : ∀ u, Φ *ᵥ u ∈ W := by
    intro u
    have hu : u ∈ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) := by rw [hsp]; trivial
    induction hu using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (hΦA s hs)
    | zero => simp
    | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have h2 : ∀ p ∈ perpSet (starRingEnd I.E) I.J W, Φ *ᵥ p = 0 := by
    intro p hp
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 I.E)) I.E
      (lamX I x : Set (Fin I.n → I.E)) p (by rw [hsp]; trivial)
    rw [Submodule.span_eq] at ht
    have e : t • p = algebraMap (𝓞 I.E) I.E t • p := by
      rw [algebraMap_smul]; rfl
    rw [e] at ht
    have h0 : algebraMap (𝓞 I.E) I.E t ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 I.E) I.E)).2 (nonZeroDivisors.coe_ne_zero t)
    have h3 := hΦS _ ((hmem _).2 ⟨ht, fun s hs => by
      have := hp s (Submodule.subset_span hs)
      rw [hform_eq] at this ⊢
      rw [mulVec_smul, dotProduct_smul, this, smul_zero]⟩)
    rw [mulVec_smul] at h3
    exact (smul_eq_zero.1 h3).resolve_left h0
  refine ⟨Φ - adj I.J Φ, ⟨inCen_sub_adj I.J_herm I.J_det hWW h1 h2, fun u hu => ?_⟩, ?_⟩
  · rw [sub_mulVec]
    refine sub_mem (hR.1 (hΦA u hu)) ((hdual _).2 fun z hz => ?_)
    rw [← adj_left I.J_det]
    exact (hdual u).1 hu _ (hR.1 (hΦA z hz))
  · have e : Z - diagEmb I (Φ - adj I.J Φ) = fun v => D v - adj (I.J.map (I.φ v)) (D v) := by
      funext v
      have a1 := adj_of_skew (herm_map I v) (det_map_ne I v) (hZ v).1.1
      have a2 := adj_map I.J_det (I.φ v) (I.cm.cmUnram.2.1 (I.φ v)) Φ
      have a3 : adj (I.J.map (I.φ v)) (D v) = (1 / 2 : ℂ) • adj (I.J.map (I.φ v)) (Z v) -
          adj (I.J.map (I.φ v)) (Φ.map (I.φ v)) := by
        rw [hD' v]
        simp [adj, conjTranspose_sub, conjTranspose_smul, Matrix.mul_sub, Matrix.sub_mul]
      rw [a3, a1, ← a2, hD' v, Pi.sub_apply, diagEmb, Matrix.map_sub _ (map_sub (I.φ v))]
      module
    rw [e]
    refine (normAt_sub_adj I x D).trans ?_
    have hrkA : rkK (lamX I x) = I.n := by
      unfold rkK
      rw [hsp, finrank_top]
      simp
    have hle : rkK R ≤ rkK (perpIn I x R) := Submodule.finrank_mono (Submodule.span_mono hRp)
    have r1 : (rkK (lamX I x) : ℝ) - rkK (perpIn I x R) = rkK R := by
      have : (rkK (perpIn I x R) : ℝ) + rkK R = I.n := by exact_mod_cast hrk
      rw [hrkA]
      linarith
    have r2 : 2 * (rkK R : ℝ) ≤ I.n := by
      have : 2 * rkK R ≤ I.n := by omega
      exact_mod_cast this
    rw [r1] at hn
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    have hj : (0 : ℝ) ≤ rkK R := Nat.cast_nonneg _
    have r3 : (rkK R : ℝ) ^ 2 ≤ (I.n : ℝ) ^ 2 / 4 := by nlinarith
    have r4 : ((I.n : ℝ) ^ 2 * I.f) * I.rd * rho / (16 * Real.sqrt I.f) =
        (I.n : ℝ) ^ 2 / 4 * (rho / 4) * (Real.sqrt I.f * I.rd) := by
      conv_rhs => rw [← Real.div_sqrt]
      ring
    have r5 : 2 * ((rkK R : ℝ) * rkK R * Real.sqrt I.f * I.rd * hi / (2 * hi⁻¹)) =
        (rkK R : ℝ) ^ 2 * hi ^ 2 * (Real.sqrt I.f * I.rd) := by
      field_simp
    rw [r4]
    refine (mul_le_mul_of_nonneg_left hn (by norm_num)).trans ?_
    rw [r5]
    exact mul_le_mul_of_nonneg_right (mul_le_mul r3 hrho (sq_nonneg _) (by positivity))
      (mul_nonneg (Real.sqrt_nonneg _) hrd)

end GlobalTheory.Count.CentralCover
