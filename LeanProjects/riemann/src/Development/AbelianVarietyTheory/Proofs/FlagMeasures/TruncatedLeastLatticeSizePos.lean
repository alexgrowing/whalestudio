import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTrivialPointwise
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FgOfHtNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSeparated
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPointStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.RationalCount

abbrev op {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)

theorem norm_op_conj_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖op (g.map (starRingEnd ℂ))‖ ≤ ‖op g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  let u' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun i => starRingEnd ℂ (u i)
  have h1 : ‖u'‖ = ‖u‖ := by simp [u', EuclideanSpace.norm_eq]
  have h2 : ‖op (g.map (starRingEnd ℂ)) u‖ = ‖op g u'‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : op (g.map (starRingEnd ℂ)) u i = starRingEnd ℂ (op g u' i) := by
      simp [op, u', Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]
    rw [this, RCLike.norm_conj]
  rw [h2, ← h1]
  exact (op g).le_opNorm u'

theorem norm_op_conj {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ‖op (g.map (starRingEnd ℂ))‖ = ‖op g‖ := by
  refine le_antisymm (norm_op_conj_le g) ?_
  have h := norm_op_conj_le (g.map (starRingEnd ℂ))
  have e : (g.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g := by ext i j; simp
  rwa [e] at h

theorem finrank_op (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = 2 * n ^ 2 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    ← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n))
      (F' := EuclideanSpace ℂ (Fin n))).finrank_eq, Module.finrank_linearMap]
  simp [sq]

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  have key : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
    intro w
    rcases GlobalTheory.Count.Test.embedding_cases I w with h | h
    · rw [← h, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
  refine ⟨fun w w' h => ?_, InfinitePlace.comap_surjective⟩
  rw [key w, key w']
  exact congrArg (fun v => InfinitePlace.mk (I.φ v)) h

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, AutInst.f, IsTotallyReal.finrank,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem opNormAt_eq (x y : I.GA) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (w : InfinitePlace I.E) :
    opNormAt (bas I) (frm I y) (bas I) (frm I x) w (Matrix.toLin' δ) =
      ‖op ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
        δ.map (I.φ (w.comap (algebraMap I.F I.E))) *
        (I.P (w.comap (algebraMap I.F I.E)) * uMat (y.1 (w.comap (algebraMap I.F I.E)))))‖ := by
  have e : LinearMap.toMatrix (bas I) (bas I) (Matrix.toLin' δ) = δ := by simp [bas]
  unfold opNormAt frm
  rw [e]
  split_ifs with h
  · rw [h]
  · have h' := (GlobalTheory.Count.Test.embedding_cases I w).resolve_left h
    set v := w.comap (algebraMap I.F I.E)
    have hu : IsUnit (I.P v * uMat (x.1 v)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 ((I.P_unit v).mul (Units.isUnit _))
    have hJ : δ.map w.embedding = (δ.map (I.φ v)).map (starRingEnd ℂ) := by
      rw [h']; rfl
    have hi : ((I.P v * uMat (x.1 v)).map (starRingEnd ℂ))⁻¹ = (I.P v * uMat (x.1 v))⁻¹.map (starRingEnd ℂ) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
      simp [Matrix.map_one]
    rw [hJ, hi, ← Matrix.map_mul, ← Matrix.map_mul]
    exact norm_op_conj _

theorem uMat_eq (x y a : I.GA) (γ : Matrix (Fin I.n) (Fin I.n) I.E) (v : InfinitePlace I.F)
    (h : uMat (a.1 v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v) :
    uMat ((x⁻¹ * a * y).1 v) = (I.P v * uMat (x.1 v))⁻¹ * γ.map (I.φ v) * (I.P v * uMat (y.1 v)) := by
  have e : uMat ((x⁻¹ * a * y).1 v) = (uMat (x.1 v))⁻¹ * uMat (a.1 v) * uMat (y.1 v) := by
    simp [uMat]
  rw [e, h, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem mulVec_mem (x y a : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (hK : (x⁻¹ * a * y).2 ∈ I.Kset) (z : Fin I.n → I.E) (hz : z ∈ lamX I y) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I x := by
  have h1 := (GlobalTheory.Count.Test.lamX_equivariant I a y γ h z).2 hz
  rw [GlobalTheory.Count.Test.mem_lamX] at h1 ⊢
  have h2 := (hK _).1 h1
  have h3 : I.fmat (x⁻¹ * a * y).2 * I.fmat (a * y).2⁻¹ = I.fmat x.2⁻¹ := by
    have : (x⁻¹ * a * y).2 * (a * y).2⁻¹ = x.2⁻¹ := by simp [mul_assoc]
    rw [← this]; rfl
  rw [Matrix.mulVec_mulVec] at h2
  rw [← h3]
  exact h2

theorem lamX_ne_bot (hn : 1 ≤ I.n) (x : I.GA) : lamX I x ≠ ⊥ := by
  intro h0
  have h1 := (GlobalTheory.NearLowerCompare.lamX_isLattice I x).span_eq_top
  rw [h0] at h1
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  simp at h1

theorem truncatedLeastLatticeSize_pos (hn : 1 ≤ I.n) (x : I.GA) : 0 < tau1 I x :=
  lt_min (by norm_num) (GlobalTheory.StepDualityCompare.least_pos I x
    (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg (lamX_ne_bot I hn x))

theorem separated (hn : 1 ≤ I.n) (x y a b : I.GA) (ha : a ∈ I.GFset) (hb : b ∈ I.GFset)
    (haK : (x⁻¹ * a * y).2 ∈ I.Kset) (hbK : (x⁻¹ * b * y).2 ∈ I.Kset) (hab : a ≠ b) :
    tau1 I x * tau1 I y ≤ (∏ v, ‖op (uMat ((x⁻¹ * a * y).1 v)) - op (uMat ((x⁻¹ * b * y).1 v))‖) ^
      ((1 : ℝ) / Fintype.card (InfinitePlace I.F)) := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  obtain ⟨γ, -, hγ1, hγ2⟩ := ha
  obtain ⟨η, -, hη1, hη2⟩ := hb
  have hne : (γ : Matrix (Fin I.n) (Fin I.n) I.E) - η ≠ 0 := by
    intro h
    have h' : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = η := sub_eq_zero.1 h
    refine hab (Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_)))
    · exact (hγ1 v).trans (h' ▸ (hη1 v).symm)
    · exact hγ2.trans (h' ▸ hη2.symm)
  have hx := GlobalTheory.NearLowerCompare.lamX_isLattice I x
  have hy := GlobalTheory.NearLowerCompare.lamX_isLattice I y
  have h := sizeIneq I.E _ _ _ _ (bas I) (frm I y) (bas I) (frm I x)
    (GlobalTheory.NearLowerCompare.frm_isUnit I y) (GlobalTheory.NearLowerCompare.frm_isUnit I x)
    (Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - η)) (lamX I y) (lamX I x) hy.fg hx.fg
    (by
      rintro _ ⟨z, hz, rfl⟩
      have := sub_mem (mulVec_mem I x y a γ hγ2 haK z hz) (mulVec_mem I x y b η hη2 hbK z hz)
      simpa [Matrix.sub_mulVec] using this)
    (by
      intro h0
      apply hne
      apply Matrix.toLin'.injective
      rw [map_zero]
      refine LinearMap.ext_on hy.span_eq_top fun z hz => ?_
      exact (Submodule.eq_bot_iff _).1 h0 _ ⟨z, hz, rfl⟩)
  rw [(GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I y).2.1 hn, div_inv_eq_mul] at h
  have e1 : (nPl I.E : ℝ) = Fintype.card (InfinitePlace I.F) := by
    rw [nPl, Fintype.card_of_bijective (comap_bijective I)]
  have e2 : ∏ w, opNormAt (bas I) (frm I y) (bas I) (frm I x) w
      (Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - η)) =
      ∏ v, ‖op (uMat ((x⁻¹ * a * y).1 v)) - op (uMat ((x⁻¹ * b * y).1 v))‖ := by
    refine Fintype.prod_bijective _ (comap_bijective I) _ _ fun w => ?_
    rw [opNormAt_eq, uMat_eq I x y a γ _ (hγ1 _), uMat_eq I x y b η _ (hη1 _), op, op, op, ← map_sub, ← map_sub,
      Matrix.map_sub _ (map_sub _), Matrix.mul_sub, Matrix.sub_mul]
  rw [e1, e2] at h
  refine le_trans ?_ h
  exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (truncatedLeastLatticeSize_pos I hn y).le
    ((truncatedLeastLatticeSize_pos I hn x).le.trans (min_le_right _ _))

theorem count_le (I : AutInst) (x y : I.GA) (r : InfinitePlace I.F → ℝ) (hn : 1 ≤ I.n) (_hr : ∀ v, 0 ≤ r v) :
    {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}.Finite ∧
    (({a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧
        ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
      (1 + 2 * Real.sqrt I.n * Real.exp ((∑ v, r v) / I.f) / (tau1 I x * tau1 I y)) ^ (2 * (I.n ^ 2 * I.f)) := by
  set A := {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * y).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * y).1 v)) ≤ r v}
  let s : I.GA → InfinitePlace I.F → (EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) :=
    fun a v => op (uMat ((x⁻¹ * a * y).1 v))
  have hla : 0 < tau1 I x * tau1 I y := mul_pos (truncatedLeastLatticeSize_pos I hn x) (truncatedLeastLatticeSize_pos I hn y)
  have hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → tau1 I x * tau1 I y ≤
      (∏ v, ‖s a v - s b v‖) ^ ((1 : ℝ) / Fintype.card (InfinitePlace I.F)) :=
    fun a ha b hb hab => separated I hn x y a b ha.1 hb.1 ha.2.1 hb.2.1 hab
  have hcard : (0 : ℝ) < Fintype.card (InfinitePlace I.F) := by exact_mod_cast Fintype.card_pos
  have hinj : Set.InjOn s A := by
    intro a ha b hb h
    by_contra hab
    have := hsep a ha b hb hab
    rw [h] at this
    simp only [sub_self, norm_zero, Finset.prod_const, Finset.card_univ] at this
    rw [zero_pow Fintype.card_ne_zero, Real.zero_rpow (one_div_pos.2 hcard).ne'] at this
    exact absurd this (not_le.2 hla)
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) :=
    Module.Finite.trans ℂ _
  obtain ⟨hfin, hle⟩ := GlobalTheory.packing_geometric_mean_separated (InfinitePlace I.F)
    (fun _ => EuclideanSpace ℂ (Fin I.n) →L[ℂ] EuclideanSpace ℂ (Fin I.n)) (2 * I.n ^ 2)
    (by nlinarith) (fun _ => finrank_op I.n) (tau1 I x * tau1 I y) (s '' A) (fun v => Real.exp (r v)) hla
    (fun v => Real.exp_pos _) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      exact hsep a ha b hb fun h => hab (by rw [h]))
  have hA : {t ∈ s '' A | ∀ v, ‖t v‖ ≤ Real.exp (r v)} = s '' A := by
    refine Set.sep_eq_self_iff_mem_true.2 ?_
    rintro _ ⟨a, ha, rfl⟩ v
    exact (Real.le_exp_log _).trans (Real.exp_le_exp.2 (ha.2.2 v))
  rw [hA] at hfin hle
  refine ⟨hfin.of_finite_image hinj, ?_⟩
  rw [hinj.ncard_image, ← Real.exp_sum, ← Real.exp_mul, card_places, mul_one_div, mul_assoc 2 (I.n ^ 2)] at hle
  refine hle.trans (pow_le_pow_left₀ (by positivity) ?_ _)
  have h1 : (1 : ℝ) ≤ Real.sqrt I.n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have h2 := Real.exp_pos ((∑ v, r v) / I.f)
  gcongr
  linarith

end GlobalTheory.RationalCount
