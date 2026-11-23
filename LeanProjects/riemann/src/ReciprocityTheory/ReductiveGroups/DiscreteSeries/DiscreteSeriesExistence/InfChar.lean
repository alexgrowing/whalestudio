import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Resolvent
import Formalism.FormalDegreeBessel.StatementIO
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Gelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.AntiEIsGlRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

section Fun

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem icx_smooth_eabV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) (a b : Fin n) :
    S7.SmoothOnGV ε (S7.EabV ε a b f) := by
  obtain ⟨h1, h2, -, -⟩ := smc_cpart (ε := ε) (Matrix.single a b 1)
  exact smoothOnGV_add (smoothOnGV_rdV hf h1) (smoothOnGV_smul Complex.I (smoothOnGV_rdV hf h2))

theorem icx_eabV_add_smul {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    (hf' : S7.SmoothOnGV ε f') (c : ℂ) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    S7.EabV ε a b (fun h => f h + c • f' h) g = S7.EabV ε a b f g + c • S7.EabV ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := smc_cpart (ε := ε) (Matrix.single a b 1)
  show S7.RdV (S7.cpart1 ε (Matrix.single a b 1)) (fun h => f h + c • f' h) g +
      Complex.I • S7.RdV (S7.cpart2 ε (Matrix.single a b 1)) (fun h => f h + c • f' h) g =
    (S7.RdV (S7.cpart1 ε (Matrix.single a b 1)) f g + Complex.I • S7.RdV (S7.cpart2 ε (Matrix.single a b 1)) f g) +
      c • (S7.RdV (S7.cpart1 ε (Matrix.single a b 1)) f' g +
        Complex.I • S7.RdV (S7.cpart2 ε (Matrix.single a b 1)) f' g)
  rw [rdV_add_smul_fun hf hf' c h1 hg, rdV_add_smul_fun hf hf' c h2 hg, smul_add, smul_add,
    smul_comm c Complex.I]
  abel

private theorem Jm_mul_Jm_eq_oneDiscreteSeriesExistence : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeDiscreteSeriesExistence : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

private theorem Jm_mul_Jm_conj_conjTranspose (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_Jm_eq_oneDiscreteSeriesExistence, Matrix.one_mul]

private theorem Jm_conj_conjTranspose_mul_Jm (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Jm ε * Zᴴ * Jm ε)ᴴ * Jm ε = Jm ε * Z := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTransposeDiscreteSeriesExistence,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_Jm_eq_oneDiscreteSeriesExistence, Matrix.mul_one]

private theorem inG_cpart1' (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (S7.cpart1 ε Z) := by
  unfold inG S7.cpart1
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Jm_mul_Jm_conj_conjTranspose, Jm_conj_conjTranspose_mul_Jm]
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hc, ← smul_add, show Zᴴ * Jm ε - Jm ε * Z + (Jm ε * Z - Zᴴ * Jm ε) = 0 by abel, smul_zero]

private theorem inG_cpart2' (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (S7.cpart2 ε Z) := by
  unfold inG S7.cpart2
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Jm_mul_Jm_conj_conjTranspose, Jm_conj_conjTranspose_mul_Jm]
  have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [hc, neg_smul, add_comm (Jm ε * Z)]
  abel

private theorem inUJ_mul_exp_smul_of_inG {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (t : ℝ) :
    inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) := by
  have hX0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX0
  unfold inUJ at hg ⊢
  set Y := (t : ℂ) • X with hY
  have hYJ : Yᴴ * Jm ε = Jm ε * -Y := by
    rw [hY, Matrix.conjTranspose_smul, Matrix.smul_mul, hX', Matrix.mul_neg, Matrix.mul_smul, smul_neg]
    simp
  have hYc : Yᴴ = Jm ε * -Y * Jm ε := by
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Jm_mul_Jm_eq_oneDiscreteSeriesExistence, Matrix.mul_one]
      _ = Jm ε * -Y * Jm ε := by rw [hYJ]
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv Jm_mul_Jm_eq_oneDiscreteSeriesExistence
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_Jm_eq_oneDiscreteSeriesExistence, Jm_mul_Jm_eq_oneDiscreteSeriesExistence⟩, rfl⟩
  have hE : (NormedSpace.exp Y)ᴴ = Jm ε * NormedSpace.exp (-Y) * Jm ε := by
    rw [← Matrix.exp_conjTranspose, hYc]
    have := Matrix.exp_conj (Jm ε) (-Y) hJu
    rw [hJinv] at this
    exact this
  have e1 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  have step : (g * NormedSpace.exp Y)ᴴ * Jm ε * (g * NormedSpace.exp Y) =
      (NormedSpace.exp Y)ᴴ * (gᴴ * Jm ε * g) * NormedSpace.exp Y := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [step, hg, hE, Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), Jm_mul_Jm_eq_oneDiscreteSeriesExistence,
    Matrix.mul_one, Matrix.mul_assoc, e1, Matrix.mul_one]

theorem icx_eabV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : S7.EabV ε a b f g = S7.EabV ε a b f' g := by
  have key : ∀ X, inG ε X → (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X)) :=
    fun X hX => funext fun t => h _ (inUJ_mul_exp_smul_of_inG hg hX t)
  have k1 := key _ (inG_cpart1' (ε := ε) (Matrix.single a b 1))
  have k2 := key _ (inG_cpart2' (ε := ε) (Matrix.single a b 1))
  simp only [S7.EabV, S7.EcV, S7.RdV]
  rw [k1, k2]

theorem icx_eabV_clm (φ : E →L[ℂ] ℂ) {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    S7.EabV ε a b (fun x => φ (f x)) g = φ (S7.EabV ε a b f g) := by
  obtain ⟨h1, h2, -, -⟩ := smc_cpart (ε := ε) (Matrix.single a b 1)
  show S7.RdV (S7.cpart1 ε (Matrix.single a b 1)) (fun x => φ (f x)) g +
      Complex.I • S7.RdV (S7.cpart2 ε (Matrix.single a b 1)) (fun x => φ (f x)) g =
    φ (S7.RdV (S7.cpart1 ε (Matrix.single a b 1)) f g + Complex.I • S7.RdV (S7.cpart2 ε (Matrix.single a b 1)) f g)
  rw [rdV_clm φ hf h1 hg, rdV_clm φ hf h2 hg, map_add, map_smul]

end Fun

section Scalar

theorem icx_eab_eq (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n) :
    Formalism.REAL.Eab ε a b F = S7.EabV ε a b F := rfl

theorem icx_eword_congr {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → F g = G g) :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.REAL.Eword ε w F g = Formalism.REAL.Eword ε w G g
  | [], g, hg => h g hg
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      rw [icx_eab_eq, icx_eab_eq]
      exact icx_eabV_congr (fun g' hg' => icx_eword_congr h w g' hg') p.1 p.2 hg

theorem isSmoothL2_congr {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F)
    (h : ∀ g, inUJ ε g → F g = G g) : IsSmoothL2 ε G := by
  unfold IsSmoothL2 Formalism.REAL.SmoothOnG at hF ⊢
  refine ⟨fun g₀ hg₀ => ?_, fun w => ?_⟩
  · obtain ⟨U, F', hU, hg, hF', hE⟩ := hF.1 g₀ hg₀
    exact ⟨U, F', hU, hg, hF', fun g hgU hgJ => by rw [← h g hgJ]; exact hE g hgU hgJ⟩
  · have e : (fun y : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w G (Formalism.MainNotions.S.umat y)) =
        fun y => Formalism.REAL.Eword ε w F (Formalism.MainNotions.S.umat y) :=
      funext fun y => (icx_eword_congr h w (Formalism.MainNotions.S.umat y) y.2).symm
    rw [e]
    exact hF.2 w

theorem icx_eword_zero : ∀ w : List (Fin n × Fin n),
    Formalism.REAL.Eword ε w (fun _ => (0 : ℂ)) = fun _ => 0
  | [] => rfl
  | p :: w => by
      simp only [Formalism.REAL.Eword]
      rw [icx_eword_zero w]
      funext g
      simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

theorem isSmoothL2_zero : IsSmoothL2 ε (fun _ => (0 : ℂ)) := by
  unfold IsSmoothL2 Formalism.REAL.SmoothOnG
  refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const,
    fun _ _ _ => rfl⟩, fun w => ?_⟩
  rw [icx_eword_zero]
  exact MemLp.zero

theorem icx_eword_add_smul {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F)
    (hG : Formalism.REAL.SmoothOnG ε G) (c : ℂ) :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.REAL.Eword ε w (fun x => F x + c * G x) g = Formalism.REAL.Eword ε w F g + c * Formalism.REAL.Eword ε w G g
  | [], g, _ => rfl
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      rw [icx_eab_eq, icx_eab_eq, icx_eab_eq,
        icx_eabV_congr (fun g' hg' => icx_eword_add_smul hF hG c w g' hg') p.1 p.2 hg]
      exact icx_eabV_add_smul (Formalism.REAL.smooth_iterated_lie_derivative hF w) (Formalism.REAL.smooth_iterated_lie_derivative hG w) c p.1 p.2 hg

theorem isSmoothL2_add_smul {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F)
    (hG : IsSmoothL2 ε G) (c : ℂ) : IsSmoothL2 ε (fun x => F x + c * G x) := by
  unfold IsSmoothL2 Formalism.REAL.SmoothOnG at hF hG ⊢
  refine ⟨fun g₀ hg₀ => ?_, fun w => ?_⟩
  · obtain ⟨U, F', hU, hgU, hF', hE⟩ := hF.1 g₀ hg₀
    obtain ⟨U', G', hU', hgU', hG', hE'⟩ := hG.1 g₀ hg₀
    refine ⟨U ∩ U', fun g => F' g + c * G' g, hU.inter hU', ⟨hgU, hgU'⟩, ?_, fun g hg hgJ => ?_⟩
    · exact (hF'.mono Set.inter_subset_left).add (contDiffOn_const.mul (hG'.mono Set.inter_subset_right))
    · simp only [hE g hg.1 hgJ, hE' g hg.2 hgJ]
  · have e : (fun y : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w (fun x => F x + c * G x) (Formalism.MainNotions.S.umat y)) =
        fun y => Formalism.REAL.Eword ε w F (Formalism.MainNotions.S.umat y) + c * Formalism.REAL.Eword ε w G (Formalism.MainNotions.S.umat y) :=
      funext fun y => icx_eword_add_smul hF.1 hG.1 c w (Formalism.MainNotions.S.umat y) y.2
    rw [e]
    exact (hF.2 w).add ((hG.2 w).const_mul c)

end Scalar

section Good

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def IcxGood (ε : Fin n → Bool) (φ : E →L[ℂ] ℂ) (x : smD ε (rreg ε)) (Φ : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  S7.SmoothOnGV ε Φ ∧ IsSmoothL2 ε (fun g => φ (Φ g)) ∧ (x : L2 ε) = toL2 ε (fun g => φ (Φ g))

variable {φ : E →L[ℂ] ℂ}

private theorem toL2_congr_of_inUJ_eq {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → F g = G g) :
    toL2 ε F = toL2 ε G := by
  have hfg : (fun y : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat y)) = fun y => G (Formalism.MainNotions.S.umat y) :=
    funext fun y => h _ y.2
  unfold toL2
  rw [hfg]

private theorem toL2_zero' : toL2 ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : ℂ)) = 0 := by
  simp only [toL2]
  rw [dif_pos (show MemLp (fun _ : Formalism.REAL.UJ ε => (0 : ℂ)) 2 (Formalism.REAL.muG ε) from MemLp.zero)]
  exact MemLp.toLp_zero _

private theorem toL2_add_mul_of_memLp (F G : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : MemLp (fun y : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat y)) 2 (Formalism.REAL.muG ε))
    (hG : MemLp (fun y : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat y)) 2 (Formalism.REAL.muG ε)) (c : ℂ) :
    toL2 ε (fun x => F x + c * G x) = toL2 ε F + c • toL2 ε G := by
  have hFG : MemLp (fun y : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat y) + c * G (Formalism.MainNotions.S.umat y)) 2
      (Formalism.REAL.muG ε) := hF.add (hG.const_mul c)
  simp only [toL2, dif_pos hF, dif_pos hG, dif_pos hFG]
  rw [← MemLp.toLp_const_smul c hG, ← MemLp.toLp_add hF (hG.const_smul c)]
  rfl

theorem icxGood_congr {x x' : smD ε (rreg ε)} {Φ Φ' : Matrix (Fin n) (Fin n) ℂ → E}
    (h : IcxGood ε φ x Φ) (hx : x = x') (hΦ : ∀ g, inUJ ε g → Φ g = Φ' g) : IcxGood ε φ x' Φ' := by
  obtain ⟨h1, h2, h3⟩ := h
  subst hx
  unfold IcxGood
  refine ⟨?_, isSmoothL2_congr h2 (fun g hg => by simp only [hΦ g hg]), ?_⟩
  · unfold S7.SmoothOnGV at h1 ⊢
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hE⟩ := h1 g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => by rw [← hΦ g hgJ]; exact hE g hg hgJ⟩
  · rw [h3]
    exact toL2_congr_of_inUJ_eq (fun g hg => by simp only [hΦ g hg])

theorem icxGood_zero : IcxGood ε φ 0 (fun _ => (0 : E)) := by
  unfold IcxGood
  refine ⟨?_, ?_, ?_⟩
  · unfold S7.SmoothOnGV
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  · simpa using (isSmoothL2_zero (ε := ε))
  · simp only [map_zero, Submodule.coe_zero]
    exact toL2_zero'.symm

private theorem smoothOnGV_add_smul {Φ Φ' : Matrix (Fin n) (Fin n) ℂ → E}
    (hΦ : S7.SmoothOnGV ε Φ) (hΦ' : S7.SmoothOnGV ε Φ') (c : ℂ) :
    S7.SmoothOnGV ε (fun g => Φ g + c • Φ' g) := by
  unfold S7.SmoothOnGV at hΦ hΦ' ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hΦ g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hE'⟩ := hΦ' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + c • F' g, hU.inter hU', ⟨hgU, hgU'⟩, ?_, fun g hg hgJ => ?_⟩
  · exact (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
  · simp only [hE g hg.1 hgJ, hE' g hg.2 hgJ]

theorem icxGood_add_smul {x y : smD ε (rreg ε)} {Φ Φ' : Matrix (Fin n) (Fin n) ℂ → E}
    (hx : IcxGood ε φ x Φ) (hy : IcxGood ε φ y Φ') (c : ℂ) :
    IcxGood ε φ (x + c • y) (fun g => Φ g + c • Φ' g) := by
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨k1, k2, k3⟩ := hy
  unfold IcxGood
  refine ⟨smoothOnGV_add_smul h1 k1 c, ?_, ?_⟩
  · have := isSmoothL2_add_smul h2 k2 c
    simpa [map_add, map_smul] using this
  · have m1 : MemLp (fun y : Formalism.REAL.UJ ε => φ (Φ (Formalism.MainNotions.S.umat y))) 2 (Formalism.REAL.muG ε) := h2.2 []
    have m2 : MemLp (fun y : Formalism.REAL.UJ ε => φ (Φ' (Formalism.MainNotions.S.umat y))) 2 (Formalism.REAL.muG ε) := k2.2 []
    rw [Submodule.coe_add, Submodule.coe_smul, h3, k3,
      ← toL2_add_mul_of_memLp (fun g => φ (Φ g)) (fun g => φ (Φ' g)) m1 m2 c]
    congr 1
    funext g
    simp [map_add, map_smul]

theorem icxGood_neg {x : smD ε (rreg ε)} {Φ : Matrix (Fin n) (Fin n) ℂ → E} (hx : IcxGood ε φ x Φ) :
    IcxGood ε φ (-x) (fun g => -Φ g) := by
  have h := icxGood_add_smul (icxGood_zero (ε := ε) (φ := φ)) hx (-1)
  exact icxGood_congr h (by simp) (fun g _ => by simp)

theorem icxGood_eab {x : smD ε (rreg ε)} {Φ : Matrix (Fin n) (Fin n) ℂ → E} (hx : IcxGood ε φ x Φ) (a b : Fin n) :
    IcxGood ε φ (smE ε (rreg ε) a b x) (S7.EabV ε a b Φ) := by
  have hc : ∀ g, inUJ ε g → Formalism.REAL.Eab ε a b (fun g => φ (Φ g)) g = φ (S7.EabV ε a b Φ g) :=
    fun g hg => icx_eabV_clm φ hx.1 a b hg
  refine ⟨icx_smooth_eabV hx.1 a b, isSmoothL2_congr (hx.2.1.Eab a b) hc, ?_⟩
  have e : x = ⟨toL2 ε (fun g => φ (Φ g)), toL2_mem_smD_of_isSmoothL2 hx.2.1⟩ := Subtype.ext hx.2.2
  rw [e, rightDerivative_toL2 hx.2.1 a b]
  exact toL2_congr_of_forall_inUJ_eq hc

theorem icxGood_sum {ι : Type*} (s : Finset ι) {x : ι → smD ε (rreg ε)} {Φ : ι → Matrix (Fin n) (Fin n) ℂ → E}
    (h : ∀ i ∈ s, IcxGood ε φ (x i) (Φ i)) : IcxGood ε φ (∑ i ∈ s, x i) (fun g => ∑ i ∈ s, Φ i g) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact icxGood_congr (icxGood_zero (ε := ε) (φ := φ)) (by simp) (fun g _ => by simp)
  · intro i s hi ih h
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact icxGood_congr (icxGood_add_smul h1 h2 1) (by rw [Finset.sum_insert hi, one_smul])
      (fun g _ => by simp [Finset.sum_insert hi])

theorem icxGood_ePow (A : Fin n → Fin n → Module.End ℂ (smD ε (rreg ε)))
    (B : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hAB : ∀ a b y Ψ', IcxGood ε φ y Ψ' → IcxGood ε φ (A a b y) (B a b Ψ'))
    {x : smD ε (rreg ε)} {Φ : Matrix (Fin n) (Fin n) ℂ → E} (hx : IcxGood ε φ x Φ) :
    ∀ k a b, IcxGood ε φ (ePow A k a b x) (S7.opPow B k a b Φ)
  | 0, a, b => by
      by_cases h : a = b
      · subst h
        simpa [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, S7.opPow] using hx
      · exact icxGood_congr icxGood_zero (by simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, h]) fun g _ => by simp [S7.opPow, h]
  | k + 1, a, b => by
      have := icxGood_sum Finset.univ fun c _ => hAB a c _ _ (icxGood_ePow A B hAB hx k c b)
      exact icxGood_congr this (by simp [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply]) fun g _ => by
        simp [S7.opPow, Finset.sum_apply]

theorem icxGood_gelfand (A : Fin n → Fin n → Module.End ℂ (smD ε (rreg ε)))
    (B : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hAB : ∀ a b y Ψ', IcxGood ε φ y Ψ' → IcxGood ε φ (A a b y) (B a b Ψ'))
    {x : smD ε (rreg ε)} {Φ : Matrix (Fin n) (Fin n) ℂ → E} (hx : IcxGood ε φ x Φ) (k : ℕ) :
    IcxGood ε φ (gelfand A k x) (S7.opGelfand B k Φ) := by
  have h := icxGood_sum (φ := φ) Finset.univ (x := fun a => ePow A k a a x)
    (Φ := fun a => S7.opPow B k a a Φ) (fun a _ => icxGood_ePow A B hAB hx k a a)
  exact icxGood_congr h (by simp [gelfand, LinearMap.sum_apply])
    (fun g _ => by simp [S7.opGelfand, Finset.sum_apply])

theorem icxGood_anti {y : smD ε (rreg ε)} {Φ : Matrix (Fin n) (Fin n) ℂ → E} (h : IcxGood ε φ y Φ) (a b : Fin n) :
    IcxGood ε φ (antiE (smE ε (rreg ε)) a b y) (S7.rightEanti ε a b Φ) := by
  have h1 := icxGood_neg (icxGood_eab h (Fin.rev b) (Fin.rev a))
  exact icxGood_congr h1 (by simp [antiE]) (fun g _ => by simp [S7.rightEanti])

theorem icxGood_list {ι : Type*} (A : ι → Module.End ℂ (smD ε (rreg ε)))
    (B : ι → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hAB : ∀ i y Ψ', IcxGood ε φ y Ψ' → IcxGood ε φ (A i y) (B i Ψ')) :
    ∀ (L : List ι) (x : smD ε (rreg ε)) (Φ : Matrix (Fin n) (Fin n) ℂ → E), IcxGood ε φ x Φ →
      IcxGood ε φ ((L.map A).prod x) ((L.map B).foldr (fun T h => T h) Φ)
  | [], x, Φ, hx => by simpa using hx
  | i :: L, x, Φ, hx => by
      simp only [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
      exact hAB i _ _ (icxGood_list A B hAB L x Φ hx)

private theorem S7_EabV_eq_REAL_EabV (a b : Fin n) (Ψ : Matrix (Fin n) (Fin n) ℂ → E) :
    S7.EabV ε a b Ψ = Formalism.REAL.EabV ε a b Ψ := rfl

theorem icxGood_tm {x : smD ε (rreg ε)} {Φ : Matrix (Fin n) (Fin n) ℂ → E} (hx : IcxGood ε φ x Φ)
    (u u' : ℂ) (hu : u = u') (a b : Fin n) :
    IcxGood ε φ (Formalism.REAL.Tm (smE ε (rreg ε)) u a b x) (Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV ε) u' a b Φ) := by
  subst hu
  by_cases hab : a = b
  · subst hab
    have h1 := icxGood_add_smul (icxGood_add_smul (icxGood_zero (ε := ε) (φ := φ)) hx u)
      (icxGood_eab hx a a) 1
    refine icxGood_congr h1 ?_ (fun g _ => ?_)
    · simp [Formalism.REAL.Tm]
    · simp only [Formalism.QuantumDeterminants.Top, eq_self_iff_true, if_true, zero_add, one_smul, S7_EabV_eq_REAL_EabV]
  · refine icxGood_congr (icxGood_eab hx a b) ?_ (fun g _ => ?_)
    · simp [Formalism.REAL.Tm, hab]
    · simp only [Formalism.QuantumDeterminants.Top, if_neg hab, zero_add, S7_EabV_eq_REAL_EabV]

theorem icxGood_qdet {x : smD ε (rreg ε)} {Φ : Matrix (Fin n) (Fin n) ℂ → E} (hx : IcxGood ε φ x Φ) (u : ℂ) :
    IcxGood ε φ (Formalism.REAL.qdet (smE ε (rreg ε)) u x) (Formalism.QuantumDeterminants.qdetOp (Formalism.REAL.EabV ε) u Φ) := by
  have key : ∀ σ : Equiv.Perm (Fin n), IcxGood ε φ
      ((List.ofFn fun k : Fin n => Formalism.REAL.Tm (smE ε (rreg ε)) (u - (k : ℂ)) (σ k) k).prod x)
      ((List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (Formalism.REAL.EabV ε) (u - ((k : ℕ) : ℂ)) (σ k) k).foldr
        (fun T h => T h) Φ) := by
    intro σ
    rw [List.ofFn_eq_map, List.ofFn_eq_map]
    exact icxGood_list _ _ (fun k y Ψ' hy => icxGood_tm hy _ _ rfl (σ k) k) (List.finRange n) x Φ hx
  have hs := icxGood_sum (φ := φ) (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun σ _ => icxGood_add_smul (icxGood_zero (ε := ε) (φ := φ)) (key σ)
      (((Equiv.Perm.sign σ : ℤ) : ℂ)))
  refine icxGood_congr hs ?_ (fun g _ => ?_)
  · simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, id_eq, zero_add, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  · simp [Formalism.QuantumDeterminants.qdetOp, Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply]

private theorem toL2_const_mul (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (c : ℂ) :
    toL2 ε (fun g => c * F g) = c • toL2 ε F := by
  by_cases hm : MemLp (fun y : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat y)) 2 (Formalism.REAL.muG ε)
  · have hm' : MemLp (fun y : Formalism.REAL.UJ ε => c * F (Formalism.MainNotions.S.umat y)) 2 (Formalism.REAL.muG ε) :=
      hm.const_mul c
    simp only [toL2, dif_pos hm, dif_pos hm']
    rw [← MemLp.toLp_const_smul c hm]
    rfl
  · by_cases hc : c = 0
    · subst hc
      simp only [zero_mul, zero_smul]
      exact toL2_zero'
    · have hm' : ¬ MemLp (fun y : Formalism.REAL.UJ ε => c * F (Formalism.MainNotions.S.umat y)) 2 (Formalism.REAL.muG ε) := by
        intro h
        apply hm
        have := h.const_mul c⁻¹
        simpa [hc] using this
      simp only [toL2, dif_neg hm, dif_neg hm', smul_zero]

theorem icx_val {x y : smD ε (rreg ε)} {Φ Φ₀ : Matrix (Fin n) (Fin n) ℂ → E} (hy : IcxGood ε φ y Φ)
    (hx : (x : L2 ε) = toL2 ε (fun g => φ (Φ₀ g))) (c : ℂ) (hΦ : ∀ g, inUJ ε g → Φ g = c • Φ₀ g) :
    y = c • x := by
  obtain ⟨_, _, h3⟩ := hy
  apply Subtype.ext
  rw [Submodule.coe_smul, h3, hx,
    toL2_congr_of_inUJ_eq (F := fun g => φ (Φ g)) (G := fun g => c * φ (Φ₀ g)) (fun g hg => by simp [hΦ g hg])]
  exact toL2_const_mul (fun g => φ (Φ₀ g)) c

end Good

section Central

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem icx_genSub_eigen (A : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) (Op : Module.End ℂ M) (c : ℂ)
    (hcomm : ∀ a b, Op * A a b = A a b * Op) (hS : ∀ x ∈ S, Op x = c • x) :
    ∀ x ∈ genSub A S, Op x = c • x := by
  intro x hx
  let T : Submodule ℂ M :=
    { carrier := {x | Op x = c • x}
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        rw [map_add, hu, hv, smul_add]
      zero_mem' := by simp
      smul_mem' := by
        intro r u hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        rw [map_smul, hu, smul_comm] }
  have hT : S ≤ T ∧ ∀ a b, ∀ v ∈ T, A a b v ∈ T := by
    refine ⟨fun v hv => hS v hv, fun a b v hv => ?_⟩
    have hv' : Op v = c • v := hv
    have h1 := LinearMap.congr_fun (hcomm a b) v
    show Op (A a b v) = c • A a b v
    calc Op (A a b v) = (Op * A a b) v := rfl
      _ = (A a b * Op) v := h1
      _ = A a b (Op v) := rfl
      _ = c • A a b v := by rw [hv', map_smul]
  have hx' : x ∈ sInf {T : Submodule ℂ M | S ≤ T ∧ ∀ a b, ∀ v ∈ T, A a b v ∈ T} := hx
  exact sInf_le (show T ∈ {T : Submodule ℂ M | S ≤ T ∧ ∀ a b, ∀ v ∈ T, A a b v ∈ T} from hT) hx'

private theorem isGlRep_antiE {A : Fin n → Fin n → Module.End ℂ M} (hA : IsGlRep A) :
    IsGlRep (antiE A) := by
  intro a b c d
  have h := hA (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c)
  simp only [antiE]
  rw [neg_mul_neg, neg_mul_neg, h]
  have e1 : (Fin.rev a = Fin.rev d) = (d = a) := by rw [Fin.rev_inj]; exact propext eq_comm
  have e2 : (Fin.rev c = Fin.rev b) = (b = c) := by rw [Fin.rev_inj]; exact propext eq_comm
  simp only [e1, e2]
  split_ifs <;> abel

theorem icx_anti_comm {A : Fin n → Fin n → Module.End ℂ M} (hA : IsGlRep A) (k : ℕ) (a b : Fin n) :
    gelfand (antiE A) k * A a b = A a b * gelfand (antiE A) k := by
  have hG := isGlRep_antiE hA
  have h := gelfand_comm hG k (Fin.rev b) (Fin.rev a)
  have e : antiE A (Fin.rev b) (Fin.rev a) = -A a b := by simp [antiE]
  rw [e, neg_mul, mul_neg, neg_inj] at h
  exact h.symm

end Central

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem icx_good_datum (hP : IsPsiFor ε lam T Ψ) {y : smD ε (rreg ε)} {v : T.V}
    (hv : (y : L2 ε) = uniformisationL2 ε Ψ v₀ v) : IcxGood ε (pdA_coef v₀ v) y Ψ :=
  ⟨hP.2.2.1, datumFunction_isSmoothL2 hP v₀ v, hv⟩

theorem capelli_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)
    (Y : ℂ) (x : smD ε (rreg ε)) (hx : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :
    Formalism.REAL.qdet (smE ε (rreg ε)) (Y + ((n : ℂ) - 1) / 2) x =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • x := by
  have hE : IsGlRep (smE ε (rreg ε)) := (isDerivedOn_smE (rreg_isURepOn ε)).glRep
  refine icx_genSub_eigen (smE ε (rreg ε)) (datumV ε Ψ v₀) (Formalism.REAL.qdet (smE ε (rreg ε)) (Y + ((n : ℂ) - 1) / 2))
    (Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y)
    (fun a b => Formalism.REAL.qDetCentral (Module.End ℂ (smD ε (rreg ε))) n (smE ε (rreg ε)) hE _ a b) ?_ x hx
  intro y hy
  obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ y).1 hy
  exact icx_val (icxGood_qdet (icx_good_datum hP hv) _) hv _ fun g hg => hcap Y g hg

theorem hasGelfandChar_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hG : ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      S7.opGelfand (S7.rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        S7.opGelfand (S7.rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) :
    HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  have hE : IsGlRep (smE ε (rreg ε)) := (isDerivedOn_smE (rreg_isURepOn ε)).glRep
  intro k x hx
  have hdat : ∀ y ∈ datumV ε Ψ v₀, gelfand (smE ε (rreg ε)) k y = gval (icShift lam) k • y ∧
      gelfand (antiE (smE ε (rreg ε))) k y = gval (icShift (-lam)) k • y := by
    intro y hy
    obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ y).1 hy
    have hg := icx_good_datum hP hv
    exact ⟨icx_val (icxGood_gelfand (smE ε (rreg ε)) (S7.rightE ε) (fun a b _ _ h => icxGood_eab h a b) hg k)
        hv _ fun g hg' => (hG k g hg').1,
      icx_val (icxGood_gelfand (antiE (smE ε (rreg ε))) (S7.rightEanti ε) (fun a b _ _ h => icxGood_anti h a b) hg k)
        hv _ fun g hg' => (hG k g hg').2⟩
  exact ⟨icx_genSub_eigen _ _ _ _ (fun a b => (gelfand_comm hE k a b).symm) (fun y hy => (hdat y hy).1) x hx,
    icx_genSub_eigen _ _ _ _ (fun a b => icx_anti_comm hE k a b) (fun y hy => (hdat y hy).2) x hx⟩

end ReciprocityTheory.ChartRestriction.DS
