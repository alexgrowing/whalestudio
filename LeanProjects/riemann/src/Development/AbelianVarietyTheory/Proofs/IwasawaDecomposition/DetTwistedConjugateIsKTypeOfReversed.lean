import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConjTwist

variable {k : ℕ}

theorem Jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mem_U_iff (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  show gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) ↔ _
  rw [Jm_allPos, Matrix.mul_one]

theorem mem_K_iff (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  rw [mem_U_iff]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔ _
  rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem map_star_mul (g h : Matrix (Fin k) (Fin k) ℂ) :
    (g * h).map star = g.map star * h.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_star_one : (1 : Matrix (Fin k) (Fin k) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem map_star_star (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).map star = g := by
  ext a b
  simp

theorem map_star_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g.map star ∈ UJset (allPos k) := by
  rw [mem_U_iff] at hg ⊢
  have h : (g.map star)ᴴ = gᴴ.map star := by
    ext a b
    simp
  rw [h, ← map_star_mul, hg, map_star_one]

theorem norm_det {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : ‖g.det‖ = 1 := by
  rw [mem_U_iff] at hg
  have h := congrArg (fun M => ‖Matrix.det M‖) hg
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one,
    norm_one] at h
  nlinarith [norm_nonneg g.det]

theorem det_ne_zero {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : g.det ≠ 0 := by
  intro h
  have := norm_det hg
  rw [h, norm_zero] at this
  exact zero_ne_one this

abbrev tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_map_star (θ : Fin k → ℝ) : (tor θ).map star = tor (fun a => -θ a) := by
  rw [tor, Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  show (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  simp

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ UJset (allPos k) := by
  rw [mem_U_iff, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  show (starRingEnd ℂ) _ * _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem tor_det_zpow (θ : Fin k → ℝ) (x : ℤ) :
    (tor θ).det ^ x = Complex.exp (((∑ a, (x : ℝ) * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

def revMat (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun a b => if Fin.rev a = b then 1 else 0

theorem revMat_mul_self : revMat k * revMat k = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
  · simp [revMat, Matrix.one_apply]
  · intro c _ hc
    simp [revMat, hc.symm]
  · simp

theorem revMat_conjTranspose : (revMat k)ᴴ = revMat k := by
  ext a b
  simp only [revMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · have h' : ¬ Fin.rev b = a := fun h' => h (by rw [← h', Fin.rev_rev])
    simp [h, h']

theorem revMat_mem : revMat k ∈ UJset (allPos k) := by
  rw [mem_U_iff, revMat_conjTranspose, revMat_mul_self]

theorem tor_mul_revMat (θ : Fin k → ℝ) :
    tor θ * revMat k = revMat k * tor (fun a => θ (Fin.rev a)) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, revMat, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · simp [h]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem isWtOn_rev (hσ : IsURepOn (UJset (allPos k)) σ) {μ : Fin k → ℝ} {v : H}
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) σ μ v) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => μ (Fin.rev a)) (σ (revMat k) v) := by
  intro θ _
  have h1 : σ (tor θ) (σ (revMat k) v) = σ (revMat k) (σ (tor fun a => θ (Fin.rev a)) v) := by
    have h2 := hσ.1.2 _ (tor_mem θ) _ revMat_mem
    have h3 := hσ.1.2 _ revMat_mem _ (tor_mem fun a => θ (Fin.rev a))
    rw [tor_mul_revMat, h3] at h2
    exact (congrArg (fun f : H →L[ℂ] H => f v) h2).symm
  refine h1.trans ?_
  rw [hv _ ((mem_K_iff _).2 (tor_mem _)), map_smul]
  congr 4
  rw [← Equiv.sum_comp Fin.revPerm]
  simp

theorem rev_ne_zero (hσ : IsURepOn (UJset (allPos k)) σ) {v : H} (hv : v ≠ 0) :
    σ (revMat k) v ≠ 0 := by
  rw [← norm_ne_zero_iff, hσ.2.1 _ revMat_mem, norm_ne_zero_iff]
  exact hv

theorem exp_split (x : ℤ) (μ θ : Fin k → ℝ) :
    Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) =
      (tor θ).det ^ x * Complex.exp (((∑ a, ((x : ℝ) - μ a) * -θ a : ℝ) : ℂ) * Complex.I) := by
  rw [tor_det_zpow, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  exact Finset.sum_congr rfl fun a _ => by ring

theorem isWtOn_twist_iff (x : ℤ) (μ : Fin k → ℝ) (v : H) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) μ v ↔
      IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => (x : ℝ) - μ a) v := by
  constructor
  · intro h θ _
    have h1 : (tor fun a => -θ a).det ^ x • σ ((tor fun a => -θ a).map star) v = _ :=
      h (fun a => -θ a) ((mem_K_iff _).2 (tor_mem _))
    rw [exp_split x, ← smul_smul, tor_map_star] at h1
    simp only [neg_neg] at h1
    exact smul_right_injective H (zpow_ne_zero x (det_ne_zero (tor_mem _))) h1
  · intro h θ _
    show (tor θ).det ^ x • σ ((tor θ).map star) v = _
    rw [exp_split x, ← smul_smul, tor_map_star, h _ ((mem_K_iff _).2 (tor_mem _))]

theorem stable_twist_iff (x : ℤ) (S : Submodule ℂ H) :
    IsKStableOn (allPos k) (fun g => g.det ^ x • σ (g.map star)) S ↔ IsKStableOn (allPos k) σ S := by
  constructor
  · intro h g hg v hv
    have hg' := map_star_mem ((mem_K_iff g).1 hg)
    have h1 : (g.map star).det ^ x • σ ((g.map star).map star) v ∈ S :=
      h _ ((mem_K_iff _).2 hg') v hv
    rw [map_star_star] at h1
    exact (S.smul_mem_iff (zpow_ne_zero x (det_ne_zero hg'))).1 h1
  · intro h g hg v hv
    exact S.smul_mem _ (h _ ((mem_K_iff _).2 (map_star_mem ((mem_K_iff g).1 hg))) v hv)

theorem isURepOn_twist (hσ : IsURepOn (UJset (allPos k)) σ) (x : ℤ) :
    IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · simp only [Matrix.det_one, _root_.one_zpow, one_smul, map_star_one, hσ.1.1]
  · simp only [Matrix.det_mul, mul_zpow, map_star_mul]
    rw [hσ.1.2 _ (map_star_mem ha) _ (map_star_mem hb)]
    ext v
    simp [smul_smul, mul_comm]
  · simp only [ContinuousLinearMap.smul_apply, norm_smul, norm_zpow, norm_det hg, _root_.one_zpow,
      one_mul, hσ.2.1 _ (map_star_mem hg)]
  · simp only [ContinuousLinearMap.smul_apply]
    refine ContinuousOn.smul ?_ ?_
    · exact (continuous_id.matrix_det.continuousOn).zpow₀ x fun g hg => Or.inl (det_ne_zero hg)
    · exact (hσ.2.2 v).comp (continuous_id.matrix_map continuous_star).continuousOn
        fun g hg => map_star_mem hg

theorem cdom_rev (x : ℤ) (Λ μ : Fin k → ℝ)
    (h : CDom (allPos k) (fun a => (x : ℝ) - μ (Fin.rev a)) Λ) :
    CDom (allPos k) μ (fun a => (x : ℝ) - Λ (Fin.rev a)) := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b hab => ⟨?_, rfl⟩, ?_⟩
  · exact Fin.rev_lt_rev.1 (hc _ _ hab).1
  · funext i
    have h1 := congrFun he (Fin.rev i)
    simp only [Pi.sub_apply, Fin.rev_rev, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    have h2 : ∑ a, ∑ b, (c (Fin.rev b) (Fin.rev a) : ℝ) * Formalism.REAL.root a b i =
        -∑ a, ∑ b, (c a b : ℝ) * Formalism.REAL.root a b (Fin.rev i) := by
      rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply,
        Fin.rev_eq_iff]
      ring
    rw [h2, ← h1]
    ring

theorem conj_twist_isKTypeOf : ∀ (k : ℕ) (Λ : Fin k → ℝ) (x : ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) ∧ IsKTypeOf (allPos k) (fun g => g.det ^ x • σ (g.map star)) (fun a => (x : ℝ) - Λ (Fin.rev a)) ⊤ := by
  intro k Λ x H _ _ _ σ hσ hK
  obtain ⟨hfd, -, hirr, ⟨v, -, hv0, hv⟩, hdom⟩ := hK
  refine ⟨isURepOn_twist hσ x, hfd, fun _ _ _ _ => trivial,
    fun S hS hst => hirr S hS ((stable_twist_iff x S).1 hst),
    ⟨σ (revMat k) v, trivial, rev_ne_zero hσ hv0, ?_⟩, fun μ w _ hw0 hw => ?_⟩
  · rw [isWtOn_twist_iff]
    simpa only [sub_sub_cancel] using isWtOn_rev hσ hv
  · rw [isWtOn_twist_iff] at hw
    exact cdom_rev x Λ μ (hdom _ _ trivial (rev_ne_zero hσ hw0) (isWtOn_rev hσ hw))

end GlobalTheory.ConjTwist
