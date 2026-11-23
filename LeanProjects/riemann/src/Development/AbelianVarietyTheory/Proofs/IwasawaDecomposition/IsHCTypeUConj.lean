import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered

noncomputable section

open Matrix Formalism.MainNotions.S

namespace GlobalTheory.CoefSpace.Conj

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem ujset_eq (k : ℕ) : UJset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  GlobalTheory.RealPar.ujset_const true

theorem kset_eq (k : ℕ) : Formalism.REAL.Kset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  (GlobalTheory.DefiniteCheck.kset_const k true).trans (ujset_eq k)

theorem conj_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g.map star ∈ Matrix.unitaryGroup (Fin k) ℂ :=
  Matrix.transpose_mem_unitaryGroup_iff.2 (Unitary.star_mem hg)

def tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_conj (θ : Fin k → ℝ) : (tor θ).map star = tor (-θ) := by
  rw [tor, Matrix.diagonal_map (star_zero ℂ)]
  congr 1
  funext a
  simp [← Complex.exp_conj]

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, tor, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp [← Complex.exp_conj, ← Complex.exp_add]

theorem wt_iff (μ : Fin k → ℝ) (v : H) : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v ↔
    ∀ θ, π (tor θ) v = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v :=
  ⟨fun h θ => h θ (by rw [kset_eq]; exact tor_mem θ), fun h θ _ => h θ⟩

theorem wt_conj {μ : Fin k → ℝ} {v : H} :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => π (g.map star)) μ v ↔ IsWtOn (Formalism.REAL.Kset (allPos k)) π (-μ) v := by
  simp only [wt_iff, tor_conj]
  refine ⟨fun h θ => ?_, fun h θ => ?_⟩
  · simpa using h (-θ)
  · simpa using h (-θ)

def revM (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := (1 : Matrix (Fin k) (Fin k) ℂ).submatrix Fin.revPerm id

theorem revM_mem : revM k ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, revM, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_one, Matrix.submatrix_mul_equiv, Matrix.mul_one, Matrix.submatrix_id_id]

theorem tor_revM (θ : Fin k → ℝ) : tor θ * revM k = revM k * tor fun a => θ (Fin.rev a) := by
  ext a b
  simp only [tor, revM, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, Fin.revPerm_apply, id,
    Matrix.one_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem wt_rev (hπ : IsURepOn (UJset (allPos k)) π) {μ : Fin k → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v) :
    π (revM k) v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset (allPos k)) π (fun a => μ (Fin.rev a)) (π (revM k) v) := by
  rw [ujset_eq] at hπ
  refine ⟨fun h => hv0 ?_, (wt_iff _ _).2 fun θ => ?_⟩
  · rw [← norm_eq_zero, ← hπ.2.1 _ revM_mem v, h, norm_zero]
  · have e : ∑ a, μ a * θ (Fin.rev a) = ∑ a, μ (Fin.rev a) * θ a := by
      rw [← Equiv.sum_comp Fin.revPerm]
      simp
    rw [← ContinuousLinearMap.comp_apply, ← hπ.1.2 _ (tor_mem θ) _ revM_mem, tor_revM,
      hπ.1.2 _ revM_mem _ (tor_mem _), ContinuousLinearMap.comp_apply, (wt_iff _ _).1 hv, map_smul, e]

theorem cdom_neg_rev {μ Λ : Fin k → ℝ} (h : CDom (allPos k) μ Λ) :
    CDom (allPos k) (fun a => -μ (Fin.rev a)) fun a => -Λ (Fin.rev a) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b h => ⟨Fin.rev_lt_rev.1 (hc _ _ h).1, rfl⟩, ?_⟩
  funext x
  have h1 := congrFun e (Fin.rev x)
  rw [← Equiv.sum_comp Fin.revPerm] at h1
  simp only [← Equiv.sum_comp Fin.revPerm (fun b => (c _ b : ℝ) • Formalism.REAL.root _ b)] at h1
  rw [Finset.sum_comm] at h1
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.single_apply, Fin.revPerm_apply,
    Fin.rev_inj, smul_eq_mul] at h1 ⊢
  rw [show -Λ x.rev - -μ x.rev = -(Λ x.rev - μ x.rev) by ring, h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem isHCTypeU_conj {u : Fin k → ℝ} (h : IsHCTypeU k u π) :
    IsHCTypeU k (fun i => -u (Fin.rev i)) (fun g => π (g.map star)) := by
  obtain ⟨h1, h2, h3, h4, -, h5, ⟨v, -, hv0, hv⟩, h6⟩ := h
  have hl : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) =
      fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const, GlobalTheory.DefiniteCheck.lowK_const, Fin.val_rev, Nat.cast_sub a.2]
    push_cast
    ring
  have h3' := h3
  rw [ujset_eq] at h3'
  refine ⟨h1, h2, ?_, h4, fun _ _ _ _ => trivial, fun S hS hst => h5 S hS fun g hg x hx => ?_,
    ⟨_, trivial, (wt_rev h3 hv0 hv).1, ?_⟩, fun μ x _ hx0 hx => ?_⟩
  · rw [ujset_eq]
    refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg => h3'.2.1 _ (conj_mem hg), fun x => ?_⟩
    · beta_reduce
      rw [Matrix.map_one _ (star_zero ℂ) (star_one ℂ)]
      exact h3'.1.1
    · have : (a * b).map star = a.map star * b.map star := Matrix.map_mul (f := starRingEnd ℂ)
      beta_reduce
      rw [this]
      exact h3'.1.2 _ (conj_mem ha) _ (conj_mem hb)
    · exact (h3'.2.2 x).comp (continuous_id.matrix_map continuous_star).continuousOn fun g hg => conj_mem hg
  · rw [kset_eq] at hg
    have := hst (g.map star) (by rw [kset_eq]; exact conj_mem hg) x hx
    have e : (g.map star).map star = g := by
      ext a b
      simp
    simpa only [e] using this
  · rw [hl, wt_conj]
    convert (wt_rev h3 hv0 hv).2 using 1
    funext a
    simp
  · obtain ⟨a1, a2⟩ := wt_rev h3 hx0 (wt_conj.1 hx)
    rw [hl]
    convert cdom_neg_rev (h6 _ _ trivial a1 a2) using 1
    funext a
    simp

end GlobalTheory.CoefSpace.Conj
