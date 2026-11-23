import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem cpt_box (R : ℝ) : IsCompact {A : Matrix (Fin N) (Fin N) ℂ | ∀ i j, ‖A i j‖ ≤ R} := by
  have : {A : Matrix (Fin N) (Fin N) ℂ | ∀ i j, ‖A i j‖ ≤ R} =
      Set.univ.pi (fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R) := by
    ext A
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem cpt_SL (R : ℝ) :
    IsCompact {A : SpecialLinearGroup (Fin N) ℂ | ∀ i j, ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R} :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage (cpt_box R)

theorem cpt_Z [Fintype ι] (R : ℝ) : IsCompact (Zb (ι := ι) (N := N) R) := by
  have : Zb (ι := ι) (N := N) R = Set.univ.pi (fun _ =>
      {A : SpecialLinearGroup (Fin N) ℂ | ∀ i j, ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ R}) := by
    ext z; simp [Zb]
  rw [this]
  exact isCompact_univ_pi fun _ => cpt_SL R

theorem cont_val : Continuous fun A : SpecialLinearGroup (Fin N) ℂ => (A : Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous

theorem cpt_U : IsCompact {A : SpecialLinearGroup (Fin N) ℂ |
    (A : Matrix (Fin N) (Fin N) ℂ) ∈ unitaryGroup (Fin N) ℂ} := by
  refine (cpt_SL (N := N) 1).of_isClosed_subset ?_ ?_
  · have : {A : SpecialLinearGroup (Fin N) ℂ | (A : Matrix (Fin N) (Fin N) ℂ) ∈ unitaryGroup (Fin N) ℂ} =
        {A : SpecialLinearGroup (Fin N) ℂ | (A : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ)ᴴ = 1} := by
      ext A; simp [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rw [this]
    exact isClosed_eq (cont_val.matrix_mul cont_val.matrix_conjTranspose)
      continuous_const
  · intro A hA i j
    exact entry_norm_bound_of_unitary hA i j

theorem cpt_KS : IsCompact (KS (ι := ι) (N := N)) := by
  have : KS (ι := ι) (N := N) = Set.univ.pi (fun _ =>
      {A : SpecialLinearGroup (Fin N) ℂ | (A : Matrix (Fin N) (Fin N) ℂ) ∈ unitaryGroup (Fin N) ℂ}) := by
    ext z; simp [KS]
  rw [this]
  exact isCompact_univ_pi fun _ => cpt_U

theorem cont_mt (w : ι) (i j : Fin N) : Continuous fun p : G ι N => mt p w i j :=
  (continuous_apply j).comp ((continuous_apply i).comp (cont_val.comp (continuous_apply w)))

theorem cpt_Om [Fintype ι] (M : ℝ) : IsCompact (OmG (ι := ι) (N := N) M) := by
  refine (cpt_Z (ι := ι) (N := N) M).of_isClosed_subset ?_ ?_
  · have : OmG (ι := ι) (N := N) M =
        {p : G ι N | ∀ w i j, j < i → mt p w i j = 0} ∩ {p | ∀ w i j, ‖mt p w i j‖ ≤ M} ∩
          {p | ∀ w i, M⁻¹ ≤ ‖mt p w i i‖} ∩ {p | ∀ i, ∏ w, ‖mt p w i i‖ = 1} := by
      ext p
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨fun w i j hij => h1 w hij, h2⟩, h3⟩, h4⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨fun w i j hij => h1 w i j hij, h2, h3, h4⟩
    rw [this]
    simp only [Set.setOf_forall]
    refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
    · exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (cont_mt w i j) continuous_const
    · exact isClosed_iInter fun w => isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (cont_mt w i j).norm continuous_const
    · exact isClosed_iInter fun w => isClosed_iInter fun i =>
        isClosed_le continuous_const (cont_mt w i i).norm
    · exact isClosed_iInter fun i =>
        isClosed_eq (continuous_finset_prod _ fun w _ => (cont_mt w i i).norm) continuous_const
  · intro p hp
    exact hp.2.1

theorem cont_dg : Continuous fun s : {s : Fin N → ℝ // ∑ i, s i = 0} => (dg s.1 s.2 : G ι N) := by
  refine continuous_pi fun w => Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
  exact Continuous.matrix_diagonal (continuous_pi fun i =>
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp ((continuous_apply i).comp continuous_subtype_val)))

theorem cpt_S (T : ℝ) (m : Fin N → ℤ) : IsCompact
    {s : {s : Fin N → ℝ // ∑ i, s i = 0} | Cone T s.1 ∧ ∀ i, (m i : ℝ) ≤ s.1 i ∧ s.1 i ≤ m i + 1} := by
  have hemb : Topology.IsClosedEmbedding (Subtype.val : {s : Fin N → ℝ // ∑ i, s i = 0} → (Fin N → ℝ)) :=
    (isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const).isClosedEmbedding_subtypeVal
  have hbox : IsCompact {s : Fin N → ℝ | Cone T s ∧ ∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1} := by
    refine (isCompact_univ_pi fun i => isCompact_Icc (a := (m i : ℝ)) (b := m i + 1)).of_isClosed_subset ?_ ?_
    · have hc1 : IsClosed {s : Fin N → ℝ | Cone T s} := by
        have : {s : Fin N → ℝ | Cone T s} = ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : (j : ℕ) = i + 1),
            {s : Fin N → ℝ | s j ≤ s i + T} := by
          ext s; simp [Cone]
        rw [this]
        exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_le (continuous_apply j) ((continuous_apply i).add continuous_const)
      have hc2 : IsClosed {s : Fin N → ℝ | ∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1} := by
        have : {s : Fin N → ℝ | ∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1} = ⋂ i : Fin N,
            ({s : Fin N → ℝ | (m i : ℝ) ≤ s i} ∩ {s | s i ≤ m i + 1}) := by
          ext s; simp
        rw [this]
        exact isClosed_iInter fun i => (isClosed_le continuous_const (continuous_apply i)).inter
          (isClosed_le (continuous_apply i) continuous_const)
      exact hc1.inter hc2
    · intro s hs
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
      exact hs.2
  exact hemb.isCompact_preimage hbox

theorem cpt_X {P : Set (G ι N)} (hP : IsCompact P) (T : ℝ) (m : Fin N → ℤ) : IsCompact (Xb P T m) := by
  have himg : Xb P T m = (fun x : G ι N × {s : Fin N → ℝ // ∑ i, s i = 0} × G ι N =>
      x.1 * dg x.2.1.1 x.2.1.2 * x.2.2) ''
      (P ×ˢ {s : {s : Fin N → ℝ // ∑ i, s i = 0} | Cone T s.1 ∧ ∀ i, (m i : ℝ) ≤ s.1 i ∧ s.1 i ≤ m i + 1} ×ˢ
        KS) := by
    ext x
    constructor
    · rintro ⟨p, hp, s, hs, hc, hb, k, hk, rfl⟩
      exact ⟨(p, ⟨s, hs⟩, k), ⟨hp, ⟨hc, hb⟩, hk⟩, rfl⟩
    · rintro ⟨⟨p, ⟨s, hs⟩, k⟩, ⟨hp, ⟨hc, hb⟩, hk⟩, rfl⟩
      exact ⟨p, hp, s, hs, hc, hb, k, hk, rfl⟩
  rw [himg]
  refine (hP.prod ((cpt_S T m).prod cpt_KS)).image ?_
  exact (continuous_fst.mul (cont_dg.comp (continuous_fst.comp continuous_snd))).mul
    (continuous_snd.comp continuous_snd)

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
