import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isSmoothVec_add {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (u + v) := by
  obtain ⟨F, hF, hF'⟩ := hu
  obtain ⟨K, hK, hK'⟩ := hv
  exact ⟨fun z => F z + K z, hF.add hK, fun z hz => by rw [map_add, hF' z hz, hK' z hz]⟩

theorem isSmoothVec_smul (c : ℂ) {v : H} (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (c • v) := by
  obtain ⟨F, hF, hF'⟩ := hv
  exact ⟨fun z => c • F z, hF.const_smul c, fun z hz => by rw [map_smul, hF' z hz]⟩

theorem isSmoothVec_zero : IsSmoothVec G π (0 : H) :=
  ⟨fun _ => 0, contDiff_const, fun z _ => map_zero _⟩

theorem isSmoothVec_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → H)
    (hf : ∀ i, IsSmoothVec G π (f i)) : IsSmoothVec G π (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSmoothVec_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSmoothVec_add (isSmoothVec_smul _ (hf a)) ih

variable {d : ℕ} {b : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem word_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {w : H} (hw : IsSmoothVec G π w) :
    IsSmoothVec G π (p.foldr (fun i w => dRep π (b i) w) w) := by
  induction p with
  | nil => exact hw
  | cons i p ih => exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih (hb i)).2

theorem list_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) {v : H}
    (hv : IsSmoothVec G π v) : IsSmoothVec G π (l.foldr (dRep π) v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep
      (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) (hl X List.mem_cons_self)).2

theorem word_add (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {u v : H} (hu : IsSmoothVec G π u)
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (u + v) =
      p.foldr (fun i w => dRep π (b i) w) u + p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hu)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.1

theorem word_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) (c : ℂ) {v : H}
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (c • v) =
      c • p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hv)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.2 c

theorem word_sum (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → H) (hf : ∀ i, IsSmoothVec G π (f i)) :
    p.foldr (fun i w => dRep π (b i) w) (∑ j ∈ s, c j • f j) =
      ∑ j ∈ s, c j • p.foldr (fun i w => dRep π (b i) w) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := word_smul hG hrep hb p (0 : ℂ) (isSmoothVec_zero (G := G) (π := π) (H := H))
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      word_add hG hrep hb p (isSmoothVec_smul _ (hf a)) (isSmoothVec_sum s c f hf),
      word_smul hG hrep hb p _ (hf a), ih]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem prod_mnorm_nonneg (l : List (Matrix (Fin n) (Fin n) ℂ)) : 0 ≤ (l.map mnorm).prod := by
  induction l with
  | nil => simp
  | cons X l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (mnorm_nonneg X) ih

theorem mixed_bound (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) (p : List (Fin d)) :
    ‖p.foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
      C ^ (p.length + l.length + 1) * (p.length + l.length).factorial * D ^ l.length *
        (l.map mnorm).prod := by
  induction l generalizing p with
  | nil => simpa using hbound p
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ HCSS.lieOf G := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hX : X ∈ HCSS.lieOf G := hl X List.mem_cons_self
    have hw : IsSmoothVec G π (l.foldr (dRep π) v) := list_smooth hG hrep l hl' hv
    obtain ⟨r, hr⟩ := hsp X hX
    have e1 : dRep π X (l.foldr (dRep π) v) =
        ∑ i, (r i : ℂ) • dRep π (b i) (l.foldr (dRep π) v) := by
      rw [hr]
      exact hexp r _ hw
    have hsm : ∀ i, IsSmoothVec G π (dRep π (b i) (l.foldr (dRep π) v)) := fun i =>
      (hasDerivAt_dRep_and_isSmoothVec hG hrep hw (hb i)).2
    have e2 : p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v)) =
        ∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v) := by
      rw [e1, word_sum hG hrep hb p _ _ _ hsm]
      simp [List.foldr_append]
    have hih : ∀ i, ‖(p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
        C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
          D ^ l.length * (l.map mnorm).prod := by
      intro i
      have h := ih hl' (p ++ [i])
      rw [List.length_append, List.length_singleton,
        show p.length + 1 + l.length = p.length + (l.length + 1) by omega] at h
      exact h
    have hK : 0 ≤ C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
        D ^ l.length * (l.map mnorm).prod :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC.le _) (Nat.cast_nonneg _))
        (pow_nonneg hD0 _)) (prod_mnorm_nonneg l)
    have hsum : ∑ i, |r i| ≤ D * mnorm X := by
      rw [hr]
      exact hD r
    show ‖p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v))‖ ≤ _
    rw [e2]
    calc ‖∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖
        ≤ ∑ i, |r i| * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) := by
          refine norm_sum_le_of_le _ fun i _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hih i) (abs_nonneg _)
      _ = (∑ i, |r i|) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (D * mnorm X) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          mul_le_mul_of_nonneg_right hsum hK
      _ = _ := by
          simp only [List.length_cons, List.map_cons, List.prod_cons]
          ring

theorem wordBound_of_basis {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ}
    (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial) :
    WordBound G π v := by
  have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
  refine ⟨C * (D + 1), by positivity, fun l hl => ?_⟩
  have h := mixed_bound hG hrep hb hsp D hD0 hD hexp hv C hC hbound l hl []
  simp only [List.foldr_nil, List.length_nil, Nat.zero_add] at h
  refine h.trans ?_
  have hP := prod_mnorm_nonneg l
  have hpow : D ^ l.length ≤ (D + 1) ^ (l.length + 1) :=
    (pow_le_pow_left₀ hD0 (by linarith) _).trans (pow_le_pow_right₀ hD1 (Nat.le_succ _))
  have hCk : 0 ≤ C ^ (l.length + 1) := pow_nonneg hC.le _
  have hf : (0 : ℝ) ≤ l.length.factorial := Nat.cast_nonneg _
  rw [mul_pow]
  calc C ^ (l.length + 1) * l.length.factorial * D ^ l.length * (l.map mnorm).prod
      = (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) * D ^ l.length := by ring
    _ ≤ (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) *
          (D + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hCk hf) hP)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

end
