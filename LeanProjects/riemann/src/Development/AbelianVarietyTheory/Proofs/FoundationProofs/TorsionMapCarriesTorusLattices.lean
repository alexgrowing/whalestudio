import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OkLinearTorsionCorrespondenceMapsLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_coords_of_mem_LaB (D : D7) (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : VC D N N') (hy : y ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  unfold LaB at hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, i, rfl⟩ := hz
    refine ⟨Pi.single i w, fun j => ?_, ?_⟩
    · by_cases h : j = i
      · subst h; simpa using hw
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨w', hw', rfl⟩ := hz
    refine ⟨w + w', fun j => add_mem (hw j) (hw' j), ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨fun j => -w j, fun j => neg_mem (hw j), ?_⟩
    simp only [neg_smul, Finset.sum_neg_distrib]

theorem adpB_lattices : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ n : ℕ, 0 < n → (∀ x x' y y', AdpB D (tor0 D cc δ) M ρ b n x x' → AdpB D (tor0 D cc δ) M ρ b n y y' → AdpB D (tor0 D cc δ) M ρ b n (x - y) (x' - y')) ∧ (∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → ∃ t', AdpB D (tor0 D cc δ) M ρ b n t t') ∧ ∀ (k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D (tor0 D cc δ) Y, ∃ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ (∀ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, ∃ x ∈ LaS D (tor0 D cc δ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ ∀ x x', AdpB D (tor0 D cc δ) M ρ b n x x' → (x ∈ LaS D (tor0 D cc δ) Y ↔ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y) := by
  intro D hG hS cc δ hc M ρ hK hD hM N N' r b hb n hn
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hneg : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) (-t) (-t') := by
    intro t t' h
    have := h5 (-1) t t' h
    simpa using this
  have hsub : ∀ t t' u u', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) u u' →
      StarPt M ρ (lamOf D cc δ) (t - u) (t' - u') := by
    intro t t' u u' h h'
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact h4 _ _ _ _ h (hneg _ _ h')
  have hone : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' →
      (t ∈ lamOf D cc δ ↔ t' ∈ lamConj M ρ (lamOf D cc δ)) := by
    intro t t' h
    simpa using h6 1 t t' h
  have hex : ∀ t, InRationalLattice (lamOf D cc δ) t → ∃ t', StarPt M ρ (lamOf D cc δ) t t' := by
    intro t hq
    refine h1 _ hq ?_
    by_cases h : t ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  have hex' : ∀ t', InRationalLattice (lamConj M ρ (lamOf D cc δ)) t' → ∃ t, StarPt M ρ (lamOf D cc δ) t t' := by
    rintro t' ⟨m, hm, ht'⟩
    obtain ⟨t, -, ht⟩ := h7 m hm (fun t h h' => hM t ⟨m, hm, h⟩ h') t' ht'
    exact ⟨t, ht⟩
  have hst : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamOf D cc δ,
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
    intro a w hw
    have := h5 a w 0 (Or.inl ⟨hw, zero_mem _⟩)
    rw [hone _ _ this, mul_zero]; exact zero_mem _
  have hst' : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamConj M ρ (lamOf D cc δ),
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamConj M ρ (lamOf D cc δ) := by
    intro a w hw
    have := h5 a 0 w (Or.inl ⟨zero_mem _, hw⟩)
    rw [← hone _ _ this, mul_zero]; exact zero_mem _
  have hT := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  have hT' := good_torConj D hG cc δ M ρ hK hD
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ _ _ ⟨c, c', hc, rfl, rfl, hcc⟩ ⟨d, d', hd, rfl, rfl, hdd⟩
    refine ⟨c - d, c' - d', fun j => ?_, ?_, ?_, fun j => ?_⟩
    · obtain ⟨m, hm, h⟩ := hc j
      obtain ⟨m', hm', h'⟩ := hd j
      refine ⟨m * m', Nat.mul_pos hm hm', ?_⟩
      have : ((m * m' : ℕ) : ℂ) * (c - d) j = m' • ((m : ℂ) * c j) - m • ((m' : ℂ) * d j) := by
        simp only [nsmul_eq_mul, Pi.sub_apply]; push_cast; ring
      rw [this]
      exact sub_mem (AddSubgroup.nsmul_mem _ h _) (AddSubgroup.nsmul_mem _ h' _)
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · show StarPt M ρ (lamOf D cc δ) ((c j - d j) / n) ((c' j - d' j) / n)
      rw [sub_div, sub_div]
      exact hsub _ _ _ _ (hcc j) (hdd j)
  · intro x m hm hmx
    obtain ⟨w, hw, hsum⟩ := exists_coords_of_mem_LaB D _ b _ hmx
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hq : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
      intro j
      refine hex _ ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
      rw [this]; exact hw j
    choose t' ht' using hq
    refine ⟨_, fun j => w j / m, fun j => (n : ℂ) * t' j, ?_, ?_, rfl, ?_⟩
    · intro j
      refine ⟨m, hm, ?_⟩
      have : (m : ℂ) * (w j / m) = w j := by field_simp
      rw [this]; exact hw j
    · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
      rw [hx, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← div_eq_inv_mul]
    · intro j
      have : (n : ℂ) * t' j / n = t' j := by field_simp
      show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
      rw [this]; exact ht' j
  · intro k Y hk hkn hY
    obtain ⟨A1, A2⟩ := GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice D (tor0 D cc δ) (torConj D (tor0 D cc δ) M ρ) hT hT' hst N N' r b hb.1
      (StarPt M ρ (lamOf D cc δ)) hex (fun t t₁ t₂ h h' => (h2 t t₁ t₂ h).1 h') h4 h5
      (fun m t t' h => (h6 m t t' h).1) n k Y hn hk hkn hY
    obtain ⟨B1, B2⟩ := GlobalTheory.T.okLinear_torsionCorrespondence_maps_lattice D (torConj D (tor0 D cc δ) M ρ) (tor0 D cc δ) hT' hT hst' N N' r b hb.1
      (fun t' t => StarPt M ρ (lamOf D cc δ) t t') hex'
      (fun t t₁ t₂ h h' => (hone _ _ (hsub _ _ _ _ h h')).2 (by rw [sub_self]; exact zero_mem _))
      (fun t t' u u' h h' => h4 _ _ _ _ h h') (fun a t t' h => h5 a _ _ h)
      (fun m t t' h => (h6 m _ _ h).2) n k Y hn hk hkn hY
    refine ⟨fun x hx => ?_, fun x' hx' => ?_, ?_⟩
    · obtain ⟨c, c', hc, hxc, hcc, hmem⟩ := A1 x hx
      exact ⟨_, hmem, c, c', hc, hxc, rfl, hcc⟩
    · obtain ⟨c', c, hc', hxc, hcc, hmem⟩ := B1 x' hx'
      refine ⟨_, hmem, c, c', fun j => ?_, rfl, hxc, hcc⟩
      obtain ⟨m, hm, h⟩ := hc' j
      refine ⟨m, hm, ?_⟩
      have h' := (h6 (m * n) _ _ (hcc j)).2 (by
        have : ((m * n : ℕ) : ℂ) * (c' j / n) = m * c' j := by push_cast; field_simp
        rw [this]; exact h)
      have : ((m * n : ℕ) : ℂ) * (c j / n) = m * c j := by push_cast; field_simp
      rw [this] at h'; exact h'
    · rintro _ _ ⟨c, c', -, rfl, rfl, hcc⟩
      exact ⟨A2 c c' hcc, B2 c' c hcc⟩

end GlobalTheory.ThetaConj
