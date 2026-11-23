import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealUnitaryCovolumeSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianGramDiagonalSignatureUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeCongruenceSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamilyStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem GlobalTheory.ClassSum.sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r) (S : Finset (Fin m)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, ∀ j ∈ S, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) → (∀ i ∈ S, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧ ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧ ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧ IsOrth (X i) (x0 i)) → ∑ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤ ENNReal.ofReal ((M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r M m G Λ Ψ X g x0 S g0 hr hM hU hΛ hg0 hg hT hUE hX
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
  · subst hS; simp
  obtain ⟨hG0, hΨ0, -, -, hO0⟩ := hX i0 hi0
  subst hG0
  subst hΨ0
  obtain ⟨L, hLset, hLhat, hL⟩ := GlobalTheory.T.self_dual_lattice_real_completion E r (X i0).Gm Λ g0 hΛ hg0
  obtain ⟨γ, s, hγs, hpair⟩ := GlobalTheory.T.self_dual_lattice_congruence_subgroups E r M m (X i0).Gm Λ L g g0 S (fun i => (X i).Γ) (fun i => (X i).Λ)
    (by omega) hΛ hg0 hLset hLhat hg hT (fun i hi => ⟨(hX i hi).2.2.1, (hX i hi).2.2.2.1⟩)
  have hherm : ∀ a b, cc ((X i0).Gm a b) = (X i0).Gm b a := (X i0).Gm_herm
  have tr : ∀ (Ψ1 : Finset (E →+* ℂ)) (G1 : Matrix (Fin r) (Fin r) E) (x1 : Frame Ψ1 r) (p1 : ℕ)
      (H : Subgroup (GL (Fin r) E)), Ψ1 = (X i0).Ψ → G1 = (X i0).Gm →
      (∀ τ : Ψ1, gram τ.1 G1 (mat x1 τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) →
      covolume (inReal Ψ1 G1 H) (realSU Ψ1 G1) (riemHaar Ψ1 G1 x1) =
        covolume (inReal (X i0).Ψ (X i0).Gm H) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro Ψ1 G1 x1 p1 H h1 h2 h3
    subst h1 h2
    rw [GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame E r p1 (X i0).p0 _ _ x1 (x0 i0) hherm h3 hO0]
  set Δ : Fin m → Subgroup (GL (Fin r) E) := fun i => ((X i).Γ).map (MulAut.conj (γ i)⁻¹).toMonoidHom with hΔ
  have hback : ∀ i, (Δ i).map (MulAut.conj (γ i)).toMonoidHom = (X i).Γ := by
    intro i
    rw [hΔ, Subgroup.map_map]
    have : (MulAut.conj (γ i)).toMonoidHom.comp (MulAut.conj (γ i)⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext δ : 1
      simp [mul_assoc]
    rw [this, Subgroup.map_id]
  have hterm : ∀ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
      (riemHaar (X i).Ψ (X i).Gm (x0 i)) =
      covolume (inReal (X i0).Ψ (X i0).Gm (Δ i)) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro i hi
    obtain ⟨hGi, hΨi, -, -, hOi⟩ := hX i hi
    rw [tr (X i).Ψ (X i).Gm (x0 i) (X i).p0 (X i).Γ hΨi hGi hOi, ← hback i]
    exact GlobalTheory.T.hermitian_gram_diagonal_signature_unitary E r (X i0).p0 (X i0).Ψ (X i0).Gm (x0 i0) (γ i) (Δ i) hherm hO0 (hγs i hi).1
  obtain ⟨J, t, ht, hcount⟩ := GlobalTheory.T.signature_unitary_lattice_family E r M (X i0).p0 (X i0).Gm L (X i0).Ψ (x0 i0) (Fin m) S s Δ hr
    (by omega) hL (X i0).cmType hO0 (fun i hi => (hγs i hi).2.1)
    (fun i hi j hj h => hUE i hi j hj (hpair i hi j hj h)) (fun i hi => (hγs i hi).2.2)
  have hV := GlobalTheory.T.real_unitary_covolume_sum hP E r (X i0) L (x0 i0) J t hr hU hL hO0 ht
  rw [Finset.sum_congr rfl hterm]
  refine hcount.trans ?_
  calc (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ∑' j, covolume (inReal (X i0).Ψ (X i0).Gm (ratStab (X i0).Gm (L : Set (Fin r → E)) (t j))) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0))
      ≤ (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
        gcongr
    _ = _ := by
        rw [mul_assoc ((M : ℝ) ^ (2 * fdeg E * r ^ 2)), ENNReal.ofReal_mul (p := (M : ℝ) ^ (2 * fdeg E * r ^ 2)) (by positivity),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
