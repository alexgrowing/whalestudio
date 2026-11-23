import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFdGramCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.UnipotentHaarConjInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

def GsWitt : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r z z' g₁ → Zhat k r z z' g₁ = Zhat k r z z' g₂ →
      ∃ c ∈ UWset k r z, ∃ n ∈ C2.N0set k r z, ∃ n' ∈ C2.N0set k r z', ∃ c' ∈ UWset k r z',
        g₂ = c * (n⁻¹ * g₁ * n') * c'

def GsFrames : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ Fr : B.Mat k r → Set (B.Mat k r × B.Mat k r),
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → (Fr g).Nonempty) ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ p ∈ Fr g, p.1 ∈ UWset k r z ∧ p.2 ∈ UWset k r z') ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, Fr (n⁻¹ * g * n') = Fr g) ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ c ∈ UWset k r z, ∀ n ∈ C2.N0set k r z, ∀ n' ∈ C2.N0set k r z',
      ∀ c' ∈ UWset k r z', ∀ p ∈ Fr g, (p.1 * c⁻¹, c'⁻¹ * p.2) ∈ Fr (c * (n⁻¹ * g * n') * c')) ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ p ∈ Fr g, ∀ q ∈ Fr g, Rel z z' (p.1 * g * p.2) (q.1 * g * q.2)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Fl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g → Fl g ∈ Fr g)

section rel

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem rel_of (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {a b x y : B.Mat k r} (hx : x ∈ C2.N0set k r z)
    (hy : y ∈ C2.N0set k r z') (hb : b = x * a * y) : Rel z z' a b := by
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have hux := Gz.unit x hx
  refine ⟨x⁻¹, Gz.inv_mem x hx, 1, Gz.one_mem, y, hy, 1, Gz'.one_mem, 1, one_mem_UW z, 1, one_mem_UW z', ?_, ?_⟩
  · rw [Matrix.nonsing_inv_nonsing_inv x hux, hb]; simp
  · simp

theorem mem_of_rel (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {a b : B.Mat k r} (h : Rel z z' a b) :
    ∃ x ∈ C2.N0set k r z, ∃ y ∈ C2.N0set k r z', b = x * a * y := by
  obtain ⟨n, hn, m, hm, n', hn', m', hm', c, hc, c', hc', hb, ha⟩ := h
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have hcu := Wz.unit c hc
  have hcu' := Wz'.unit c' hc'
  have hmu := Gz.unit m hm
  have hmu' := Gz'.unit m' hm'
  have K : m * c⁻¹ * a * c'⁻¹ * m'⁻¹ = a := by
    calc m * c⁻¹ * a * c'⁻¹ * m'⁻¹ = m * c⁻¹ * (c * (m⁻¹ * a * m') * c') * c'⁻¹ * m'⁻¹ := by rw [ha]
      _ = a := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv_cancel_left c' _ hcu', Matrix.mul_nonsing_inv m' hmu', Matrix.mul_one,
          Matrix.nonsing_inv_mul_cancel_left c _ hcu, Matrix.mul_nonsing_inv_cancel_left m _ hmu]
  have hP : c * n⁻¹ * c⁻¹ ∈ C2.N0set k r z := unipotent_normal_unitary hz hc (Gz.inv_mem n hn)
  have hX : c * m * c⁻¹ ∈ C2.N0set k r z := unipotent_normal_unitary hz hc hm
  have hY : c'⁻¹ * m'⁻¹ * c' ∈ C2.N0set k r z' := by
    have := unipotent_normal_unitary hz' (Wz'.inv_mem c' hc') (Gz'.inv_mem m' hm')
    rwa [Matrix.nonsing_inv_nonsing_inv c' hcu'] at this
  have hQ : c'⁻¹ * n' * c' ∈ C2.N0set k r z' := by
    have := unipotent_normal_unitary hz' (Wz'.inv_mem c' hc') hn'
    rwa [Matrix.nonsing_inv_nonsing_inv c' hcu'] at this
  refine ⟨c * n⁻¹ * c⁻¹ * (c * m * c⁻¹), Gz.mul_mem _ hP _ hX, c'⁻¹ * m'⁻¹ * c' * (c'⁻¹ * n' * c'),
    Gz'.mul_mem _ hY _ hQ, ?_⟩
  calc b = c * (n⁻¹ * a * n') * c' := hb
    _ = c * (n⁻¹ * (m * c⁻¹ * a * c'⁻¹ * m'⁻¹) * n') * c' := by rw [K]
    _ = c * n⁻¹ * c⁻¹ * (c * m * c⁻¹) * a * (c'⁻¹ * m'⁻¹ * c' * (c'⁻¹ * n' * c')) := by
        simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hcu,
          Matrix.mul_nonsing_inv_cancel_left _ _ hcu']

theorem rel_trans (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {a b c : B.Mat k r} (h1 : Rel z z' a b)
    (h2 : Rel z z' b c) : Rel z z' a c := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_of_rel hz hz' h1
  obtain ⟨x', hx', y', hy', rfl⟩ := mem_of_rel hz hz' h2
  refine rel_of hz hz' ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz).mul_mem _ hx' _ hx)
    ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz').mul_mem _ hy _ hy') ?_
  simp only [Matrix.mul_assoc]

end rel

theorem gf_eq_of_zhat {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g₁ g₂ : B.Mat k r}
    (h : Zhat k r z z' g₁ = Zhat k r z z' g₂) : Gf k r z z' g₂ = Gf k r z z' g₁ := by
  unfold Gf Dmin
  rw [h]

open Classical in
theorem gramSlice_of (hW : GsWitt) (hF : GsFrames) : GramSlice := by
  intro k r z z' hk hr hz hz'
  obtain ⟨Fr, hne, hU, hinv, heq, hrel, hloc⟩ := hF k r z z' hk hr hz hz'
  let T : B.Mat k r → B.Mat k r × B.Mat k r := fun g => if h : (Fr g).Nonempty then h.some else (1, 1)
  have hT : ∀ g ∈ B.GV k r, 0 < Gf k r z z' g → T g ∈ Fr g := by
    intro g hg hG
    have h := hne g hg hG
    simp only [T, dif_pos h]
    exact h.some_mem
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  refine ⟨T, fun g hg hG => hU g hg hG _ (hT g hg hG), ?_, ?_, ?_⟩
  · intro g hg hG n hn n' hn'
    simp only [T, hinv g hg hG n hn n' hn']
  · intro g₁ hg₁ g₂ hg₂ hG₁ hZ
    have hG₂ : 0 < Gf k r z z' g₂ := by rw [gf_eq_of_zhat hZ]; exact hG₁
    obtain ⟨c, hc, n, hn, n', hn', c', hc', e⟩ := hW k r z z' hk hr hz hz' g₁ hg₁ g₂ hg₂ hG₁ hZ
    set p := T g₁ with hp
    have hp1 : p ∈ Fr g₁ := hT g₁ hg₁ hG₁
    obtain ⟨hpa, hpb⟩ := hU g₁ hg₁ hG₁ p hp1
    have hp2 : (p.1 * c⁻¹, c'⁻¹ * p.2) ∈ Fr g₂ := by
      rw [e]; exact heq g₁ hg₁ hG₁ c hc n hn n' hn' c' hc' p hp1
    have hr1 : Rel z z' (nrm T g₁) (p.1 * c⁻¹ * g₂ * (c'⁻¹ * p.2)) := by
      have hua := Wz.unit p.1 hpa
      have hub := Wz'.unit p.2 hpb
      have hcu := Wz.unit c hc
      have hcu' := Wz'.unit c' hc'
      have hx : p.1 * n⁻¹ * p.1⁻¹ ∈ C2.N0set k r z := unipotent_normal_unitary hz hpa (Gz.inv_mem n hn)
      have hy : p.2⁻¹ * n' * p.2 ∈ C2.N0set k r z' := by
        have := unipotent_normal_unitary hz' (Wz'.inv_mem p.2 hpb) hn'
        rwa [Matrix.nonsing_inv_nonsing_inv p.2 hub] at this
      refine rel_of hz hz' hx hy ?_
      show p.1 * c⁻¹ * g₂ * (c'⁻¹ * p.2) = p.1 * n⁻¹ * p.1⁻¹ * (p.1 * g₁ * p.2) * (p.2⁻¹ * n' * p.2)
      rw [e]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hcu, Matrix.nonsing_inv_mul_cancel_left _ _ hua,
        Matrix.mul_nonsing_inv_cancel_left _ _ hcu', Matrix.mul_nonsing_inv_cancel_left _ _ hub]
    have hr2 : Rel z z' (p.1 * c⁻¹ * g₂ * (c'⁻¹ * p.2)) (nrm T g₂) :=
      hrel g₂ hg₂ hG₂ _ hp2 _ (hT g₂ hg₂ hG₂)
    exact rel_trans hz hz' hr1 hr2
  · intro g₀ hg₀ hG₀
    obtain ⟨O, Fl, hO, hgO, hs, hFl⟩ := hloc g₀ hg₀ hG₀
    refine ⟨O, Fl, hO, hgO, hs, fun g hgO' hg hG => ?_⟩
    have h1 := hFl g hgO' hg hG
    obtain ⟨ha, hb⟩ := hU g hg hG _ h1
    exact ⟨ha, hb, hrel g hg hG _ h1 _ (hT g hg hG)⟩

end PI.UnitaryGroupMassFormula.DLm.Gram
