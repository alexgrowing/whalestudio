import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PGsWitt

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

def GsSliceP : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ S : Set (B.Mat k r),
    (∀ y ∈ S, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, n * y * n' ∈ S) ∧
    (∀ y ∈ S, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z', α * y * β ∈ S → Rel z z' y (α * y * β)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Fl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
        (Fl g).1 ∈ UWset k r z ∧ (Fl g).2 ∈ UWset k r z' ∧ (Fl g).1 * g * (Fl g).2 ∈ S)

theorem gsFrames_of_slice (hS : GsSliceP) : GsFrames := by
  intro k r z z' hk hr hz hz'
  obtain ⟨S, hsat, hstab, hloc⟩ := hS k r z z' hk hr hz hz'
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have key : ∀ (g : B.Mat k r) (p : B.Mat k r × B.Mat k r), p.1 ∈ UWset k r z → p.2 ∈ UWset k r z' →
      ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, p.1 * g * p.2 ∈ S → p.1 * (n⁻¹ * g * n') * p.2 ∈ S := by
    intro g p ha hb n hn n' hn' hy
    have hau := Wz.unit _ ha
    have hbu := Wz'.unit _ hb
    have hx : p.1 * n⁻¹ * p.1⁻¹ ∈ Nset k r := (unitary_weyl_normal_holds k r z hz.1 _ ha _ (Nc.inv_mem n hn)).1
    have hy' : p.2⁻¹ * n' * p.2 ∈ Nset k r := by
      have := (unitary_weyl_normal_holds k r z' hz'.1 _ (Wz'.inv_mem _ hb) _ hn').1
      rwa [Matrix.nonsing_inv_nonsing_inv _ hbu] at this
    have e : p.1 * (n⁻¹ * g * n') * p.2 = (p.1 * n⁻¹ * p.1⁻¹) * (p.1 * g * p.2) * (p.2⁻¹ * n' * p.2) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hau, Matrix.mul_nonsing_inv_cancel_left _ _ hbu]
    rw [e]; exact hsat _ hy _ hx _ hy'
  let Fr : B.Mat k r → Set (B.Mat k r × B.Mat k r) :=
    fun g => {p | p.1 ∈ UWset k r z ∧ p.2 ∈ UWset k r z' ∧ p.1 * g * p.2 ∈ S}
  refine ⟨Fr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg hG
    obtain ⟨O, Fl, -, hgO, -, hFl⟩ := hloc g hg hG
    exact ⟨Fl g, hFl g hgO hg hG⟩
  · intro g _ _ p hp
    exact ⟨hp.1, hp.2.1⟩
  · intro g _ _ n hn n' hn'
    ext p
    constructor
    · rintro ⟨ha, hb, hy⟩
      have hnu := Nc.unit n hn
      have hnu' := Nc.unit n' hn'
      have h2 := key (n⁻¹ * g * n') p ha hb n⁻¹ (Nc.inv_mem n hn) n'⁻¹ (Nc.inv_mem n' hn') hy
      have e : n⁻¹⁻¹ * (n⁻¹ * g * n') * n'⁻¹ = g := by
        rw [Matrix.nonsing_inv_nonsing_inv n hnu]
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hnu, Matrix.mul_nonsing_inv n' hnu',
          Matrix.mul_one]
      rw [e] at h2
      exact ⟨ha, hb, h2⟩
    · rintro ⟨ha, hb, hy⟩
      exact ⟨ha, hb, key g p ha hb n hn n' hn' hy⟩
  · intro g _ _ c hc n hn n' hn' c' hc' p hp
    have hcu := Wz.unit c hc
    have hcu' := Wz'.unit c' hc'
    refine ⟨Wz.mul_mem _ hp.1 _ (Wz.inv_mem c hc), Wz'.mul_mem _ (Wz'.inv_mem c' hc') _ hp.2.1, ?_⟩
    show p.1 * c⁻¹ * (c * (n⁻¹ * g * n') * c') * (c'⁻¹ * p.2) ∈ S
    have e : p.1 * c⁻¹ * (c * (n⁻¹ * g * n') * c') * (c'⁻¹ * p.2) = p.1 * (n⁻¹ * g * n') * p.2 := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hcu, Matrix.mul_nonsing_inv_cancel_left _ _ hcu']
    rw [e]
    exact key g p hp.1 hp.2.1 n hn.1 n' hn'.1 hp.2.2
  · intro g _ _ p hp q hq
    have hpu := Wz.unit _ hp.1
    have hpu' := Wz'.unit _ hp.2.1
    have e : q.1 * p.1⁻¹ * (p.1 * g * p.2) * (p.2⁻¹ * q.2) = q.1 * g * q.2 := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hpu, Matrix.mul_nonsing_inv_cancel_left _ _ hpu']
    have h := hstab _ hp.2.2 _ (Wz.mul_mem _ hq.1 _ (Wz.inv_mem _ hp.1)) _ (Wz'.mul_mem _ (Wz'.inv_mem _ hp.2.1) _ hq.2.1)
      (by rw [e]; exact hq.2.2)
    rwa [e] at h
  · intro g₀ hg₀ hG₀
    obtain ⟨O, Fl, hO, hgO, hs, hFl⟩ := hloc g₀ hg₀ hG₀
    exact ⟨O, Fl, hO, hgO, hs, fun g h1 h2 h3 => hFl g h1 h2 h3⟩

theorem gramSlice_of_slice (hS : GsSliceP) : GramSlice := gramSlice_of gram_schmidt_witt (gsFrames_of_slice hS)

end PI.UnitaryGroupMassFormula.DLm.Gram
