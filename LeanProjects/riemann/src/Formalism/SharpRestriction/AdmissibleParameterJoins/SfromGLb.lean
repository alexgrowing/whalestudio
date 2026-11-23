import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLa
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdForm_apply (K : Type) [Field K] [StarRing K] (M : ℕ) (x y : Fin M → K) :
    StandardLattice.stdForm K M x y = ∑ i, star (x i) * y i := rfl

theorem std_ortho (K : Type) [Field K] [NumberField K] [StarRing K] (M : ℕ) :
    IsOrthoLattice (StandardLattice.stdForm K M) (StandardLattice.stdLat K M) M := by
  have e : (fun i : Fin M => (Pi.single i 1 : Fin M → K)) = Pi.basisFun K (Fin M) := by
    funext i; simp
  refine ⟨fun i => Pi.single i 1, ?_, ?_, rfl, fun i j => ?_⟩
  · rw [e]; exact (Pi.basisFun K (Fin M)).linearIndependent
  · rw [e]; exact (Pi.basisFun K (Fin M)).span_eq
  · by_cases hij : i = j
    · subst hij; simp [stdForm_apply, Pi.single_apply]
    · simp [stdForm_apply, Pi.single_apply, hij, Ne.symm hij]

theorem massRatio_host_of (D : D7) (h : StandardLattice.MassRatio₂ D) : ∀ (j : ℕ), 3 ≤ j →
    ∀ (V V' : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
      [IsScalarTower (𝓞 D.host.E) D.host.E V] [AddCommGroup V'] [Module D.host.E V']
      [Module (𝓞 D.host.E) V'] [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E)
      (L : Submodule (𝓞 D.host.E) V) (L' : Submodule (𝓞 D.host.E) V'),
      h.IsSymm → h'.IsSymm → IsOrthoLattice h L j → IsOrthoLattice h' L' (j - 1) →
      mass h L / mass h' L' = massRatioRightSide D.host.E j := by
  intro j hj V V' _ _ _ _ _ _ _ _ hV hV' L L' _ _ hL hL'
  rw [mass_ortho_eq hL (std_ortho D.host.E j), mass_ortho_eq hL' (std_ortho D.host.E (j - 1))]
  exact h j hj

theorem massRatio_all_of (h : StandardLattice.SiegelMassRatioCM) : SiegelMassRatio := by
  intro K _ _ _ hK M hM V V' _ _ _ _ _ _ _ _ hV hV' L L' _ _ hL hL'
  rw [mass_ortho_eq hL (std_ortho K M), mass_ortho_eq hL' (std_ortho K (M - 1))]
  exact h K hK M hM

theorem zetaR_eq (M : ℕ) (hM : 2 ≤ M) : (riemannZeta (M : ℂ)).re = StandardLattice.zetaR M := by
  have h1 : (1 : ℝ) < ((M : ℂ)).re := by
    simp only [Complex.natCast_re]; exact_mod_cast hM
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  have h2 : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (M : ℂ)) = ((StandardLattice.zetaR M : ℝ) : ℂ) := by
    unfold StandardLattice.zetaR
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [h2, Complex.ofReal_re]

theorem lBound_host_of (D : D7) (h : StandardLattice.gram_det_kernel_dual_lattice D) : ∀ i : ℕ, 2 ≤ i →
    |Real.log (lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re := by
  intro i hi
  rw [zetaR_eq i hi]
  exact h i hi

end Formalism.MainNotions.J

end
