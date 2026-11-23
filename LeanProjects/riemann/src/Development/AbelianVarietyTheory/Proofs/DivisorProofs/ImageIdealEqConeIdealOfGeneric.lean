import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt
open AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.Twist GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem form_eq_zero_of_generic {K : Type} [Field K] (S : LinSys K) [IsReduced S.Y] {η : S.Y}
    (hη : IsGenericPoint η Set.univ) {d : ℕ} {g : MvPolynomial (Fin S.N) K} (hg : g.IsHomogeneous d)
    (h : η ∉ nonzeroLocus (S.form hg)) : S.form hg = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus (S.form hg)).isOpen).2 ⟨y, trivial, hy.2⟩)).elim

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem imageIdeal_eq_coneIdeal_of_generic (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (S : LinSys K)
    [IsIntegral S.Y] (x : S.Pt Ω) (hx : IsGenericPoint (ptOf x.1) Set.univ) (a : Ω) (y : Fin S.N → Ω) (ha : a ≠ 0)
    (h : S.coords x.1 = a • y) : S.imageIdeal = coneIdeal K y := by
  rw [← coneIdeal_smul ha y, ← h]
  have key : ∀ {d : ℕ} {g : MvPolynomial (Fin S.N) K} (_ : g.IsHomogeneous d),
      g ∈ S.imageIdeal ↔ g ∈ coneIdeal K (S.coords x.1) := fun {d g} hg => by
    rw [mem_coneIdeal_of_isHomogeneous _ hg, aeval_def,
      ← congrArg (fun φ => eval₂ φ (S.coords x.1) g) (LinSys.baseHom_ptOver x)]
    refine ⟨S.eval₂_coords_eq_zero x.1, fun h0 => (S.mem_imageIdeal_iff hg).2
      (form_eq_zero_of_generic S hx hg fun hm => ?_)⟩
    exact (S.powVal_ne_zero_iff x.1 _).2 hm ((S.powVal_form x.1 hg).trans h0)
  ext g
  rw [S.isHomogeneous_imageIdeal.mem_iff, (isHomogeneous_coneIdeal (K := K) (S.coords x.1)).mem_iff]
  exact forall_congr' fun d => key (DirectSum.decompose (homogeneousSubmodule (Fin S.N) K) g d).2

end GlobalTheory.CompHt
