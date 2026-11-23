import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen

namespace UpperTheory.KStar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)

theorem r_odd (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have := R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem exists_cycZ_pow_ne_one : ∃ g : GE N, cycZ D.host.E N.Om (X.l i) g ^ (D.R.t * D.R.r) ≠ 1 :=
  _root_.KStar.Tree.exists_cyc_pow_ne_one (X.l i) D.host.E N.Om _ (D.R.t_odd.mul (r_odd D.R)).pos.ne'

theorem exists_eps_eq_pow_nu :
    ∃ (g : GE N) (u : (X.O0 i)ˣ),
      ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ (D.R.t * D.R.r) - 1 = (X.l i : X.O0 i) ^ nu X i * u := by
  obtain ⟨g, u, hu⟩ := _root_.KStar.Tree.exists_eq_pow_nuOf_mul_unit (X.l i) (cycZ D.host.E N.Om (X.l i)) (D.R.t * D.R.r)
    (exists_cycZ_pow_ne_one X i)
  refine ⟨g, Units.map (algebraMap ℤ_[X.l i] (X.O0 i)).toMonoidHom u, ?_⟩
  have h := congrArg (algebraMap ℤ_[X.l i] (X.O0 i)) hu
  rw [map_sub, map_pow, map_one, map_mul, map_pow, map_natCast] at h
  exact h

theorem nu_pos_of_res (K : Type) [CommRing K] [Nontrivial K] [Algebra (X.O0 i) K]
    (h : ∀ g : GE N, algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ (D.R.t * D.R.r) = 1) : 0 < nu X i := by
  exact _root_.KStar.Tree.nuOf_pos_of_res (X.l i) (cycZ D.host.E N.Om (X.l i)) (D.R.t * D.R.r) (exists_cycZ_pow_ne_one X i)
    ((algebraMap (X.O0 i) K).comp (algebraMap ℤ_[X.l i] (X.O0 i))) h

end UpperTheory.KStar
