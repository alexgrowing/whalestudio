import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue

noncomputable section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AnisotropicResidueNonvanishing

variable {D : D7} {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r)

theorem isIwasawa (l : Lvl V) (hl : l.Good) (h : HasIw d l.K) : IsIwasawa (absDet d) l.K :=
  ⟨h, fun p hp => triv_of_isCompact (isClosed_stab d) (continuous_absDet d) hl.isCompact_K p hp⟩

theorem absDet_rat (q : stab d) (hq : (q : GA D V) ∈ GQ V) : absDet d q = 1 := by
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 ((mem_GQ_iff _ _).1 hq)
  have hα : (onX d q).1 = rat (d.qX * γ * d.e) := by
    rw [eq_of_mul_jX d (mul_jX d q), ← hγ, rat_mul, rat_mul, Matrix.mul_assoc]
    rfl
  have hdet : ((Matrix.GeneralLinearGroup.det (onX d q) : (AE D)ˣ) : AE D)
      = incA D (d.qX * γ * d.e).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hα, RingHom.map_det]
    rfl
  have hne : (d.qX * γ * d.e).det ≠ 0 := by
    intro h0
    have h1 : (1 : AE D) = 0 := by
      rw [← (Matrix.GeneralLinearGroup.det (onX d q)).mul_inv, hdet, h0, map_zero, zero_mul]
    exact one_ne_zero (incA_injective (D := D) (by rw [map_one, map_zero]; exact h1))
  have hu : Matrix.GeneralLinearGroup.det (onX d q)
      = Units.map (incA D).toMonoidHom (Units.mk0 _ hne) := Units.ext hdet
  show absA D (Matrix.GeneralLinearGroup.det (onX d q)) = 1
  rw [hu]
  exact absE_inclR _

theorem witt_spherical_section_left_invariant_rational_parabolic (l : Lvl V) (hl : l.Good) (h : HasIw d l.K) (s : ℂ) :
    LeftInv (stab d ⊓ GQ V) (sphericalSectionIwasawa d l.K s) := by
  have hI : IsIwasawa (absDet d) l.K := isIwasawa d l hl h
  intro γ hγ g
  have hγ' := Subgroup.mem_inf.1 hγ
  have e : iwAbs (absDet d) l.K (((⟨γ, hγ'.1⟩ : stab d) : GA D V) * g) = iwAbs (absDet d) l.K g := by
    rw [hI.iwAbs_left, absDet_rat d _ hγ'.2, one_mul]
  show npow (iwAbs (absDet d) l.K (γ * g)) _ = npow (iwAbs (absDet d) l.K g) _
  exact congrArg (fun t => npow t (s + (rhoH V r : ℂ))) e

end GlobalTheory.AnisotropicResidueNonvanishing

end
