import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel Matrix

namespace PositivityTheory.Pf1.SegRepC.Twist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_ne_zero_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hi : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  have := hi
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
  exact exists_ne (0 : ρ.asModule)

theorem exists_nabs_ne_one : ∃ x : kˣ, nabs k x ≠ 1 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  exact ⟨ϖ, fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)⟩

theorem not_equiv_segTerm {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (l : ℕ) {a b : Fin l}
    (hab : a ≠ b) : IsEmpty ((segTerm σ.ρ l a).Equiv (segTerm σ.ρ l b)) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨x, hx⟩ := exists_nabs_ne_one (k := k)
  let z : GL (Fin d) k := GeneralLinearGroup.scalar (Fin d) x
  have hz : ∀ g : GL (Fin d) k, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = x ^ d := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id σ.ρ σ.smooth σ.irr (σ.ρ z) fun g y => by
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]
  have hcz : ∀ y, σ.ρ z y = c • y := fun y => by
    rw [hc]; rfl
  obtain ⟨v, hv⟩ := exists_ne_zero_irr σ.ρ σ.irr
  have hc0 : c ≠ 0 := fun e => hv (by
    have h2 : σ.ρ z⁻¹ (σ.ρ z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hcz, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have hφv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h3 : φ.toLinearEquiv ((segTerm σ.ρ l a) z v) = (segTerm σ.ρ l b) z (φ.toLinearEquiv v) :=
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap z v
  simp only [segTerm, twist_apply, detChar_apply, hdet, map_smul, hcz, smul_smul] at h3
  have h4 := mul_right_cancel₀ hc0 (smul_left_injective ℂ hφv h3)
  rw [val_absPow, val_absPow, Complex.cpow_natCast, Complex.cpow_natCast] at h4
  have h5 : nabs k (x ^ d) ^ (a : ℕ) = nabs k (x ^ d) ^ (b : ℕ) := by exact_mod_cast h4
  have hpos : 0 < nabs k (x ^ d) := nabs_pos' k _
  have hne : nabs k (x ^ d) ≠ 1 := by
    have hpow : nabs k (x ^ d) = nabs k x ^ d := by simp [nabs]
    rw [hpow]
    exact fun e => hx ((pow_eq_one_iff_of_nonneg (nabs_pos' k x).le hd.ne').1 e)
  exact hab (Fin.ext (pow_right_injective₀ hpos hne h5))

end PositivityTheory.Pf1.SegRepC.Twist

end
