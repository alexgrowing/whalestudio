import Formalism.LocalToGlobal.InertKernelTheory.DefsMMIsom

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

namespace MMConj

theorem not_sq_padic (d p : ℕ) [Fact p.Prime] (hj : jacobiSym (-(d : ℤ)) p = -1) (y : ℚ_[p]) :
    y ^ 2 ≠ -(d : ℚ_[p]) := by
  intro hy
  have hleg : legendreSym p (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hns : ¬ IsSquare (((-(d : ℤ)) : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff (p := p)).1 hleg
  have hnd : ¬ p ∣ d := by
    intro hd
    apply hns
    have h0 : ((d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).2 hd
    refine ⟨0, ?_⟩
    push_cast
    rw [h0]
    simp
  have hdn : ‖(d : ℚ_[p])‖ = 1 := by
    have h1 : ‖(d : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) (d : ℤ)
    have h2 : ¬ ‖(d : ℚ_[p])‖ < 1 := by rw [Padic.norm_natCast_lt_one_iff]; exact hnd
    linarith [not_lt.1 h2]
  have hy1 : ‖y‖ ≤ 1 := by
    have h3 : ‖y‖ ^ 2 = 1 := by rw [← norm_pow, hy, norm_neg, hdn]
    nlinarith [norm_nonneg y]
  set z : ℤ_[p] := ⟨y, hy1⟩ with hz
  have hz2 : z ^ 2 = -(d : ℤ_[p]) := by
    apply Subtype.ext
    simp only [hz, PadicInt.coe_neg, PadicInt.coe_natCast]
    exact hy
  apply hns
  refine ⟨PadicInt.toZMod z, ?_⟩
  have h4 := congrArg (PadicInt.toZMod (p := p)) hz2
  rw [map_pow, map_neg, map_natCast] at h4
  push_cast
  rw [← h4]
  ring

theorem exists_aut_neg (d p : ℕ) [Fact p.Prime] (hj : jacobiSym (-(d : ℤ)) p = -1) (β : PadicAlgCl p)
    (hβ : β ^ 2 = -(d : PadicAlgCl p)) : ∃ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ β = -β := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(d : ℚ_[p]))) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => not_sq_padic d p hj b hb)
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (-(d : ℚ_[p]))).Monic :=
    Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have h1 := minpoly.eq_of_irreducible_of_monic (x := β) hirr (by simp [hβ]) hmon
  have h2 := minpoly.eq_of_irreducible_of_monic (x := -β) hirr (by simp [hβ]) hmon
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[p]) (E := PadicAlgCl p)).1 (h2.symm.trans h1)
  exact ⟨τ, hτ⟩

theorem aut_norm {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem aut_cont {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Continuous ((τ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p) :=
  (AddMonoidHomClass.isometry_of_norm ((τ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p)
    (fun x => aut_norm τ x)).continuous

def extC {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom ((τ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p) (aut_cont τ)

theorem extC_coe {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    extC τ (x : ℂ_[p]) = ((τ x : PadicAlgCl p) : ℂ_[p]) :=
  UniformSpace.Completion.mapRingHom_coe _ _

theorem extC_norm {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : ℂ_[p]) :
    ‖extC τ y‖ = ‖y‖ := by
  refine UniformSpace.Completion.induction_on y ?_ ?_
  · exact isClosed_eq (continuous_norm.comp UniformSpace.Completion.continuous_map) continuous_norm
  · intro a
    rw [extC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, aut_norm]

theorem phi0_algebraic (D : D7) (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom

end MMConj

open MMConj in

theorem conjugation_extension_inert : ConjExt := by
  intro D p _ _ hj lam
  let L : D.host.E →+* ℂ_[p] := lam.comp (D.host.φ₀.codRestrict Qbar.toSubring (fun z => phi0_algebraic D z))
  have hL : ∀ x, L x = lamC lam (D.host.φ₀ x) := by
    intro x
    simp only [lamC, dif_pos (phi0_algebraic D x)]
    rfl
  set b : D.host.E := D.host.sqd with hbdef
  have hb2 : b ^ 2 = -(D.host.d : D.host.E) := Formalism.BasicNotions.Examples₂.bE_sq D.host
  have hcb : D.host.conj b = -b := Formalism.BasicNotions.Examples₂.conj_bE D.host
  obtain ⟨β, hβ⟩ : ∃ β : PadicAlgCl p, β ^ 2 = -(D.host.d : PadicAlgCl p) := IsAlgClosed.exists_pow_nat_eq _ two_pos
  obtain ⟨τ, hτ⟩ := exists_aut_neg D.host.d p hj β hβ
  refine ⟨extC τ, ?_, extC_norm τ⟩
  have e1 : L b ^ 2 = -(D.host.d : ℂ_[p]) := by rw [← map_pow, hb2, map_neg, map_natCast]
  have e2 : (β : ℂ_[p]) ^ 2 = -(D.host.d : ℂ_[p]) := by
    rw [PadicComplex.coe_eq, ← map_pow, hβ, map_neg, map_natCast]
  have hLb : L b = (β : ℂ_[p]) ∨ L b = -(β : ℂ_[p]) := sq_eq_sq_iff_eq_or_eq_neg.1 (e1.trans e2.symm)
  have hσβ : extC τ (β : ℂ_[p]) = -(β : ℂ_[p]) := by
    rw [extC_coe, hτ, PadicComplex.coe_eq, PadicComplex.coe_eq, map_neg]
  have hσLb : extC τ (L b) = L (D.host.conj b) := by
    rw [hcb, map_neg]
    rcases hLb with h | h
    · rw [h, hσβ]
    · rw [h, map_neg, hσβ, neg_neg]
  let f : D.host.E →ₐ[ℚ] ℂ_[p] := ((extC τ).comp L).toRatAlgHom
  let g : D.host.E →ₐ[ℚ] ℂ_[p] := (L.comp (D.host.conj : D.host.E →+* D.host.E)).toRatAlgHom
  have hfg : b ∈ AlgHom.equalizer f g := hσLb
  have hK : (D.host.K).toSubalgebra ≤ AlgHom.equalizer f g := by
    have hK' : D.host.K = IntermediateField.adjoin ℚ {b} := rfl
    rw [hK', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic b)]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hfg)
  intro x
  rw [← hL, ← hL]
  exact hK x.2

end Formalism.L2.KerInert
