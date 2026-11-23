import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingFormsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeFr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeKerLat

theorem ex_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (n : ℕ) (w : Fin g → ℂ) :
    F.ex i P (n • w) = F.ex i P w ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have := (F.ex_ker i P hP 0).2 (zero_mem _)
    exact this
  | succ n ih => rw [succ_nsmul, F.ex_add i P hP, ih, pow_succ]

theorem exists_lift_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ)) (p : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom (F.u i P) ⟶ pullback Xo.univ.t.G.hom (F.u j P')) (ψp : (Over.mk (F.u i P) ⟶ Xo.univ.t.G) →* (Over.mk (F.u j P') ⟶ Xo.univ.t.G)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di j) ty P' → p.Prime → (∀ a ∈ C, a ^ p ^ 2 = 1) → Formalism.L2.Pj.IsHkIsog p (F.u i P) (F.u j P') C ψ ψp →
  ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
    (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧ (∀ z, F.ex j P' (h z) = ψp (F.ex i P z)) ∧
    (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ ∃ b, gam a = (p ^ 2) • b) ∧
    ∀ c ∈ C, ∃ a, c = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) := by
  intro E _ _ _ H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms E H Dw l Xo σ g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  have hker : ψp.ker = C := hI.2.2.2.2.2.1
  have hp0 : ((p : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨gam, h, h1, h2, h3, h4, fun a => ?_, fun c hc => ?_⟩
  · rw [← hker, MonoidHom.mem_ker, ← h4, map_smul, ← h2, F.ex_ker j P' hP']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hP'.2.1 ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [mul_inv_cancel₀ hp0, one_smul]
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rw [hb, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ hp0, one_smul]
  · obtain ⟨w, rfl⟩ := F.ex_onto i P hP c
    have e1 : F.ex i P ((p ^ 2) • w) = 1 := by rw [ex_nsmul F i P hP, hC _ hc]
    obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 e1
    refine ⟨a, congrArg _ ?_⟩
    rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hp0, one_smul]

end GlobalTheory.HeckeKerLat
