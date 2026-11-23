import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.EpsEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.rep_star :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ y, P.rep (G.frame.star O B n y) = (P.rep y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P y
  have sb := star_basic G.frame n O B
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
      Algebra.algebraMap_self, RingHom.mapMatrix_id]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero =>
    have h0 : G.frame.star O B n 0 = 0 := by simpa using sb.2.2.2.2.2.1 0 0
    rw [h0, map_zero, Matrix.transpose_zero]
  | add p q hp hq => rw [sb.2.2.1, map_add, map_add, hp, hq, Matrix.transpose_add]
  | single g b =>
    rw [sb.2.2.2.2.2.2 g b]
    obtain ⟨he, hc⟩ := eps_eq P g
    have hform := x.form (h.p₀ g)
    rw [Units.val_one, mul_one] at hform
    have hci : mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hT : (mat x.ρ (h.p₀ g))ᵀ =
        ((G0.frame.eps ℤ_[l] (PowerSeries x.K) (h.p₀ g) ^ (1 - (n : ℤ)) : (PowerSeries x.K)ˣ) : PowerSeries x.K) •
          mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ := by
      calc (mat x.ρ (h.p₀ g))ᵀ
          = (mat x.ρ (h.p₀ g))ᵀ * (mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹) := by
            rw [hci, mul_one]
        _ = _ := by rw [← mul_assoc, hform, Matrix.smul_mul, one_mul]
    have hu : Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g) = G0.frame.eps ℤ_[l] x.A (h.p₀ g) :=
      Units.ext he
    have hfu : P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B) =
        ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) ^ (1 - (n : ℤ)) : (x.A)ˣ) : x.A) := by
      calc P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B)
          = ((Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g ^ (1 - (n : ℤ))) : (x.A)ˣ) : x.A) := rfl
        _ = _ := by rw [map_zpow, hu]
    rw [hrep, hrep, Matrix.transpose_smul, map_mul, hfu, hT, map_inv, hc, mul_smul]
