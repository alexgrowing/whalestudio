import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharPStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem finrank_generic_le_special_and_free {R M : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) ≤
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) ∧
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) ≤
        Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) → Module.Free R M) := by
  have e : Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) = Module.finrank R M := by
    rw [IsLocalization.finrank_eq (FractionRing R) (nonZeroDivisors R) le_rfl]
    exact IsLocalizedModule.finrank_eq (nonZeroDivisors R) (TensorProduct.mk R (FractionRing R) M 1)
      le_rfl
  let b := Module.finBasis (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)
  choose v hv using fun i => TensorProduct.mk_surjective R M (IsLocalRing.ResidueField R)
    Ideal.Quotient.mk_surjective (b i)
  have hs := IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  rw [e]
  refine ⟨by simpa using finrank_le_of_span_eq_top hs, fun h => ?_⟩
  exact .of_basis (Module.Basis.mk
    (linearIndependent_of_top_le_span_of_card_le_finrank hs.ge (by simpa using h)) hs.ge)

variable {p : ℕ} {R : Type} [CommRing R]

theorem finite_omega_of_natCast_eq_zero (G : PDivGroup p R) (hp : (p : R) = 0) :
    Module.Finite R G.omega :=
  .equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective hp)).symm

variable [Fact p.Prime]

theorem finrank_omega_eq_of_iso {G H : PDivGroup p R} (e : G ≅ H) :
    Module.finrank R H.omega = Module.finrank R G.omega :=
  (LinearEquiv.ofLinearMap (omegaMap G H e.hom) (omegaMap H G e.inv)
    (by rw [← omegaMap_comp, e.hom_inv_id, omegaMap_id])
    (by rw [← omegaMap_comp, e.inv_hom_id, omegaMap_id])).finrank_eq

theorem finrank_fibre_omega_add (hW : GlobalTheory.Published.BarsottiTateDieudonne.WittModule)
    (G : PDivGroup p R) (hp : (p : R) = 0) (K : Type) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] G.omega) + Module.finrank K (K ⊗[R] G.dual.omega) = G.height := by
  have hp' : (p : K) = 0 := by rw [← map_natCast (algebraMap R K), hp, map_zero]
  rw [(LinearEquiv.ofBijective _ (T.omega_baseChange_bijective_of_p_eq_zero G K hp)).finrank_eq,
    (LinearEquiv.ofBijective _ (T.omega_baseChange_bijective_of_p_eq_zero G.dual K hp)).finrank_eq,
    finrank_omega_eq_of_iso (PerfdLat.dualBaseChange K G)]
  exact (T.dieudonne_ranks_field_char_p hW p K hp' (G.baseChange K)).2.2.1

theorem free_finite_omega_ext_of_isDiscreteValuationRing
    (hW : GlobalTheory.Published.BarsottiTateDieudonne.WittModule) (p : ℕ) [Fact p.Prime] (R : Type)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0) (G : PDivGroup p R) :
    Module.Free R G.omega ∧ Module.Finite R G.omega ∧ Module.Free R G.dual.omega ∧
      Module.Finite R G.dual.omega ∧ Module.Free R G.VecExt ∧ Module.Finite R G.VecExt ∧
      Module.Free R G.RigExt ∧ Module.Finite R G.RigExt := by
  haveI f1 := G.finite_omega_of_natCast_eq_zero h
  haveI f2 := G.dual.finite_omega_of_natCast_eq_zero h
  have k1 := G.finrank_fibre_omega_add hW h (FractionRing R)
  have k2 := G.finrank_fibre_omega_add hW h (IsLocalRing.ResidueField R)
  obtain ⟨a1, a2⟩ := finrank_generic_le_special_and_free (R := R) (M := G.omega)
  obtain ⟨b1, b2⟩ := finrank_generic_le_special_and_free (R := R) (M := G.dual.omega)
  haveI g1 : Module.Free R G.omega := a2 (by omega)
  haveI g2 : Module.Free R G.dual.omega := b2 (by omega)
  let e : G.VecExt ≃ₗ[R] Module.Dual R G.dual.omega :=
    (G.extCharEquiv h).trans (LinearEquiv.ofBijective _ (G.primLie_bijective h))
  haveI g3 : Module.Free R G.VecExt := .of_equiv e.symm
  haveI f3 : Module.Finite R G.VecExt := .equiv e.symm
  obtain ⟨s, hs⟩ := G.rigToExt.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 G.rigToExt_surjective)
  let e' : G.RigExt ≃ₗ[R] G.omega × G.VecExt :=
    (G.exact_rigOfOmega_rigToExt.splitSurjectiveEquiv (G.rigOfOmega_injective_of_eq_zero h)
      ⟨s, hs⟩).1
  exact ⟨g1, f1, g2, f2, g3, f3, .of_equiv e'.symm, .equiv e'.symm⟩

end PDivGroup

end GlobalTheory
