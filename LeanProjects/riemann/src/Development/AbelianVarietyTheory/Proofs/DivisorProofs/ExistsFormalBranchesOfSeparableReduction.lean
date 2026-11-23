import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparableStatement
open Filter Topology

namespace GlobalTheory.ShiftHomomorphism

noncomputable def shiftHom (D : ℕ) (c : Fin D → ℂ) :
    MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPowerSeries (Fin D) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.X i + MvPowerSeries.C (c i))

theorem shiftHom_X (D : ℕ) (c : Fin D → ℂ) (i : Fin D) :
    shiftHom D c (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  simp [shiftHom]

theorem constantCoeff_comp_shiftHom (D : ℕ) (c : Fin D → ℂ) :
    (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)).comp (shiftHom D c).toRingHom
      = MvPolynomial.eval c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [shiftHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C, MvPolynomial.eval_C]
    first | rfl | simp [MvPowerSeries.algebraMap_apply] | simp [Algebra.algebraMap_eq_smul_one]
  · intro i; simp [shiftHom]

theorem shiftHom_injective (D : ℕ) (c : Fin D → ℂ) : Function.Injective (shiftHom D c) := by
  let τ : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (c i))
  let τ' : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (c i))
  have hinv : τ'.comp τ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext; intro i; simp [τ, τ']
  have hτ : Function.Injective τ := by
    intro a b h
    have := congrArg τ' h
    simpa [← AlgHom.comp_apply, hinv] using this
  have hfac : shiftHom D c = (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp τ := by
    apply MvPolynomial.algHom_ext; intro i; simp [shiftHom, τ]
  rw [hfac]
  exact (MvPolynomial.coe_injective _ _).comp hτ

end GlobalTheory.ShiftHomomorphism

namespace GlobalTheory

open GlobalTheory.ShiftHomomorphism in

theorem branches_of_unramified_point : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  intro D P c hP hsep
  haveI : IsDomain (MvPowerSeries (Fin D) ℂ) := NoZeroDivisors.to_isDomain _
  set ψ := shiftHom D c with hψ
  set Q := P.map ψ.toRingHom with hQ
  have hQm : Q.Monic := hP.map _
  have hred : Q.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)) = P.map (MvPolynomial.eval c) := by
    rw [hQ, Polynomial.map_map, constantCoeff_comp_shiftHom]
  obtain ⟨θ, hθi, hθr⟩ := GlobalTheory.T.exists_lifts_of_separable_reduction D Q hQm (by rw [hred]; exact hsep)
  have hroot : ∀ j, P.eval₂ ψ.toRingHom (θ j) = 0 := by
    intro j
    have := hθr j
    rw [Polynomial.IsRoot.def, hQ, Polynomial.eval_map] at this
    exact this
  refine ⟨Q.natDegree, fun j => AdjoinRoot.liftAlgHom P ψ (θ j) (hroot j), ?_, ?_⟩
  · intro u hu
    obtain ⟨R, rfl⟩ := AdjoinRoot.mk_surjective u
    have hR : AdjoinRoot.mk P R = AdjoinRoot.mk P (R %ₘ P) := by
      rw [← AdjoinRoot.modByMonicHom_mk hP R, AdjoinRoot.mk_leftInverse hP]
    rw [hR] at hu ⊢
    by_contra hne
    have hR0 : R %ₘ P ≠ 0 := by
      intro h; apply hne; rw [h, map_zero]
    have hdeg : (R %ₘ P).natDegree < P.natDegree :=
      Polynomial.natDegree_lt_natDegree hR0 (Polynomial.degree_modByMonic_lt R hP)
    have hz : (R %ₘ P).map ψ.toRingHom = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hθi ?_ ?_
      · intro j
        have := hu j
        simpa [AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, Polynomial.eval_map] using this
      · calc ((R %ₘ P).map ψ.toRingHom).natDegree ≤ (R %ₘ P).natDegree := Polynomial.natDegree_map_le
          _ < P.natDegree := hdeg
          _ = Q.natDegree := (hP.natDegree_map _).symm
          _ = Fintype.card (Fin Q.natDegree) := (Fintype.card_fin _).symm
    apply hR0
    exact Polynomial.map_injective _ (shiftHom_injective D c) (by rw [hz, Polynomial.map_zero])
  · intro j i
    simp [AdjoinRoot.liftAlgHom]
    rw [hψ]; exact shiftHom_X D c i

end GlobalTheory
