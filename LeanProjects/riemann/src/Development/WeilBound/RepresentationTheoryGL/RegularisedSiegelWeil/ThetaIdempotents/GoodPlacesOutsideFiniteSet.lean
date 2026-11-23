import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.ConjUnitIdeleAt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.Jp

theorem PositivityTheory.Rg.Rsw.exists_tau {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    (σ : E →ₐ[F] E) (π : Fv F v ⊗[F] E ≃ₐ[Fv F v] Fv F v × Fv F v) (hs : ∀ y, π (sigR (Fv F v) σ y) = (π y).swap) :
    ∃ τ : E →ₐ[F] Fv F v, (∀ y, splitProj τ y = (π y).1) ∧ ∀ y, splitProj (τ.comp σ) y = (π y).2 := by
  let τ : E →ₐ[F] Fv F v :=
    ((AlgHom.fst (Fv F v) (Fv F v) (Fv F v)).restrictScalars F).comp
      (((π : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v × Fv F v).restrictScalars F).comp
        Algebra.TensorProduct.includeRight)
  have hτ : ∀ x, τ x = (π ((1 : Fv F v) ⊗ₜ[F] x)).1 := fun x => rfl
  have hx : ∀ x, (π ((1 : Fv F v) ⊗ₜ[F] σ x)).1 = (π ((1 : Fv F v) ⊗ₜ[F] x)).2 := by
    intro x
    have h0 := congrArg Prod.fst (hs ((1 : Fv F v) ⊗ₜ[F] x))
    simpa [sigR] using h0
  have e : ∀ (a : Fv F v) (x : E), (a ⊗ₜ[F] x : Fv F v ⊗[F] E) = a • ((1 : Fv F v) ⊗ₜ[F] x) := by
    intro a x
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨τ, fun y => ?_, fun y => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [splitProj, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
      rw [e a x, map_smul, Prod.smul_fst, smul_eq_mul, hτ]
    | add y z hy hz => simp only [map_add, Prod.fst_add, hy, hz]
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [splitProj, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply]
      rw [e a x, map_smul, Prod.smul_snd, smul_eq_mul, hτ, hx]
    | add y z hy hz => simp only [map_add, Prod.snd_add, hy, hz]

set_option maxHeartbeats 1000000 in
theorem PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound : GoodPlacesOutsideFiniteSet := by
  intro D r ψ hψ χ hχ hr S
  obtain ⟨v, hvS, P, hP1, hP2, hP3⟩ := PositivityTheory.Rg.Rsw.L.LJPos.placeEx D ψ hψ χ hχ r hr S
  obtain ⟨τ, hτ1, hτ2⟩ := PositivityTheory.Rg.Rsw.exists_tau v D.sp.cm.sig P.π P.swap
  refine ⟨v, hvS, ⟨fun a ha => ?_, fun ϖ hϖ => ?_⟩, τ, fun a hnorm => ?_⟩
  · have h := (hP1 a).2 ha 1 (one_mem _)
    rwa [mul_one] at h
  · have hne : (ϖ : Fv D.host.F v) ≠ 0 := by
      intro h0
      apply hϖ.ne_zero
      exact Subtype.ext h0
    have hnot : (ϖ : Fv D.host.F v)⁻¹ ∉ v.adicCompletionIntegers D.host.F := by
      intro hin
      apply hϖ.not_isUnit
      refine isUnit_iff_exists_inv.2 ⟨⟨_, hin⟩, Subtype.ext ?_⟩
      simp [mul_inv_cancel₀ hne]
    have h := (hP1 (ϖ : Fv D.host.F v)⁻¹).not.2 hnot
    push Not at h
    obtain ⟨b, hb, hb1⟩ := h
    refine ⟨⟨b, hb⟩, ?_⟩
    rwa [div_eq_inv_mul]
  · rw [hτ1, hτ2] at hnorm
    have hprod : P.π (a : Fv D.host.F v ⊗[D.host.F] D.host.E) *
        P.π ((a⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h1 : (P.π a).1 * (P.π ((a⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : _)).1 = 1 := by
      have := congrArg Prod.fst hprod
      rwa [Prod.fst_mul, Prod.fst_one] at this
    have h2 : (P.π a).2 * (P.π ((a⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : _)).2 = 1 := by
      have := congrArg Prod.snd hprod
      rwa [Prod.snd_mul, Prod.snd_one] at this
    have hα : (P.π a).1 ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hβ : (P.π a).2 ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have hn : ‖(P.π a).1‖₊ = ‖(P.π a).2‖₊ := by
      apply NNReal.eq
      rw [coe_nnnorm, coe_nnnorm]
      exact hnorm
    have hq1 : (P.π a).1 / (P.π a).2 ∈ v.adicCompletionIntegers D.host.F :=
      nnnorm_le_one_iff_mem.1 (le_of_eq (by rw [nnnorm_div, hn, div_self (nnnorm_ne_zero_iff.2 hβ)]))
    have hq2 : (P.π a).2 / (P.π a).1 ∈ v.adicCompletionIntegers D.host.F :=
      nnnorm_le_one_iff_mem.1 (le_of_eq (by rw [nnnorm_div, hn, div_self (nnnorm_ne_zero_iff.2 hβ)]))
    let u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ :=
      { val := P.π.symm ((P.π a).1 / (P.π a).2, 1)
        inv := P.π.symm ((P.π a).2 / (P.π a).1, 1)
        val_inv := by
          rw [← map_mul, Prod.mk_mul_mk, div_mul_div_comm, mul_comm ((P.π a).1), div_self (mul_ne_zero hβ hα),
            mul_one, Prod.mk_one_one, map_one]
        inv_val := by
          rw [← map_mul, Prod.mk_mul_mk, div_mul_div_comm, mul_comm ((P.π a).2), div_self (mul_ne_zero hα hβ),
            mul_one, Prod.mk_one_one, map_one] }
    have hu : P.π (u : Fv D.host.F v ⊗[D.host.F] D.host.E) = ((P.π a).1 / (P.π a).2, 1) :=
      P.π.apply_symm_apply _
    have hu' : P.π ((u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) =
        ((P.π a).2 / (P.π a).1, 1) :=
      P.π.apply_symm_apply _
    have hχu : χ (ideleAt D.host.F D.host.E v u) = 1 := by
      refine hP2 u ?_ ?_ ?_
      · rw [hu]
        exact hq1
      · rw [hu']
        exact hq2
      · rw [hu]
    have hχw : χ (ideleAt D.host.F D.host.E v (u⁻¹ * a)) = 1 := by
      refine hP3 _ ?_
      rw [Units.val_mul, map_mul, hu', Prod.fst_mul, Prod.snd_mul, div_mul_cancel₀ _ hα, one_mul]
    rw [← mul_inv_cancel_left u a, map_mul, map_mul, hχu, hχw, mul_one]

end
