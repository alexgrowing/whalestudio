import Mathlib
import Formalism.PeriodIntegrals.SelfDualBridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.AdditiveCharacterNontrivial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.SelfDualBridge.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct

section Transport

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem dualAt_of_equiv {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [AddCommGroup V']
    [TopologicalSpace V'] (e : V ≃+ V') (he : Continuous e) (hes : Continuous e.symm)
    (B : V → V → Fv F v) (B' : V' → V' → Fv F v) (hB : ∀ x y, B x y = B' (e x) (e y))
    (h : DualAt v B') : DualAt v B := by
  unfold DualAt at h ⊢
  obtain ⟨L', hc, ho, hs, hK⟩ := h
  refine ⟨L'.comap e.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · have h1 : ((L'.comap e.toAddMonoidHom : AddSubgroup V) : Set V) = e.symm '' (L' : Set V') := by
      ext x
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h1]
    exact hc.image hes
  · exact ho.preimage he
  · intro s hs' x hx
    obtain ⟨x'', hx'', hB''⟩ := hs s hs' (e x) hx
    refine ⟨e.symm x'', ?_, fun y => ?_⟩
    · show e.toAddMonoidHom (e.symm x'') ∈ L'
      simpa using hx''
    · rw [hB, hB, e.apply_symm_apply, hB'']
  · intro c
    obtain ⟨K', hK'c, hK'⟩ := hK c
    refine ⟨e.symm '' K', hK'c.image hes, fun y hy => ?_⟩
    refine ⟨e y, hK' ?_, e.symm_apply_apply y⟩
    intro x'' hx''
    have h1 := hy (e.symm x'') (by show e.toAddMonoidHom (e.symm x'') ∈ L'; simpa using hx'')
    rwa [hB, e.apply_symm_apply] at h1

end Transport

section Third

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def trP (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) : Fv F v :=
  ∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)

def reTup (ι : Type) [Fintype ι] :
    (ι → Fv F v ⊗[F] E) ≃+ (Fin (Fintype.card ι) → Fin 1 → Fv F v ⊗[F] E) where
  toFun x p _ := x ((Fintype.equivFin ι).symm p)
  invFun X i := X (Fintype.equivFin ι i) 0
  left_inv x := by funext i; simp
  right_inv X := by
    funext p k
    rw [Subsingleton.elim k 0]
    simp
  map_add' _ _ := rfl

theorem reTup_apply (ι : Type) [Fintype ι] (x : ι → Fv F v ⊗[F] E) (p : Fin (Fintype.card ι))
    (k : Fin 1) : reTup v ι x p k = x ((Fintype.equivFin ι).symm p) := rfl

theorem continuous_reTup (ι : Type) [Fintype ι] : Continuous (reTup (E := E) v ι) := by
  refine continuous_pi fun p => continuous_pi fun k => ?_
  simp only [reTup_apply]
  exact continuous_apply _

theorem continuous_reTup_symm (ι : Type) [Fintype ι] : Continuous (reTup (E := E) v ι).symm := by
  refine continuous_pi fun i => ?_
  show Continuous fun X : Fin (Fintype.card ι) → Fin 1 → Fv F v ⊗[F] E => X (Fintype.equivFin ι i) 0
  exact (continuous_apply 0).comp (continuous_apply _)

theorem sigR_id (z : Fv F v ⊗[F] E) : sigR (Fv F v) (AlgHom.id F E) z = z := by
  first
  | simp [sigR]
  | (induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, hx, hy])

theorem JR_one : JR (F := F) (Fv F v) (1 : Matrix (Fin 1) (Fin 1) E) = 1 := by
  simp [JR]

theorem localTracePairing_eq_realBilinearForm (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) :
    trP v ι x y = BR (Fv F v) (AlgHom.id F E) (1 : Matrix (Fin 1) (Fin 1) E)
      (reTup v ι x) (reTup v ι y) := by
  unfold BR trP
  have h1 : ∀ u w : Fin 1 → Fv F v ⊗[F] E, hR (Fv F v) (AlgHom.id F E) 1 u w = u 0 * w 0 := by
    intro u w
    simp [hR, Formalism.UG.hform, sigR_id, JR_one, Fin.sum_univ_one]
  simp only [h1, reTup_apply]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm
    (fun i => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))).symm

theorem localTracePairing_add_left (ι : Type) [Fintype ι] (x x' y : ι → Fv F v ⊗[F] E) :
    trP v ι (x + x') y = trP v ι x y + trP v ι x' y := by
  simp [trP, add_mul, map_add, Finset.sum_add_distrib]

theorem localTracePairing_smul_left (ι : Type) [Fintype ι] (c : Fv F v) (x y : ι → Fv F v ⊗[F] E) :
    trP v ι (c • x) y = c * trP v ι x y := by
  simp [trP, smul_mul_assoc, map_smul, Finset.mul_sum]

theorem localTracePairing_comm (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) :
    trP v ι x y = trP v ι y x := by
  unfold trP
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem continuous_localTracePairing (ι : Type) [Fintype ι] :
    Continuous (fun p : (ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E) => trP v ι p.1 p.2) := by
  have htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) := by
    first
    | exact IsModuleTopology.continuous_of_linearMap _
    | exact LinearMap.continuous_of_finiteDimensional _
  unfold trP
  refine continuous_finset_sum _ fun i _ => htr.comp ?_
  exact ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

theorem dualAt_trP (ι : Type) [Fintype ι] : DualAt v (trP (E := E) v ι) :=
  dualAt_of_equiv v (reTup v ι) (continuous_reTup v ι) (continuous_reTup_symm v ι) _ _
    (localTracePairing_eq_realBilinearForm v ι)
    (dualAt_alt v (Module.finBasis F E) (AlgHom.id F E) (1 : Matrix (Fin 1) (Fin 1) E)
      (nondeg_BR v (AlgHom.id F E) (fun _ => rfl) (1 : Matrix (Fin 1) (Fin 1) E) (by simp)))

theorem sd_trP (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
    (hψn : ∀ r, ‖ψ0 r‖ = 1) (hnt : ∃ y, ψ0 y ≠ 1) (ι : Type) [Fintype ι] :
    ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (fun x y => ψ0 (trP v ι x y)) :=
  exists_selfDual_measure v (trP v ι) ψ0 hψc hψa hψn hnt (localTracePairing_add_left v ι) (localTracePairing_smul_left v ι) (localTracePairing_comm v ι)
    (continuous_localTracePairing v ι) (dualAt_trP v ι)

end Third

theorem sdExists_of_sdEx (h0 : PI.OmFibreUniq.W.SdEx) {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ) (ι : Type) [Fintype ι] :
    PI.SelfDualBridge.SdExists σ J ψ v a ι := by
  intro hS
  obtain ⟨hCM, hJ, hψ, hstd⟩ := hS
  obtain ⟨h1, h2⟩ := h0 σ J ψ v a ⟨hCM, hJ, hψ, hstd⟩
  refine ⟨h1, h2, ?_⟩
  exact sd_trP v (psiV F ψ v) (continuous_psiV ψ hψ.1 v) (psiV_add ψ v) (fun r => hψ.2.1 _)
    (additive_character_nontrivial ψ v hψ hstd hCM.1) ι

end PI.SelfDualBridge.W
