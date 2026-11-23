import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisEqEmbeddingsOCModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfPerfectOfDvdSubAdicSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveMapIntegersClToWittQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorMapBreuilKisinEvEqStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_galK_fixFlat_of_tilt_maps_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type)
    [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O),
    ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    ∀ ψ' : OCb l →+* O, (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∃ g : ↥(GK K), bk.FixFlat g ∧ ∀ y, ψ' y = ψ (Per.σF (g : GQ l) y) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc ψ' hs
  have hflat : ψ' bk.flat = ψ bk.flat := by
    have h := hs X
    rw [bk.ev_X, WittVector.teichmuller_coeff_zero] at h
    exact h.symm
  have hW := GlobalTheory.T.wittVector_map_breuilKisin_ev_eq l K bk O ψ ψ' h0 hc hs
  obtain ⟨θ₁, hθ₁, hinj₁, hdom, hdiv⟩ := GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc
  obtain ⟨θ₂', hθ₂', hinj₂', -, -⟩ :=
    GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ' (hflat ▸ h0) (hflat ▸ hu) (hflat ▸ hc)
  have hI : Ideal.span {WittVector.map ψ' (bk.ev bk.E)} = Ideal.span {WittVector.map ψ (bk.ev bk.E)} := by
    rw [hW bk.E]
  let θ₂ := (Ideal.quotEquivOfEq hI).toRingHom.comp θ₂'
  have hθ₂ : ∀ a : Ainf l, θ₂ (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ' a) := by
    intro a
    simp only [θ₂, RingHom.comp_apply, hθ₂' a, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      Ideal.quotEquivOfEq_mk]
  have hinj₂ : Function.Injective θ₂ := (Ideal.quotEquivOfEq hI).injective.comp hinj₂'
  haveI := hdom
  have hK : ∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r) := by
    intro r
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (bk.str r)
    rw [← bk.θ_ev r x hx, hθ₁, hθ₂, hW x]
  obtain ⟨g, halg, hl⟩ := GlobalTheory.T.exists_galois_eq_embeddings_OC_mod_prime l K _ θ₁ θ₂ hinj₁ hinj₂ hK
  obtain ⟨hroot, hfix⟩ := GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk

  have key : ∀ z : OCb l, ψ z = ψ' z →
      ψ ((frobeniusEquiv (OCb l) l).symm z) = ψ' ((frobeniusEquiv (OCb l) l).symm z) := by
    intro z hz
    apply frobenius_inj O l
    rw [← RingHom.map_frobenius, ← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, hz]
  have hiter : ∀ n : ℕ, ψ (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) =
      ψ' (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) := by
    intro n
    induction n with
    | zero => exact hflat.symm
    | succ n ih => rw [Function.iterate_succ_apply']; exact key _ ih
  have hθroot : ∀ n : ℕ, θ₁ (GlobalTheory.MemLoc.rootT bk.flat n) = θ₂ (GlobalTheory.MemLoc.rootT bk.flat n) := by
    intro n
    have e : GlobalTheory.MemLoc.rootT bk.flat n =
        Per.θ l (WittVector.teichmuller l (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat)) := by
      rw [GlobalTheory.MemLoc.rootT, WittVector.fontaineTheta_teichmuller]
    rw [e, hθ₁, hθ₂, WittVector.map_teichmuller, WittVector.map_teichmuller, hiter n]
  refine ⟨g, ?_, ?_⟩
  · refine hfix (g : GQ l) bk.flat fun n => ?_
    obtain ⟨z, hz⟩ := hroot n
    have h := halg _ ⟨z, hz⟩
    rw [← hθroot n] at h
    exact (hinj₁ h).symm
  · have hext := GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated l (OCb l) O (ψ bk.flat) bk.Ep.natDegree bk.deg_pos hc.toIsHausdorff
      ψ' (ψ.comp (Per.σF (g : GQ l))) fun y => ?_
    · intro y
      exact RingHom.congr_fun hext y
    · have hmk := hl (Per.θ l (WittVector.teichmuller l y))
      rw [← GlobalTheory.RingBasics.θ_σA, hθ₁, hθ₂] at hmk
      have e2 : Per.σA (g : GQ l) (WittVector.teichmuller l y) =
          WittVector.teichmuller l (Per.σF (g : GQ l) y) := by
        exact GlobalTheory.RingIface.sigA_teich l (g : GQ l) y
      rw [e2, WittVector.map_teichmuller, WittVector.map_teichmuller, ← map_sub] at hmk
      have h := hdiv _ hmk
      rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
        WittVector.teichmuller_coeff_zero] at h
      simpa [RingHom.comp_apply] using h

end GlobalTheory.BSP
