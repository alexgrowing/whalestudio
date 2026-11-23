import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct Topology

namespace GlobalTheory.HeckeSplitGen

theorem integralFiniteAdelesTensor_eq_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAEF F E = GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  unfold intAEF GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_trivial_modSetF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  intro F E _ _ _ _ _ ν hν
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (GlobalTheory.AdLat.RA F E) := ⟨rfl⟩
  haveI : ContinuousAdd (GlobalTheory.AdLat.RA F E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hsmall := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (by simp)).2
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.finite_order_of_small (infPartF F E) (finPartF F E) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (GlobalTheory.CharFin.hatRing F E) hsmall (GlobalTheory.CharFin.finite_quotient_hatRing F E) ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  rw [integralFiniteAdelesTensor_eq_adelicCompletion_integers] at hr h3
  have hNr : (N : Af F ⊗[F] E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPartF F E (x : AEF F E) ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    have : finPartF F E (x : AEF F E) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => one_mem _, _, ⟨1, rfl⟩,
      by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitGen
