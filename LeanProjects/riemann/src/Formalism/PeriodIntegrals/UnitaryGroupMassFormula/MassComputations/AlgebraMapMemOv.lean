import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactOhat

noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Crd

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

def crd (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) : Fin (Module.finrank F E) → R :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun z

theorem crd_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (z : R ⊗[F] E) (k : Fin (Module.finrank F E)) : crd R' (tensMap (E := E) φ z) k = φ (crd R z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, tensMap, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add] at *
    simp only [crd, map_add, Pi.add_apply] at *
    rw [hx, hy]

def Bint (n : ℕ) : Set (Fin n → E) :=
  {x | ∀ i k, IsIntegral ℤ ((Module.finBasis F E).repr (x i) k)}

theorem algebraMap_mem_Ov (v : HeightOneSpectrum (𝓞 F)) {c : F} (hc : IsIntegral ℤ c) :
    algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, rfl⟩ : ∃ x : 𝓞 F, (x : F) = c := ⟨⟨c, hc⟩, rfl⟩
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v x

theorem crd_mem_of_latLoc {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v (Bint (F := F) n)) (i : Fin n) (k : Fin (Module.finrank F E)) :
    crd (Fv F v) (y i) k ∈ v.adicCompletionIntegers F := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have h := algebraMap_mem_Ov v (hx i k)
    simpa [crd, ratV, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.one_def] using h
  | zero => simp [crd]
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, crd, map_add] at ha hb ⊢
    exact add_mem ha hb
  | smul c a _ ha =>
    simp only [crd] at ha ⊢
    have e : (c • a) i = (c : Fv F v) • a i := rfl
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem c.2 ha

end Crd

end MassDataMassesW.KCptW
