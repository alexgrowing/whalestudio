import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatAnn

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def incInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem inf_mul (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * z = incInf D (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    show _ = incInf D (fstA D.host.F a ⊗ₜ[D.host.F] e)
    have : pairA D.host.F 1 0 * a = (fstA D.host.F a, (0 : Af D.host.F)) :=
      Prod.ext (by show (1 : Ainf D.host.F) * a.1 = a.1; rw [one_mul]) (by show (0 : Af D.host.F) * a.2 = 0; rw [zero_mul])
    rw [this]; rfl
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]

theorem finite_idempotent_mul_eq (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * z = jF D (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, finPart_tmul, jF_tmul]
    congr 1
    exact Prod.ext (by show (0 : Ainf D.host.F) * a.1 = 0; rw [zero_mul]) (by show (1 : Af D.host.F) * a.2 = a.2; rw [one_mul])
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]

theorem eq_jF_of_inf (z : AE D) (hz : infPart D z = 0) : z = jF D (finPart D z) := by
  have h1 : pairA D.host.F 1 0 + pairA D.host.F 0 1 = (1 : AF D.host.F) := Prod.ext (add_zero _) (zero_add _)
  calc z = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0 + pairA D.host.F 0 1) * z := by rw [h1, map_one, one_mul]
    _ = jF D (finPart D z) := by rw [map_add, add_mul, inf_mul, hz, map_zero, zero_add, finite_idempotent_mul_eq]

theorem finPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (jF D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [jF_tmul, finPart_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem infPart_jF (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (jF D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    rw [jF_tmul]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 a ⊗ₜ[D.host.F] e) = 0
    rw [Algebra.TensorProduct.map_tmul]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    rw [TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem approx_Af (a : Af D.host.F) (N : ℕ) (hN : 0 < N) :
    ∃ f : D.host.F, ∃ c ∈ intAf D.host.F, a = algebraMap D.host.F (Af D.host.F) f + algebraMap D.host.F (Af D.host.F) N * c := by
  have hNF : (N : D.host.F) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨u, hu⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx_adele (R := 𝓞 D.host.F)
    (algebraMap D.host.F (Af D.host.F) (1 / (N : D.host.F)) * a)
  refine ⟨N * u, _, intAf_of_isInt _ hu, ?_⟩
  rw [mul_sub, ← mul_assoc, ← map_mul, mul_one_div_cancel hNF, map_one, one_mul, ← map_mul]
  ring

theorem isAlg_Z (e : D.host.E) : IsAlgebraic ℤ e :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic e)

set_option maxHeartbeats 1600000 in

theorem approx_AfE (N : ℕ) (hN : 0 < N) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : D.host.E, ∃ y ∈ intAE D, z = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by rw [TensorProduct.tmul_zero, smul_zero, add_zero]⟩
  | tmul a e =>
    obtain ⟨m, hm0, hmint⟩ := IsAlgebraic.exists_integral_multiple (isAlg_Z e)
    have hmF : ((m : ℤ) : D.host.F) ≠ 0 := by exact_mod_cast hm0
    let e' : 𝓞 D.host.E := ⟨m • e, hmint⟩
    have he : e = (1 / (m : D.host.F)) • (e' : D.host.E) := by
      show e = (1 / (m : D.host.F)) • (m • e)
      rw [zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap D.host.F D.host.E), ← map_mul,
        one_div_mul_cancel hmF, map_one, one_mul]
    obtain ⟨f, c, hc, hfc⟩ := approx_Af ((1 / (m : D.host.F)) • a) N hN
    refine ⟨f • (e' : D.host.E), c ⊗ₜ[D.host.F] (e' : D.host.E), AddSubgroup.subset_closure ⟨c, hc, e', rfl⟩, ?_⟩
    have hN' : algebraMap D.host.F (Af D.host.F) (N : D.host.F) * c = N • c := by
      rw [map_natCast, nsmul_eq_mul]
    rw [he, ← TensorProduct.smul_tmul, hfc, TensorProduct.add_tmul, hN', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨w, y1, hy1, rfl⟩ := hx
    obtain ⟨w', y2, hy2, rfl⟩ := hy
    exact ⟨w + w', y1 + y2, add_mem hy1 hy2, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end Formalism.IndefR.Fin

end
