import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepI
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepM

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem form_eq_zero_of_self {M : Type} [AddCommGroup M] [Module ℂ M] {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hh : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (hp : ∀ x, 0 ≤ (B x x).re) {z : M} (hz : B z z = 0)
    (x : M) : B z x = 0 := by
  by_contra ha
  have hn : 0 < Complex.normSq (B z x) := Complex.normSq_pos.2 ha
  have hxz : B x z = (starRingEnd ℂ) (B z x) := (hh z x).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B z x) = (B x x).re + 1 :=
    ⟨((B x x).re + 1) / (2 * Complex.normSq (B z x)), by field_simp⟩
  have key := hp (x + ((-(t : ℂ)) * B z x) • z)
  have e1 : B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z) =
      B x x + (-(t : ℂ)) * B z x * (starRingEnd ℂ) (B z x) +
        (starRingEnd ℂ) (-(t : ℂ) * B z x) * B z x := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, hz, hxz]
    ring
  have e2 : (B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z)).re =
      (B x x).re - 2 * t * Complex.normSq (B z x) := by
    rw [e1]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg,
      Complex.conj_ofReal, Complex.normSq_apply]
    ring
  linarith

theorem circle_conj_mul (z : Circle) : (starRingEnd ℂ) (z : ℂ) * z = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

theorem conj_mul_self_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem conj_psi (c : k) : (starRingEnd ℂ) ((ψ c : Circle) : ℂ) = ((ψ⁻¹ c : Circle) : ℂ) := by
  rw [AddChar.inv_apply', Circle.coe_inv_eq_conj]

theorem superDiag_inv {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : superDiag u⁻¹ = -superDiag u := by
  have h := superDiag_mul ((unipB k (Fin m)).inv_mem hu) hu
  rw [inv_mul_cancel, superDiag_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem superDiag_conj {u n : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (hn : n ∈ unipB k (Fin m)) :
    superDiag (u⁻¹ * n * u) = superDiag n := by
  have hu' := (unipB k (Fin m)).inv_mem hu
  rw [superDiag_mul ((unipB k (Fin m)).mul_mem hu' hn) hu, superDiag_mul hu' hn, superDiag_inv hu]
  ring

theorem delta_one {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : (delta ψ K : GL (Fin m) k → ℂ) 1 = 1 := by
  have := delta_mul hK (unipB k (Fin m)).one_mem K.one_mem
  rw [mul_one, superDiag_one, AddChar.map_zero_eq_one, Circle.coe_one] at this
  exact this

theorem delta_ne_zero {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : delta ψ K ≠ 0 := fun h => by
  have := delta_one hK
  rw [h] at this
  exact zero_ne_one this

theorem delta_eq_of_le {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (g : GL (Fin m) k) (hg : (delta ψ K' : GL (Fin m) k → ℂ) g ≠ 0) :
    (delta ψ K : GL (Fin m) k → ℂ) g = (delta ψ K' : GL (Fin m) k → ℂ) g := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K', g = u * κ := by
    by_contra h
    exact hg (delta_eq_zero h)
  rw [delta_mul hK hu (hle hκ), delta_mul hK' hu hκ]

theorem good_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) : Good ψ (K.map (MulAut.conj u).toMonoidHom) := by
  have e : ((K.map (MulAut.conj u).toMonoidHom : Subgroup (GL (Fin m) k)) : Set (GL (Fin m) k)) =
      (fun y => u⁻¹ * y * u) ⁻¹' K := Set.ext fun _ => mem_conj
  have hc : Continuous fun κ : GL (Fin m) k => u * κ * u⁻¹ := by fun_prop
  refine ⟨?_, ?_, fun n hn hnK => ?_⟩
  · rw [e]
    exact hK.1.preimage (by fun_prop)
  · rw [Subgroup.coe_map]
    exact hK.2.1.image hc
  · rw [← superDiag_conj hu hn]
    exact hK.2.2 _ ((unipB k (Fin m)).mul_mem ((unipB k (Fin m)).mul_mem
      ((unipB k (Fin m)).inv_mem hu) hn) hu) (mem_conj.1 hnK)

end DiscreteGroups.sglob.LConv

end
