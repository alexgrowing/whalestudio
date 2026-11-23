import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryPlaceSplit

theorem mix_mul {S A : Type} [CommRing S] [Ring A] [Algebra S A] {e : S} (he : e * e = e) (x y z w : A) :
    (e • x + (1 - e) • y) * (e • z + (1 - e) • w) = e • (x * z) + (1 - e) • (y * w) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h0, sub_zero]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, zero_smul, add_zero,
    zero_add]

variable {F : Type} [Field F] [NumberField F]

def idemAt (v : Pl F) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

theorem evFin_idemAt (v : Pl F) : evFin F v (idemAt v) = 1 := evalV_singleFin_self v 1

theorem idemAt_mul_self (v : Pl F) : idemAt v * idemAt v = idemAt v := by
  refine Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero 0) ?_
  change singleFin v 1 * singleFin v 1 = singleFin v 1
  rw [← singleFin_mul, one_mul]

theorem mul_idemAt_of_evFin (v : Pl F) {u : AF F} (hu : evFin F v u = 0) : u * idemAt v = 0 := by
  refine Prod.ext (show u.1 * (0 : Ainf F) = 0 from mul_zero _) ?_
  change u.2 * singleFin v 1 = 0
  refine af_ext fun w => ?_
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    have : evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [evalV_singleFin_ne h, mul_zero]

end GlobalTheory.UnitaryPlaceSplit

end

namespace GlobalTheory.UnitaryPlaceSplit

open Matrix

theorem exists_split_at (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J) :
    ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
      ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  have hee : idemAt v * idemAt v = idemAt v := idemAt_mul_self v
  set e : AF F := idemAt v with he_def
  set G : Matrix (Fin n) (Fin n) (AE F E) := ((g.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
    with hG
  set Gi : Matrix (Fin n) (Fin n) (AE F E) :=
    ((g.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hGi
  have hGGi : G * Gi = 1 := Units.mul_inv g.1
  have hGiG : Gi * G = 1 := Units.inv_mul g.1
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  set M : Matrix (Fin n) (Fin n) (AE F E) := e • G + (1 - e) • 1 with hM
  set N : Matrix (Fin n) (Fin n) (AE F E) := e • Gi + (1 - e) • 1 with hN
  have hMN : M * N = 1 := by rw [hM, hN, mix_mul hee, hGGi, mul_one, ← split]
  have hNM : N * M = 1 := by rw [hM, hN, mix_mul hee, hGiG, mul_one, ← split]
  let g1gl : GL (Fin n) (AE F E) := ⟨M, N, hMN, hNM⟩
  have hmem : g1gl ∈ UG (cA σ) (incM F J) := by
    change Mᵀ * incM F J * M.map (cA σ) = incM F J
    have hg : Gᵀ * incM F J * G.map (cA σ) = incM F J := g.2
    have hT : Mᵀ = e • Gᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [hM, transpose_add, transpose_smul, transpose_smul, transpose_one]
    have hc : M.map (cA σ) = e • G.map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← AlgHom.mapMatrix_apply, hM, map_add, map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
    rw [hT, hc, split (incM F J), mix_mul hee, mix_mul hee, hg, one_mul, mul_one]
  let g₁ : UA σ J := ⟨g1gl, hmem⟩
  have hm1 : mat g₁ - 1 = e • (G - 1) := by
    change M - 1 = _
    rw [hM, smul_sub, sub_smul, one_smul]
    abel
  have hm2 : mat (g₁⁻¹ * g) - 1 = (1 - e) • (G - 1) := by
    change N * G - 1 = _
    conv_lhs => rw [split G]
    rw [hN, mix_mul hee, hGiG, one_mul, smul_sub, sub_smul (1 : AF F) e (1 : Matrix (Fin n) (Fin n) (AE F E)), one_smul]
    abel
  refine ⟨g₁, g₁⁻¹ * g, (mul_inv_cancel_left g₁ g).symm, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hm1, smul_smul, mul_idemAt_of_evFin v hu, zero_smul]
  · have h1 : (1 - e) • u = 0 := hu (1 - e) (by rw [map_sub, map_one, he_def, evFin_idemAt, sub_self])
    rw [hm2, smul_smul, mul_comm, ← smul_eq_mul, h1, zero_smul]

end GlobalTheory.UnitaryPlaceSplit
