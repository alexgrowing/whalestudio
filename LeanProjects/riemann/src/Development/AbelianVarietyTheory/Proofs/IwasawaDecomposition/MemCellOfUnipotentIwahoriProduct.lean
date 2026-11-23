import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationEqUniformizer
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IwaCell

namespace GlobalTheory.IwaCell

theorem right_translate_mem_cell (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ) (hϖ : ord k ϖ = 1) (b d : Fin m → ℤ) (hd : Monotone d) (g : GL (Fin m) k)
    (hg : ∃ u ∈ unipB k (Fin m), ∃ i ∈ iwahori k (Fin m), g * tD ϖ d = u * tD ϖ (b + d) * i) :
    g ∈ cell ϖ b := by
  obtain ⟨u, hu, i, hi, e⟩ := hg
  obtain ⟨n, hn, c, hc, l, hl, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hi
  have hl' := GlobalTheory.IwaStep.conj_mem_unipLowerOne hϖ hd hl
  have hnB : tD ϖ d * n * (tD ϖ d)⁻¹ ∈ unipB k (Fin m) := GlobalTheory.IwahoriTraceProof.conj_mem_unipB _ hn.1
  have hnB' : tD ϖ b * (tD ϖ d * n * (tD ϖ d)⁻¹) * (tD ϖ b)⁻¹ ∈ unipB k (Fin m) :=
    GlobalTheory.IwahoriTraceProof.conj_mem_unipB _ hnB
  have hK : diagT k (Fin m) c * (tD ϖ d * l * (tD ϖ d)⁻¹) ∈ KO k (Fin m) :=
    iwahori_le_KO k (Fin m) (mul_mem (diagT_mem_iwahori hc) (KOne_le_iwahori k (Fin m) hl'.2))
  have hcomm : tD ϖ d * diagT k (Fin m) c = diagT k (Fin m) c * tD ϖ d := by
    rw [tD, ← map_mul, ← map_mul, mul_comm]
  have hg : g = (u * (tD ϖ b * (tD ϖ d * n * (tD ϖ d)⁻¹) * (tD ϖ b)⁻¹)) * tD ϖ b *
      (diagT k (Fin m) c * (tD ϖ d * l * (tD ϖ d)⁻¹)) := by
    have e2 : g = u * tD ϖ (b + d) * (n * diagT k (Fin m) c * l) * (tD ϖ d)⁻¹ := by
      rw [← e]; group
    rw [e2, tD_add]
    have h3 : (tD ϖ d)⁻¹ * diagT k (Fin m) c * tD ϖ d = diagT k (Fin m) c := by
      rw [mul_assoc, ← hcomm]; group
    calc u * (tD ϖ b * tD ϖ d) * (n * diagT k (Fin m) c * l) * (tD ϖ d)⁻¹
        = u * (tD ϖ b * tD ϖ d) * (n * ((tD ϖ d)⁻¹ * diagT k (Fin m) c * tD ϖ d) * l) * (tD ϖ d)⁻¹ := by rw [h3]
      _ = _ := by group
  rw [hg]
  exact mul_mem_cell (mul_mem hu hnB') hK

example : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ (b d : Fin m → ℤ), Monotone d → ∀ g : GL (Fin m) k, (∃ u ∈ unipB k (Fin m), ∃ i ∈ iwahori k (Fin m), g * tD ϖ d = u * tD ϖ (b + d) * i) → g ∈ cell ϖ b := right_translate_mem_cell

end GlobalTheory.IwaCell
