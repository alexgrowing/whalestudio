import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviActionLocalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviIsoPlaneUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.JacquetFlagLevi

open GlobalTheory.JacquetLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Levi

variable {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}

theorem levi_mem_UAt (hspan : ∀ z : Fin n → E, ∃ (s r : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + r • H.y)
    {v : Pl F} {t : (AE F E)ˣ} {h₁ : UA σ Y₁.J} {m : UA σ Y.J} (hL : IsLevi (W₁ := Y₁) H t h₁ m)
    (ht : ∀ c : AF F, evFin F v c = 0 → c • ((t : AE F E) - 1) = 0)
    (ht' : ∀ c : AF F, evFin F v c = 0 → c • (((t⁻¹ : (AE F E)ˣ) : AE F E) - 1) = 0)
    (hh : h₁ ∈ UAt σ Y₁ (evFin F v)) : m ∈ UAt σ Y (evFin F v) := by
  show ∀ c : AF F, evFin F v c = 0 → c • (mat m - 1) = 0
  intro c hc
  have h2 : c • (cA σ (t⁻¹ : (AE F E)ˣ).1 - 1) = 0 := by
    rw [← map_one (cA σ), ← map_sub, ← map_smul, ht' c hc, map_zero]
  have hx : (c • (mat m - 1)) *ᵥ incV F H.x = 0 := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hL.1]
    exact GlobalTheory.LeviLoc.smul_sub_eq_zero (ht c hc) _
  have hy : (c • (mat m - 1)) *ᵥ incV F H.y = 0 := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hL.2.1]
    exact GlobalTheory.LeviLoc.smul_sub_eq_zero h2 _
  have hι : (c • (mat m - 1)) * incM F H.ι = 0 := by
    have h0 : c • (mat h₁ - 1) = 0 := hh c hc
    have e : (mat m - 1) * incM F H.ι = incM F H.ι * (mat h₁ - 1) := by
      rw [Matrix.sub_mul, Matrix.one_mul, hL.2.2, Matrix.mul_sub, Matrix.mul_one]
    rw [Matrix.smul_mul, e, ← Matrix.mul_smul, h0, Matrix.mul_zero]
  ext i j
  obtain ⟨s, r, u, e⟩ := hspan (Pi.single j 1)
  have hcol : (c • (mat m - 1)) *ᵥ incV F (Pi.single j (1 : E)) = 0 := by
    rw [e, GlobalTheory.LeviLoc.incV_decomp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hx, hy, hι, Matrix.zero_mulVec, smul_zero, smul_zero, add_zero, add_zero]
  rw [GlobalTheory.LeviUniqueCartan.incV_single, Matrix.mulVec_single_one] at hcol
  have := congrFun hcol i
  simpa [Matrix.col] using this

theorem adapted_spans (B : Base F E) {i₀ i₁ : ℕ} (hA : H.IsAdapted σ B Y Y₁ i₀ i₁)
    (hL : Submodule.span E (Y.L : Set (Fin n → E)) = ⊤) (z : Fin n → E) :
    ∃ (s r : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + r • H.y := by
  let S : Submodule E (Fin n → E) :=
    { carrier := {z | ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y}
      add_mem' := by
        rintro _ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
        exact ⟨s + s', t + t', u + u', by rw [add_smul, add_smul, Matrix.mulVec_add]; abel⟩
      zero_mem' := ⟨0, 0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨s, t, u, rfl⟩
        exact ⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul, smul_add, smul_add, mul_smul, mul_smul]⟩ }
  have hsub : (Y.L : Set (Fin n → E)) ⊆ S := fun z hz => by
    obtain ⟨s, t, u, -, -, -, e⟩ := hA.split z hz
    exact ⟨s, t, u, e⟩
  have hz : z ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
    rw [hL]; trivial
  exact Submodule.span_le.2 hsub hz

end Levi

section Core

variable {n d d₁ d₂ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {W₂ : Spc F E d₂}

end Core

end GlobalTheory.JacquetFlagLevi
