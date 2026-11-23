import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section

namespace GlobalTheory.LeviUniq

theorem levi_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m m' : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m → IsLevi (W₁ := W₁) H' t 1 m' → m = m' := by
  intro F E _ _ _ _ _ σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t m m' hm hm'

  let S : Submodule E (Fin d → E) :=
    { carrier := {e | mat m *ᵥ incV F e = mat m' *ᵥ incV F e}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        have : incV F (a + b) = incV F a + incV F b := by
          funext i; simp [incV, map_add]
        rw [this, Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        have : incV F (0 : Fin d → E) = 0 := by funext i; simp [incV]
        rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at *
        have : incV F (c • a) = inclR (F := F) (AF F) c • incV F a := by
          funext i; simp [incV, map_mul]
        rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul, ha] }
  have hone : mat (1 : UA σ W₁.J) = 1 := rfl
  have hι : ∀ (g : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 g → ∀ u : Fin d₁ → E,
      mat g *ᵥ incV F (H'.ι *ᵥ u) = incV F (H'.ι *ᵥ u) := by
    intro g hg u
    have hv : incV F (H'.ι *ᵥ u) = incM F H'.ι *ᵥ incV F u := by
      funext i; simp [incV, incM, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [hv, Matrix.mulVec_mulVec, hg.2.2, hone, Matrix.mul_one]
  have hx : H'.x ∈ S := by
    show mat m *ᵥ incV F H'.x = mat m' *ᵥ incV F H'.x
    rw [hm.1, hm'.1]
  have hy : H'.y ∈ S := by
    show mat m *ᵥ incV F H'.y = mat m' *ᵥ incV F H'.y
    rw [hm.2.1, hm'.2.1]
  have hιS : ∀ u, H'.ι *ᵥ u ∈ S := by
    intro u
    show mat m *ᵥ incV F (H'.ι *ᵥ u) = mat m' *ᵥ incV F (H'.ι *ᵥ u)
    rw [hι m hm, hι m' hm']
  have hL : ∀ z ∈ W.L, z ∈ S := by
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
    exact S.add_mem (S.add_mem (S.smul_mem a hx) (hιS u)) (S.smul_mem b hy)
  have htop : S = ⊤ := by
    have h1 : Submodule.span E (W.L : Set (Fin d → E)) ≤ S := Submodule.span_le.2 hL
    rw [hW.lat.span_eq_top] at h1
    exact top_le_iff.1 h1
  have hall : ∀ e, mat m *ᵥ incV F e = mat m' *ᵥ incV F e := fun e => by
    have : e ∈ S := htop ▸ Submodule.mem_top
    exact this
  have hmat : mat m = mat m' := by
    ext i j
    have h := congrFun (hall (Pi.single j 1)) i
    have hs : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
      funext k; by_cases hk : k = j
      · subst hk; simp [incV]
      · simp [incV, Pi.single_apply, hk]
    rw [hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa using h
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUniq
