import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviSectionCont

theorem continuous_levi_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    Continuous (fun p : (AE F E)ˣ × UA σ G₁.V.J => m p.1 p.2) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC _ hG _ m hm
  have hL : Submodule.span E (G.V.L : Set (Fin (b + 2) → E)) = ⊤ := hG.hV.lat.span_eq_top
  choose s t u hdec using fun j : Fin (b + 2) =>
    GlobalTheory.IterBochner.exists_decomp B H G.V G₁.V hC.hH hL (Pi.single j 1)
  exact GlobalTheory.IterBochner.continuous_of_isLevi H s t u hdec m hm

end GlobalTheory.LeviSectionCont
