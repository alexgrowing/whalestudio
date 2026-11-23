import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

theorem idem_apply_eq_zero_of_ne : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0 := by
  intro D ι h1 h2 P e he P' hP
  have hee : e * e = e := he.1.1
  have hm : ∀ a b : AE D, ι (finPart D (a * b)) P' = ι (finPart D a) P' * ι (finPart D b) P' := fun a b => by
    rw [RingHom.map_mul, map_mul]; rfl
  by_contra h0
  have hone : ι (finPart D e) P' = 1 := mul_left_cancel₀ h0 (by rw [← hm, hee, mul_one])
  refine hP (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun x hx => ?_))
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
  refine (he.2 x hx0).2 fun hint => ?_
  have hv := (h2 _).1 hint P'
  have hi : ι (finPart D (incA D ((x : D.host.E)⁻¹))) P' =
      algebraMap D.host.E (P'.adicCompletion D.host.E) ((x : D.host.E)⁻¹) :=
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P') (h1 ((x : D.host.E)⁻¹))
  rw [hm, hone, one_mul, hi, map_inv₀, map_inv₀, GlobalTheory.GeoLevel.valued_coe_int] at hv
  have hlt : P'.intValuation x < 1 := (P'.intValuation_lt_one_iff_mem x).2 hx
  have hpos : 0 < P'.intValuation x := zero_lt_iff.2 (P'.intValuation_ne_zero x hx0)
  exact absurd ((inv_le_one₀ hpos).1 hv) (not_le.2 hlt)

end GlobalTheory.ExportSeries
