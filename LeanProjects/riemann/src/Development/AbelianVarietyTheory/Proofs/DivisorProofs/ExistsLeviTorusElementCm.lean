import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK

open GlobalTheory.LeviPlane

theorem exists_isLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' r s i₀ i₁ hcm hW hH t
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hc : ∀ z, c (c z) = z := cA_invol (sigma_invol hcm)
  have hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [hcdef, incM, Matrix.map_apply, cAr_inclR, hW.skew, map_neg]
  have hxx : fm c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fm_inc, hH.xx, map_zero]
  have hyy : fm c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fm_inc, hH.yy, map_zero]
  have hxy : fm c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fm_inc, hH.xy, map_one]
  have hι : ∀ j, fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.x) = 0 ∧
      fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.y) = 0 := by
    intro j
    have ho := hH.orth (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at ho
    have h1 : form σ W.J (fun i => H'.ι i j) H'.x = 0 := ho.1
    have h2 : form σ W.J (fun i => H'.ι i j) H'.y = 0 := ho.2
    have e : (fun i => incM F H'.ι i j) = incV F (fun i => H'.ι i j) := rfl
    rw [e, fm_inc, fm_inc, h1, h2, map_zero]
    exact ⟨rfl, rfl⟩
  let L : AE F E → AE F E → Matrix (Fin d) (Fin d) (AE F E) := lev c (incM F W.J) (incV F H'.x) (incV F H'.y)
  have hinv : ∀ u : (AE F E)ˣ, L u (c (u⁻¹ : (AE F E)ˣ)) * L (u⁻¹ : (AE F E)ˣ) (c u) = 1 := by
    intro u
    show lev c _ _ _ _ _ * lev c _ _ _ _ _ = 1
    rw [lev_mul hc hJ hxx hyy hxy, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, lev_one hc hJ hxx hyy hxy]
  let g : GL (Fin d) (AE F E) := ⟨L t (c (t⁻¹ : (AE F E)ˣ)), L (t⁻¹ : (AE F E)ˣ) (c t), hinv t, by simpa using hinv t⁻¹⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) := by
    show (L t (c (t⁻¹ : (AE F E)ˣ)))ᵀ * incM F W.J * (L t (c (t⁻¹ : (AE F E)ˣ))).map c = incM F W.J
    exact lev_unitary hc hJ hxx hyy hxy _ _ (by rw [hc, Units.mul_inv])
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
  · exact lev_X hxx hxy _ _
  · exact lev_Y hc hJ hxx hyy hxy _ _
  · show L t (c (t⁻¹ : (AE F E)ˣ)) * incM F H'.ι = incM F H'.ι * 1
    rw [Matrix.mul_one]
    exact lev_mul_ι _ hι _ _

end GlobalTheory.ThK
