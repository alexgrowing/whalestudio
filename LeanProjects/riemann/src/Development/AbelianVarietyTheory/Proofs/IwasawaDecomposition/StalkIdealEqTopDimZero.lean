import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenFibre

theorem isUnit_of_flat_of_dim_zero {A B : Type} [CommRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : φ.Flat) (hd : ringKrullDim B = 0) {a : A} (ha : a ∈ nonZeroDivisors A) :
    IsUnit (φ a) := by
  letI := φ.toAlgebra
  have : Module.Flat A B := hφ
  have hreg : IsSMulRegular B (a ^ 0 * a) := by
    rw [pow_zero, one_mul]; exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha
  haveI : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.2 (le_of_eq (by exact_mod_cast hd))
  by_contra hna
  have hm : φ a ∈ maximalIdeal B := hna
  obtain ⟨k, hk⟩ := Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.2 hm
  have hreg' : IsSMulRegular B (a ^ k) := by
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) (pow_mem ha k)
    exact this
  have h1 : (a ^ k) • (1 : B) = (a ^ k) • (0 : B) := by
    rw [smul_zero, Algebra.smul_def, mul_one, map_pow, RingHom.algebraMap_toAlgebra, hk]
  exact one_ne_zero (hreg' h1)

theorem flat_of_stalkClosedPointTo {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) : Flat ξ := by
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  rw [← e]
  have h₁ : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := by rw [Flat.SpecMap_iff]; exact hf
  have h₂ := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X (ξ (closedPoint _))
  exact MorphismProperty.comp_mem @Flat _ _ h₁ h₂

theorem stalkId_eq_top_of_dim_zero : ∀ {X Y' Y : Scheme.{0}} (ρ : Y' ⟶ X) (ι : Y' ⟶ Y) [Flat ι] (D : EffCartierData Y) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X), (Scheme.stalkClosedPointTo ξ).hom.Flat → ∀ v : ↥(pullback ξ ρ : Scheme.{0}), ringKrullDim ((pullback ξ ρ).presheaf.stalk v) = 0 → FinalTheorems.stalkId (((D.idealSheaf ^ n).comap ι).comap (pullback.snd ξ ρ)) v = ⊤ := by
  intro X Y' Y ρ ι _ D n R _ _ ξ hf v hv
  haveI : Flat ξ := flat_of_stalkClosedPointTo ξ hf
  obtain ⟨i, hi⟩ := D.exists_mem (ι (pullback.snd ξ ρ v))
  have hreg := GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) _ hi
  have hfl : ((pullback.snd ξ ρ).stalkMap v).hom.comp (ι.stalkMap (pullback.snd ξ ρ v)).hom |>.Flat :=
    RingHom.Flat.comp (Flat.stalkMap ι _) (Flat.stalkMap (pullback.snd ξ ρ) v)
  have hu := isUnit_of_flat_of_dim_zero _ hfl hv hreg
  rw [GlobalTheory.VanStalk.stalkId_comap, GlobalTheory.VanStalk.stalkId_comap, GlobalTheory.Vanishing.stalkId_pow,
    D.stalkId_idealSheaf i _ hi, Ideal.map_map, Ideal.map_pow, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_eq_top.2 hu, Ideal.top_pow]

end GlobalTheory.GenFibre
