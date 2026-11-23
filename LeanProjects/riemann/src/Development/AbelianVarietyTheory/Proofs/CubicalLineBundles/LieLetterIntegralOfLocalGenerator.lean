import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MemLieVectorLineIdealIffMemLieLattice
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isDiffOf_mem_lieLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {f : P.A ⟶ P'.A} {D : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)} (hD : F.IsDiffOf F' f D)
    {c : Fin F.P₀.g → K} (hc : c ∈ F.lieLat) : D c ∈ F'.lieLat := by
  have key : F.lieLat ≤ (F'.lieLat).comap (D.restrictScalars (𝓞 K)) := by
    unfold GenFib.lieLat
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu⟩
    exact Submodule.subset_span ⟨u ≫ f, hD u x hu⟩
  exact key hc

theorem smul_image_mem_lieLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    (F' : GenFib P') (f : P.A ⟶ P'.A) (hf : IsMonHom f) (i : Fin F.P₀.g) (w : epsR K ⟶ F'.P₀.A)
    (U : Fin F'.P₀.g → K) (hw : w.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left) (hU : IsLieComb U F'.v w) (c : K)
    (hc : (Pi.single i c : Fin F.P₀.g → K) ∈ F.lieLat) : c • U ∈ F'.lieLat := by
  obtain ⟨⟨M, hM, -⟩, f₀, -, hf₀, hcomb⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  have hmem : M (Pi.single i c) ∈ F'.lieLat := isDiffOf_mem_lieLat hM hc
  have hv : IsLieComb (Pi.single i 1) F.v (F.v i) :=
    (GlobalTheory.LieComb.lieComb_algebra K F.P₀.A F.P₀.g F.v F.basis.1).2.2.2.1 i
  have h1 : IsLieComb (M (Pi.single i 1)) F'.v (F.v i ≫ f₀) := hcomb M hM _ _ hv
  have hw' : F.v i ≫ f₀ = w := by
    apply Over.OverMorphism.ext
    apply F'.fib.2.1.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hf₀, hw]
    · rw [Over.w, Over.w]
  rw [hw'] at h1
  have htan : IsTangent w :=
    (GlobalTheory.LieComb.lieComb_algebra K F'.P₀.A F'.P₀.g F'.v F'.basis.1).2.1 U w hU
  have hUeq : M (Pi.single i 1) = U := (F'.basis.2 w htan).unique h1 hU
  have hsingle : (Pi.single i c : Fin F.P₀.g → K) = c • Pi.single i 1 := by
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsingle, map_smul, hUeq] at hmem
  exact hmem

theorem image_integral_of_isLocGen {K : Type} [Field K] [NumberField K] {A B : Out.PolAV (Sp (𝓞 K))} {x y : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} {ψ : y.P.A.left ⟶ B.A.left} (hx : IsFibreOf A x (gmap K) φ)
    (hy : IsFibreOf B y (gmap K) ψ) (f : A.A ⟶ B.A) (hf : IsMonHom f) {i : Fin x.P.g} {ℓ : MLine K}
    (hℓ : IsVecLine A x φ i ℓ) {w : epsR K ⟶ y.P.A} {U : Fin y.P.g → K}
    (hw : w.left ≫ ψ = (x.v i).left ≫ φ ≫ f.left) (hU : IsLieComb U y.v w) {p : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin y.P.g) (Fin y.P.g) K} (hM : IsModelAt B y ψ p M) {cl : K} (hcl : IsLocGen p cl ℓ.I) (m) :
    p.valuation K (Matrix.vecMul (cl • U) M⁻¹ m) ≤ 1 := by
  have hfA : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).mp hx
  have hfB : IsPolFibre (algebraMap (𝓞 K) K) B y.P ψ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) B y ψ).mp hy
  have hI : ℓ.I ≠ 0 := hℓ.1.1
  obtain ⟨s, hs, hsI⟩ : ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • cl ∈ ℓ.I :=
    ((((local_global_ideal_lattice K).2.1 ℓ.I p hI).2 cl).mp hcl).2 cl |>.mp le_rfl
  have hA : (Pi.single i (s • cl) : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hfA x.v x.basis : GenFib A).lieLat :=
    (isVecLine_mem_iff_mem_lieLat K A x φ hfA i ℓ hℓ (s • cl)).mp hsI
  have hB := smul_image_mem_lieLat (GenFib.mk x.P φ hfA x.v x.basis) (GenFib.mk y.P ψ hfB y.v y.basis) f hf i w U
    hw hU (s • cl) hA
  have key := (isModelAt_integral_iff_mem_lieLat K B y ψ hfB p M hM (cl • U)).mpr
    ⟨s, hs, by rw [← smul_assoc]; exact hB⟩
  exact key m

theorem letter_integral_of_isLocGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (M : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁), IsModelAt o.B o.xB o.φB p M → ∀ (k : Fin o.xB.P.g) (cl : o.K₁), IsLocGen p cl (L.ℓ k).I → ∀ m, p.valuation o.K₁ (Matrix.vecMul (cl • L.U k) M⁻¹ m) ≤ 1 := by
  intro E _ _ _ _ H l c nΨ n' f o La hgood L hL p M hM k cl hcl m
  obtain ⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, hiso, -, -, hℓΨ, hℓ', -⟩ := hgood
  obtain ⟨-, -, hlet, hline⟩ := hL
  obtain ⟨w, hwk, hU⟩ := hlet k
  have hlk := hline k
  unfold LamLetters.IsLetter at hwk
  rcases hsrc : L.src k with q | q <;> rw [hsrc] at hwk hlk
  · dsimp only at hwk hlk
    rw [hlk] at hcl
    exact image_integral_of_isLocGen hΨ hB (o.φΨ q.1) (hiso.1 q.1) (hℓΨ q.2) hwk hU hM hcl m
  · dsimp only at hwk hlk
    rw [hlk] at hcl
    exact image_integral_of_isLocGen h' hB (o.φ' q.1) (hiso.2.1 q.1) (hℓ' q.2) hwk hU hM hcl m

end GlobalTheory.LamF
