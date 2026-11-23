import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsIntDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace BlockImage

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in

theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff, heq_iff_eq, true_and] at h
  rw [h]

omit [Fintype ι] [DecidableEq ι] in

theorem const_injective (k₀ : ι) : Function.Injective (fun _ : Unit ↦ k₀) := fun _ _ _ ↦ rfl

omit [Fintype ι] in

theorem rename_component (k₀ : ι) (m : Unit → ℕ) (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    rename (blockIncl k₀) (weightedHomogeneousComponent (coordDeg fun _ : Unit ↦ n k₀) m f) =
      weightedHomogeneousComponent (coordDeg n) (Function.extend (fun _ : Unit ↦ k₀) m 0)
        (rename (blockIncl k₀) f) :=
  FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent (ι := blockIdx fun _ : Unit ↦ n k₀)
    (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀) (g := blockIncl k₀) (fun _ ↦ rfl)
    (const_injective k₀) (blockIncl_injective k₀) m f

def projVariety (P : ArithVariety n) (k₀ : ι) : ArithVariety (fun _ : Unit ↦ n k₀) where
  ideal := P.projIdeal k₀
  isPrime := by
    have := P.isPrime
    exact Ideal.comap_isPrime _ _
  homogeneous f hf m := by
    change rename (blockIncl k₀) _ ∈ P.ideal
    rw [rename_component]
    exact P.homogeneous _ hf _
  relevant k := by
    obtain ⟨i, hi⟩ := P.relevant k₀
    refine ⟨i, fun h ↦ hi ?_⟩
    change rename (blockIncl k₀) (X ⟨k, i⟩) ∈ P.ideal at h
    rwa [rename_X] at h
  horizontal a ha := by
    change rename (blockIncl k₀) (C a) ∈ P.ideal at ha
    rw [rename_C] at ha
    exact P.horizontal a ha

variable {Ω : Type} [Field Ω]

omit [Fintype ι] [DecidableEq ι] in

theorem mConeMap_rename (y : Coord n → Ω) (k₀ : ι)
    (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (rename (blockIncl k₀) f) =
      rename (fun _ : Unit ↦ k₀)
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) f) := by
  have h : ((Geo.mConeMap (ι := blockIdx n) y).comp (rename (blockIncl k₀))) =
      ((rename (R := Ω) (fun _ : Unit ↦ k₀)).restrictScalars ℤ).comp
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) := by
    refine MvPolynomial.algHom_ext fun v ↦ ?_
    simp [Geo.mConeMap, blockIncl]
  exact congrArg (fun φ : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ f) h

omit [Fintype ι] [DecidableEq ι] in

theorem comap_mCoordIdeal (y : Coord n → Ω) (k₀ : ι) :
    (Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀)) =
      Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) := by
  ext f
  simp only [Ideal.mem_comap, Geo.mCoordIdeal, RingHom.mem_ker]
  rw [mConeMap_rename]
  exact map_eq_zero_iff _ (rename_injective _ (const_injective k₀))

theorem algebraMap_injective {K : Type} {κ : K → Type} (I : Ideal (Geo.MRing κ))
    (h : Geo.IsHorizontal I) : Function.Injective (algebraMap ℤ (Geo.MRing κ ⧸ I)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  have h' : a ∈ I.comap (C : ℤ →+* Geo.MRing κ) := ha
  rw [show I.comap (C : ℤ →+* Geo.MRing κ) = ⊥ from h] at h'
  exact (Submodule.mem_bot ℤ).mp h'

omit [Fintype ι] in

theorem birational_of_block (y : Coord n → Ω) (k₀ : ι)
    (hB : Geo.Birational (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) :
    Geo.Birational (ι := blockIdx n) y := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, heq⟩ := hB s
  have hom : ∀ f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ,
      Geo.IsMultiHomog (ι := blockIdx fun _ : Unit ↦ n k₀) f d →
      Geo.IsMultiHomog (ι := blockIdx n) (rename (blockIncl k₀) f)
        (Function.extend (fun _ : Unit ↦ k₀) d 0) := by
    intro f hf
    rw [← Bridge.isMultiHomog_iff] at hf ⊢
    have hf' : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ n k₀) f d := hf
    rw [← hf'.weightedHomogeneousComponent_same, rename_component]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  refine ⟨Function.extend (fun _ : Unit ↦ k₀) d 0, rename (blockIncl k₀) g, rename (blockIncl k₀) h,
    hom g hg, hom h hh, ?_, ?_⟩
  · rw [aeval_rename]
    exact hne
  · rw [aeval_rename, aeval_rename]
    exact heq

end BlockImage

open BlockImage in

theorem BlockImage.proof (hDim : IntDomainDim.Statement) (hTr : ConeTrdeg.Statement) :
    BlockImage.Statement := by
  refine ⟨fun ι _ _ n P k₀ ↦ ⟨projVariety P k₀, rfl⟩, ?_⟩
  intro ι _ _ n Ω _ y k₀ D hA
  refine ⟨comap_mCoordIdeal y k₀, fun hB ↦ ?_⟩
  obtain ⟨-, hMP, hHor, hKd⟩ := hA
  rw [← comap_mCoordIdeal y k₀]
  have hMP' : Geo.IsMultiProjPrime (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP ⊢
    refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename
      (ι := blockIdx fun _ : Unit ↦ n k₀) (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀)
      (g := blockIncl k₀) (fun _ ↦ rfl) (const_injective k₀) (blockIncl_injective k₀) ?_ hMP
    rintro ⟨k, i⟩ ⟨u, hu⟩
    obtain rfl : k₀ = k := hu
    exact ⟨⟨(), i⟩, rfl⟩
  have hHor' : Geo.IsHorizontal (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor
    simp only [Ideal.mem_comap]
    rw [rename_C]
  refine ⟨inferInstance, hMP', hHor', ?_⟩

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hMP.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [Geo.mCoordIdeal, RingHom.mem_ker]
    simp [Geo.mConeMap, h0]
  rw [comap_mCoordIdeal y k₀] at hHor' hMP' ⊢
  have := hMP.1
  have := hMP'.1
  have dimA := hDim _ (algebraMap_injective _ hHor)
  have dimA' := hDim _ (algebraMap_injective _ hHor')
  rw [hTr ι (blockIdx n) Ω y (birational_of_block y k₀ hB) hrel hHor] at dimA
  rw [hTr Unit (blockIdx fun _ : Unit ↦ n k₀) Ω _ hB (fun _ ↦ hrel k₀) hHor'] at dimA'
  rw [hKd] at dimA
  have h1 : ((D + 1 + Fintype.card ι : ℕ) : ℕ∞) =
      (Algebra.trdeg ℤ Ω + Fintype.card ι).toENat + 1 := by exact_mod_cast dimA
  simp only [map_add, map_natCast] at h1
  have key : (Algebra.trdeg ℤ Ω).toENat = D := by
    generalize (Algebra.trdeg ℤ Ω).toENat = t at h1 ⊢
    induction t using ENat.recTopCoe with
    | top => simp at h1
    | coe m =>
      norm_cast at h1 ⊢
      omega
  rw [dimA']
  simp only [map_add, map_natCast, Fintype.card_unit, key]
  norm_cast

end

end GroundTheory.Heights₂.Heights
