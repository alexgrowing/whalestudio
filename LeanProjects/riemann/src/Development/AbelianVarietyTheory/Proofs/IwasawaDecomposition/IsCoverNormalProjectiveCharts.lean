import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCellsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagModel

theorem exists_flagModel : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (algebraMap O K) s V α c D → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (π : I.subscheme ⟶ X) (g : ∀ en : En m, I.subscheme ⟶ PSpace O (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ I.subscheme)), π ≫ s = I.subschemeι ≫ PSpace.str O n ∧ IsFlagModel (algebraMap O K) s V α c π g κ := by
  intro O K _ _ _ _ _ _ _ X s T _ m M B _ V α c D hP hN hC
  obtain ⟨P, p0, p, h, hPlk⟩ := GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base O K _ X s T m M B V α c D hP hC
  obtain ⟨F, f, i, hf, hi, hif, hcov⟩ := GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct O K _ X s T m M B V α c D P p0 p h hP hN hC hPlk
  have hXn : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, rfl⟩ := hP
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  obtain ⟨hFc, hFn, hFnoe⟩ := GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover X T m B V F i hN hi hcov
  have hbase : ∀ b w, i b w ≫ f ≫ p0 ≫ s = spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp ((α b).comp (algebraMap O K))) := by
    intro b w
    rw [← Category.assoc, hif, ← Category.assoc, hPlk.base, cbase, Category.assoc, hC.ovr, ← Spec.map_comp]
    rfl
  have hrange : Set.range (f ≫ (p0 ≫ s)) ⊆ Set.range (spMap (algebraMap O K)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hcov x
    refine ⟨spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp (α b)) y, ?_⟩
    have e := congrArg (fun φ => φ y) (hbase b w)
    have e2 : spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp ((α b).comp (algebraMap O K))) =
        spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp (α b)) ≫ spMap (algebraMap O K) := by rw [← Spec.map_comp]; rfl
    rw [e2] at e
    simp only [Scheme.Hom.comp_apply] at e ⊢
    exact e.symm
  obtain ⟨n, I, ν, j, hν, hIn, hIf, hj, hjν, hdense⟩ :=
    GlobalTheory.NormClosure.exists_normal_closure O K P F (p0 ≫ s) f hPlk.proj hf hFc hFn hrange
  have hsep : IsSeparated (ν ≫ p0) := by
    have : IsProper (PSpace.str O n) := isProper_str O n
    have : IsProper ((ν ≫ p0) ≫ s) := by rw [Category.assoc, hν]; infer_instance
    exact IsSeparated.of_comp (ν ≫ p0) s
  have hcover := GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells O K _ X s T m M B V α c D P p0 p h hC hPlk F I.subscheme f i j ν hf hi hif
    hcov hj hjν hdense hFnoe hsep
  refine ⟨n, I, ν ≫ p0, fun en => ν ≫ p en, fun b w => i b w ≫ j, by rw [Category.assoc, hν], ?_⟩
  have hflat : Flat ((ν ≫ p0) ≫ s) := by rw [Category.assoc]; exact hIf
  have hdense' : Dense ((ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X)) := by rw [hcover]; exact hdense
  refine ⟨⟨?_, ?_⟩, hIn, hflat, ?_, ?_, hdense', ?_⟩
  · intro b w
    rw [Category.assoc, ← Category.assoc j, hjν, ← Category.assoc, hif, hPlk.base]
  · intro b w en
    obtain ⟨hu, e⟩ := hPlk.plk b w en
    exact ⟨hu, by rw [Category.assoc, ← Category.assoc j, hjν, ← Category.assoc, hif, e]⟩
  · intro b w
    have := hi b w
    infer_instance
  · rw [hcover]
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨b, w, y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨b, w, y, rfl⟩ := hcov x
      exact ⟨b, w, y, rfl⟩
  · intro k _ z z' hz e1 e2
    have hr : ∀ y, (ν ≫ p0) (z y) ∈ ⋃ b, ((V b).1 : Set X) := fun y =>
      hz ⟨y, (Scheme.Hom.comp_apply _ _ _)⟩
    have hz1 : Set.range z ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      rw [← hcover]
      exact hr y
    have hz2 : Set.range z' ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      rw [← hcover]
      have e := congrArg (fun φ => φ y) e1
      simp only [Scheme.Hom.comp_apply] at e
      show (ν ≫ p0) (z' y) ∈ ⋃ b, ((V b).1 : Set X)
      simp only [Scheme.Hom.comp_apply] at hr ⊢
      rw [← e]
      exact hr y
    let z₀ := IsOpenImmersion.lift j z hz1
    let z₀' := IsOpenImmersion.lift j z' hz2
    have f₀ : z₀ ≫ j = z := IsOpenImmersion.lift_fac _ _ _
    have f₀' : z₀' ≫ j = z' := IsOpenImmersion.lift_fac _ _ _
    have key : z₀ ≫ f = z₀' ≫ f := by
      refine hPlk.ext _ _ _ ?_ fun en => ?_
      · rw [← hjν, ← Category.assoc, ← Category.assoc, f₀, f₀', Category.assoc, Category.assoc]
        exact e1
      · rw [← hjν, ← Category.assoc, ← Category.assoc, f₀, f₀', Category.assoc, Category.assoc]
        exact e2 en
    have := hf
    rw [← f₀, ← f₀', (cancel_mono f).1 key]

end GlobalTheory.FlagModel
