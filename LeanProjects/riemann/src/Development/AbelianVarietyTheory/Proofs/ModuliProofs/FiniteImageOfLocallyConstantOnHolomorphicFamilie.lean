import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedAndDenseComplHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedUnramifiedCoverOfIrreducible
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsPrimitiveElementDiscriminantMultiple
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsConnectedPrincipalOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.PrincipalOpenDenseComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedBasicOpenComplexPointsOfDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.FiniteClasses

open GlobalTheory.Points

theorem preconnectedSpace_pts (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : PreconnectedSpace (Pts (spMap (algebraMap ℂ A))) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) A 1 one_ne_zero
  have he := isEmbedding_ptsOverEquivAlgHom (C := ℂ) A (id_eq_spMap_algebraMap ℂ)
  refine ⟨he.isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨(ptsOverEquivAlgHom A (id_eq_spMap_algebraMap ℂ)).symm φ, trivial, by simp⟩

theorem finite_range_affine (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] {I : Type*}
    (c : Pts (spMap (algebraMap ℂ A)) → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcomp : ∀ P : Ideal A, spMap (Ideal.Quotient.mk P) ≫ spMap (algebraMap ℂ A) =
      spMap (algebraMap ℂ (A ⧸ P)) := fun P => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfin : (⋃ P ∈ minimalPrimes A,
      Set.range (c ∘ PtsOver.map (spMap (Ideal.Quotient.mk P)) (hcomp P) (𝟙 _))).Finite := by
    refine (minimalPrimes.finite_of_isNoetherianRing A).biUnion fun P hP => ?_
    have : P.IsPrime := hP.1.1
    have := preconnectedSpace_pts (A ⧸ P)
    exact Set.Subsingleton.finite (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hc.comp_continuous (PtsOver.continuous_map _ _ _)).apply_eq_of_preconnectedSpace a b)
  refine hfin.subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, rfl⟩ := (ptsEquivAlgHom A).symm.surjective x
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := RingHom.ker φ.toRingHom) bot_le
  refine Set.mem_biUnion (x := P) hP ⟨(ptsEquivAlgHom (A ⧸ P)).symm
    (Ideal.Quotient.liftₐ P φ fun a ha => hle ha), congrArg c (Subtype.ext ?_)⟩
  simp only [PtsOver.map_val, ptsOverEquivAlgHom_symm_val]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem finite_range {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [QuasiCompact p] {I : Type*}
    (c : Pts p → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let 𝒰 := Y.affineOpenCover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (X := Y)
    (fun i => ((𝒰.f i).opensRange : Set Y)) (fun i => (𝒰.f i).opensRange.isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨𝒰.idx y, 𝒰.covers y⟩)
  have key : ∀ {R : CommRingCat.{0}} (j : Spec R ⟶ Y) [IsOpenImmersion j],
      (Set.range (c ∘ PtsOver.map j rfl (𝟙 _))).Finite := by
    intro R j _
    have hl : IsLocallyConstant (c ∘ PtsOver.map j rfl (𝟙 _)) :=
      hc.comp_continuous (PtsOver.continuous_map _ _ _)
    have hft : LocallyOfFiniteType (j ≫ p) := inferInstance
    generalize c ∘ PtsOver.map j rfl (𝟙 _) = c' at hl
    generalize j ≫ p = q at c' hl hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact finite_range_affine R c' hl
  refine (t.finite_toSet.biUnion fun i _ => key (𝒰.f i)).subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (x.1 (IsLocalRing.closedPoint ℂ))))
  have hx' : x ∈ Set.range (PtsOver.map (𝒰.f i) rfl (𝟙 _)) := by
    rw [PtsOver.range_map, range_comp_of_isOpenImmersion]
    exact (le_preimage_iff x.1 _).2 hx
  obtain ⟨z, rfl⟩ := hx'
  exact Set.mem_biUnion hi ⟨z, rfl⟩

theorem isLocallyConstant_of_hol {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) (d : ℕ)
    (hp : SmoothOfRelativeDimension d p) {I : Type*} (c : Pts p → I)
    (H : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → Pts p), IsOpen B → IsHolTo B (fun b => (y b).1) →
      ∀ b₀ ∈ B, ∀ᶠ b in 𝓝 b₀, c (y b) = c (y b₀)) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let h := overHomeomorph (C := ℂ) (Over.mk p)
  obtain ⟨W, σ, U, t, hW, h0, hσ, -, hhol, hco, hop, -⟩ := HolChart.exists_holomorphic_chart valAt'_rules
    existsUnique_point_of_ringHom exists_holomorphic_section_of_etale (Over.mk p) d hp (h.symm x)
  have hop' : IsOpen (σ '' W) := by
    refine TopologicalSpace.le_def.1 (le_generateFrom ?_) _ hop
    rintro _ ⟨V, f, O, hO, rfl⟩
    exact (isOpen_basicSet (C := ℂ) V f hO).preimage (isEmbedding_left (Over.mk p)).continuous
  have hx : h (σ 0) = x := by rw [hσ, Homeomorph.apply_symm_apply]
  have hev := H W (fun b => h (σ b)) hW hhol 0 h0
  have hxU : ⊤ ≤ x.1 ⁻¹ᵁ U := by rw [← hx]; exact (hco 0 h0).1
  have hT : Tendsto (fun (z : Pts p) (i : Fin d) => valR z.1 U (t i)) (𝓝 x) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    have h1 := ((continuousAt_valR (t i) hxU).comp continuous_subtype_val.continuousAt).tendsto
    have h2 : valR x.1 U (t i) = (0 : Fin d → ℂ) i := by rw [← hx]; exact (hco 0 h0).2 i
    rw [← h2]
    exact h1
  have hN : h '' (σ '' W) ∈ 𝓝 x := (h.isOpenMap _ hop').mem_nhds ⟨_, ⟨0, h0, rfl⟩, hx⟩
  filter_upwards [hN, hT.eventually hev] with z hz hz'
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have : (fun i => valR (h (σ w)).1 U (t i)) = w := funext (hco w hw).2
  rw [this, hx] at hz'
  exact hz'

theorem finite_image_of_locally_constant_on_holomorphic_families :
    (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B) → ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (I : Type 1) (cls : (Sp ℂ ⟶ X) → I), SmoothOfRelativeDimension d s → QuasiCompact s → (∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B, ∀ᶠ b in nhds b₀, cls (y b) = cls (y b₀)) → (cls '' {x | x ≫ s = spMap σ}).Finite := by
  intro _ k _ σ X s d I cls hs hq H
  let p := pullback.snd s (spMap σ)
  let q := pullback.fst s (spMap σ)
  have hp : SmoothOfRelativeDimension d p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback s (spMap σ)) hs
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hover : ∀ z : Pts p, (z.1 ≫ q) ≫ s = spMap σ := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, Category.id_comp]
  have hl : IsLocallyConstant fun z : Pts p => cls (z.1 ≫ q) := by
    refine isLocallyConstant_of_hol p d hp _ fun B y hB hy => ?_
    refine H B (fun b => (y b).1 ≫ q) hB (fun b _ => hover _) fun U f => ?_
    simp only [valAt'_eq_valR, valR_comp]
    exact hy (q ⁻¹ᵁ U) ((q.app U).hom f)
  refine (finite_range p _ hl).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx), pullback.lift_snd _ _ _⟩, ?_⟩
  exact congrArg cls (pullback.lift_fst _ _ _)

end GlobalTheory.FiniteClasses
