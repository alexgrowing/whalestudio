import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRelativeDimOfTrdeg
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClosureDim

theorem ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero (F : Type) [Field F]
    {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra.FiniteType F A]
    (φ : A →+* B)
    (hB : @Algebra.FiniteType F B _ _ (φ.comp (algebraMap F A)).toAlgebra)
    (Q : Ideal B) [Q.IsPrime]
    (h : @Algebra.trdeg (Q.comap φ).ResidueField Q.ResidueField _ _
      (Ideal.ResidueField.map (Q.comap φ) Q φ rfl).toAlgebra = 0) :
    ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ Q.comap φ) := by
  letI : Algebra F B := (φ.comp (algebraMap F A)).toAlgebra
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set P := Q.comap φ
  letI : Algebra P.ResidueField Q.ResidueField := (Ideal.ResidueField.map P Q φ rfl).toAlgebra
  haveI : IsScalarTower F P.ResidueField Q.ResidueField := IsScalarTower.of_algebraMap_eq fun f ↦ by
    change algebraMap F Q.ResidueField f = Ideal.ResidueField.map P Q φ rfl (algebraMap F P.ResidueField f)
    rw [IsScalarTower.algebraMap_apply F A P.ResidueField, Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply F B Q.ResidueField]
    rfl
  haveI : Algebra.FiniteType F (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType F (B ⧸ Q) :=
    haveI := hB; Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F Q) Ideal.Quotient.mk_surjective
  have hfaith (S : Type) [CommRing S] [Nontrivial S] [Algebra F S] : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).mpr (algebraMap F S).injective
  haveI := hfaith (A ⧸ P); haveI := hfaith (B ⧸ Q); haveI := hfaith P.ResidueField
  haveI : FaithfulSMul (A ⧸ P) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr P.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Q.injective_algebraMap_quotient_residueField
  haveI : FaithfulSMul P.ResidueField Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  haveI : Algebra.IsAlgebraic (A ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ P))
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (B ⧸ Q))
  have h₁ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (A ⧸ P) P.ResidueField
  have h₂ := GlobalTheory.trdeg_eq_of_isAlgebraic_top F (B ⧸ Q) Q.ResidueField
  have h₃ := trdeg_add_eq F P.ResidueField (A := Q.ResidueField)
  rw [h, add_zero] at h₃
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq F (A ⧸ P)
  rw [hd₁]
  exact GlobalTheory.ringKrullDim_eq_of_trdeg_eq F (B ⧸ Q) (by rw [← h₂, ← h₃, h₁, hd₂])

end GlobalTheory.ClosureDim

namespace GlobalTheory.ClosureDim

theorem dim_closure_eq_of_isAlgebraic : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X)
    (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y),
    (letI := (π.residueFieldMap y).hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) →
    topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  intro F _ Y X π sX _ _ y halg
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ (π ⁻¹ᵁ U : Set Y) from hxU)
      (π ⁻¹ᵁ U).isOpen
  have hV : IsAffineOpen V := hV
  have e : V ≤ π ⁻¹ᵁ U := hVU
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  let φ := π.appLE U V e
  have hsq : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ π := IsAffineOpen.SpecMap_appLE_fromSpec π hU hV e
  have hpt : π (hV.fromSpec p) = hU.fromSpec (Spec.map φ p) := by
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have h0 : @Algebra.trdeg (X.residueField (π (hV.fromSpec p))) (Y.residueField (hV.fromSpec p)) _ _
      (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra = 0 := by
    letI := (π.residueFieldMap (hV.fromSpec p)).hom.toAlgebra
    exact trdeg_eq_zero (R := X.residueField (π (hV.fromSpec p))) (A := Y.residueField (hV.fromSpec p))
  rw [GlobalTheory.RelDimFibCrit.trdeg_affine π U hU V hV e p] at h0
  let ψ := Spec.preimage (hU.fromSpec ≫ sX)
  have hψ : Spec.map ψ = hU.fromSpec ≫ sX := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  have hA : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hB : @Algebra.FiniteType F Γ(Y, V) _ _ (φ.hom.comp (algebraMap F Γ(X, U))).toAlgebra := by
    have h : Spec.map (ψ ≫ φ) = hV.fromSpec ≫ π ≫ sX := by
      rw [Spec.map_comp, hψ, ← Category.assoc, hsq, Category.assoc]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ ≫ φ)).mp (h ▸ inferInstance)
  rw [hpt, GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient (π ≫ sX) hV.fromSpec p,
    GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient sX hU.fromSpec (Spec.map φ p)]
  haveI := p.isPrime
  exact ringKrullDim_quotient_eq_of_trdeg_residueField_eq_zero F φ.hom hB p.asIdeal h0

end GlobalTheory.ClosureDim
