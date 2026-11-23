import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.TenDim

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem exists_isLieBasis {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (h : SmoothOfRelativeDimension n G.hom) : ∃ v : Fin n → (epsR k ⟶ G), IsLieBasis v := by
  obtain ⟨x, hx⟩ := ObjDim.univChart_of_relativeDimension G h
  exact ⟨_, Chart.basis_of_chart hx⟩

theorem dim_eq_field {k O M : Type} [Field k] [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] {G A : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M)
    (hG : SmoothOfRelativeDimension 1 G.hom) {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) :
    n = Module.finrank O M := by
  obtain ⟨v, hv⟩ := exists_isLieBasis G hG
  obtain ⟨w, hw⟩ := exists_isLieBasis A hA
  have h1 : Module.finrank k (Serre.Lie a) = 1 :=
    (Module.finrank_eq_card_basis (Serre.Lie.basis a hv)).trans (Fintype.card_fin 1)
  have hb : Function.Bijective (algebraMap k (Module.End k (Serre.Lie a))) := by
    have := Module.Finite.of_basis (Serre.Lie.basis a hv)
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap, Module.finrank_linearMap, h1]
  let e := RingEquiv.ofBijective _ hb
  let τ : O →+* k := e.symm.toRingHom.comp (Module.toModuleEnd k (Serre.Lie a))
  have hτ : Serre.Lie.eig a τ = ⊤ := eq_top_iff.2 fun u _ => Serre.Lie.mem_eig_iff.2 fun x =>
    (LinearMap.congr_fun (e.apply_symm_apply (Module.toModuleEnd k (Serre.Lie a) x)) u).symm
  letI : Algebra O k := τ.toAlgebra
  have e' := t.lieEquivScalar b (N := k)
    ((Serre.Lie.basis a hv).equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) k k).symm hτ
  rw [← finrank_fibre O M k, e'.finrank_eq, Module.finrank_eq_card_basis (Serre.Lie.basis b hw),
    Fintype.card_fin]

theorem smoothOfRelativeDimension {S : Scheme.{0}} {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] {G A : Over S} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M)
    (hab : IsAbelianScheme G) (hG : SmoothOfRelativeDimension 1 G.hom) :
    SmoothOfRelativeDimension (Module.finrank O M) A.hom := by
  have hA : IsAbelianScheme A := t.isAbelianScheme hab
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using H1.exists_dim A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank O M)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank O M)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := A.left.residueField y
  let z : Sp k ⟶ A.left := A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ A.hom
  have : ConnectedSpace ↥(pullback A.hom x) :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) x _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd A.hom x) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hG' : SmoothOfRelativeDimension 1 (pullback.snd G.hom x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  rw [← dim_eq_field (t.pullback x) hG' hm, ← e₁]
  exact hd y

end GlobalTheory.CM.TenDim

namespace GlobalTheory.CM

theorem tensor_smoothOfRelativeDimension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A), Nonempty (Serre.IsTensor A b C.P.A C.act D.La) → SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) A.hom := by
  rintro E _ _ _ H R _ ω C D A _ _ b ⟨t⟩
  obtain ⟨h1, h2, h3⟩ := (OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
  rw [← D.rank, ← h3]
  exact TenDim.smoothOfRelativeDimension t C.P.isAb (C.dim ▸ C.P.smoothDim)

end GlobalTheory.CM
