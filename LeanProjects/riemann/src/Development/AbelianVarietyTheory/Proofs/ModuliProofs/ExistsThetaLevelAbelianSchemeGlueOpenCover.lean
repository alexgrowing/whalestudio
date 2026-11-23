import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectComparisonMapsCocycleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GroupLawsOnCoverAgreeOnCommonPointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBinaryOpGluedAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGrpObjOfLocalGroupLawsOnCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsLocalOnBaseOfOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionAndIsMonHomOfOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionBasisGeometricFibresOfOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCoverStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

open CoverGlue

private theorem exists_section_of_compatible_local_sections {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    {G : ∀ i, Over (U i).toScheme} {ψ : ∀ i, (G i).left ⟶ A.left}
    (hp : ∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι)
    (σ : ∀ i, Out.baseOver (U i).toScheme ⟶ G i)
    (hσ : ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (σ i).left ≫ ψ i =
      S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (σ j).left ≫ ψ j) :
    ∃ x : Out.baseOver S ⟶ A, ∀ i, (σ i).left ≫ ψ i = (U i).ι ≫ x.left := by
  have hc : ∀ p : S, ∃ i, p ∈ Set.range (U i).ι := fun p => by
    obtain ⟨i, hi⟩ := exists_mem hU p
    exact ⟨i, by simpa using hi⟩
  obtain ⟨F, hF⟩ := exists_hom (fun i => (U i).ι) (fun i => inferInstance) hc
    (fun i => (σ i).left ≫ ψ i) (fun i j => isPullback_opens_inf (U i) (U j)) hσ
  have hw : F ≫ A.hom = 𝟙 S := by
    refine hom_ext (fun i => (U i).ι) (fun i => inferInstance) hc (fun i => ?_)
    have h1 := Over.w (σ i)
    rw [reassoc_of% (hF i), (hp i).w, reassoc_of% h1]
    simp
  refine ⟨Over.homMk F (by simpa using hw), fun i => ?_⟩
  simpa using (hF i).symm

private theorem exists_endo_of_compatible_local_endos {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    {G : ∀ i, Over (U i).toScheme} {ψ : ∀ i, (G i).left ⟶ A.left}
    (hp : ∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ (G i).left} {a' : ∀ i j, B i j ⟶ (G j).left}
    (hB : ∀ i j, IsPullback (a i j) (a' i j) (ψ i) (ψ j)) (e : ∀ i, G i ⟶ G i)
    (he : ∀ i j, a i j ≫ (e i).left ≫ ψ i = a' i j ≫ (e j).left ≫ ψ j) :
    ∃ f : A ⟶ A, ∀ i, (e i).left ≫ ψ i = ψ i ≫ f.left := by
  have hψ : ∀ i, IsOpenImmersion (ψ i) := fun i => isOpenImmersion (hp i)
  have hc := covers hU hp
  obtain ⟨F, hF⟩ := exists_hom ψ hψ hc (fun i => (e i).left ≫ ψ i) hB he
  have hw : F ≫ A.hom = A.hom := by
    refine hom_ext ψ hψ hc (fun i => ?_)
    rw [reassoc_of% (hF i), (hp i).w, reassoc_of% (Over.w (e i))]
  exact ⟨Over.homMk F hw, fun i => (hF i).symm⟩

private theorem hcompl_unit_property_of_isPrime {o : Type} [CommRing o] {S S' : Scheme.{0}} (f : S' ⟶ S) (s : S ⟶ Sp o) (u : oˣ) :
    Units.map f.appTop.hom.toMonoidHom (unitS s u) = unitS (f ≫ s) u := by
  ext
  simp [unitS]
  rfl

theorem exists_tobj_of_cover : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J b ((U i).ι ≫ s)), iSup U = ⊤ → (∀ i j, ∃ u : TObj g k J b ((U i ⊓ U j).ι ≫ s), TMap u (t i) (S.homOfLE inf_le_left) ∧ TMap u (t j) (S.homOfLE inf_le_right)) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J b (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∃ t₀ : TObj g k J b s, ∀ i, TMap (t i) t₀ (U i).ι := by
  intro o _ g k J b S s I U t hU hov hrig
  choose u hl hr using hov
  simp only [TMap] at hl hr
  choose a ha using hl
  choose a' ha' using hr
  have hcoc := GlobalTheory.T.thetaObject_comparison_maps_cocycle tObj_pull o g k J b S s I U t u a a'
    (fun i j => ⟨(ha i j).1, (ha i j).2.1, (ha i j).2.2.1⟩)
    (fun i j => ⟨(ha' i j).1, (ha' i j).2.1, (ha' i j).2.2.1⟩) hrig
  obtain ⟨A, ψ, hp, hB⟩ := GlobalTheory.T.glue_schemes_over_opens_along_cocycle S I U (fun i => (t i).A) (fun i j => (u i j).A) a a'
    (fun i j => (ha i j).1.1) (fun i j => (ha' i j).1.1) hcoc
  have hgl := GlobalTheory.T.group_laws_on_cover_agree_on_common_points S I U A (fun i => (t i).A) ψ (fun i j => (u i j).A) a a' hp
    (fun i j => (ha i j).1) (fun i j => (ha' i j).1) hB
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_binary_op_glued_along_cover S I U A (fun i => (t i).A) ψ (fun i => μ) hU hp
    (fun i j T r r' x y x' y' hx hy => by
      simpa only [Hom.mul_def] using (hgl.1 i j T r r' x y x' y' hx hy).1)
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_binary_op_glued_along_cover S I U A (fun i => (t i).A) ψ (fun i => fst _ _ ≫ ι) hU hp
    (fun i j T r r' x y x' y' hx hy => by
      simpa only [lift_fst_assoc, Hom.inv_def] using (hgl.1 i j T r r' x y x' y' hx hy).2)
  obtain ⟨e, he⟩ := exists_section_of_compatible_local_sections hU hp (fun i => (1 : Out.baseOver (U i).toScheme ⟶ (t i).A)) hgl.2
  obtain ⟨inst, hgp⟩ := GlobalTheory.T.exists_grpObj_of_local_group_laws_on_cover S I U A (fun i => (t i).A) ψ m n e hU hp
    (fun i T x y x₀ y₀ hx hy => ⟨by simpa only [Hom.mul_def] using hm i T x y x₀ y₀ hx hy,
      by simpa only [lift_fst_assoc, Hom.inv_def] using hn i T x y x₀ y₀ hx hy⟩) he
  have hab := GlobalTheory.T.isAbelianScheme_and_relDim_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp
  have hA : IsAbelianScheme A := hab.1 (fun i => (t i).ab)
  obtain ⟨L, hL, hrigL, hLi⟩ := GlobalTheory.T.exists_glue_rigidified_lineBundles_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab)
    (fun i => (t i).L) (fun i j => (u i j).A.left) a a' hB (fun i => (t i).isLB) (fun i => (t i).rigid)
    (fun i j => LBIso.trans (pull_isLB (t i).isLB _) (u i j).isLB (pull_isLB (t j).isLB _)
      (ha i j).2.1.symm (ha' i j).2.1)
  choose P hP using fun l => exists_section_of_compatible_local_sections hU hp (fun i => (t i).pt l) (fun i j => by
    rw [← Category.assoc, ← (ha i j).2.2.1 l, Category.assoc, (hB i j).w, ← Category.assoc,
      (ha' i j).2.2.1 l, Category.assoc])
  choose F hF using fun w => exists_endo_of_compatible_local_endos hU hp hB (fun i => (t i).act w) (fun i j => by
    rw [← Category.assoc, ← (ha i j).2.2.2 w, Category.assoc, (hB i j).w, ← Category.assoc,
      (ha' i j).2.2.2 w, Category.assoc])
  have h82 := GlobalTheory.T.torsion_and_isMonHom_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab)
  have hsym := GlobalTheory.T.symmetric_local_on_base_cover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi (fun i => (t i).sym)
  have hamp := GlobalTheory.T.relAmple_of_open_cover_grpPullback_relAmple S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) (fun i => (t i).ample)
  have hkt := GlobalTheory.T.thetaGroupKernel_trivial_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) (fun i => (t i).ktriv)
  have htor : ∀ l, P l ^ k = 1 := fun l =>
    h82.1 k (P l) (fun i => (t i).pt l) (fun i => hP l i) (fun i => (t i).torsion l)
  have hbij := GlobalTheory.T.torsionBasis_geometric_fibres_of_open_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab) g k P
    (fun i => (t i).pt) (fun i l => hP l i) (fun i => (t i).bij)
  have hunit : ∀ i, Units.map (U i).ι.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS ((U i).ι ≫ s) b.ζ :=
    fun i => hcompl_unit_property_of_isPrime (U i).ι s b.ζ
  have hpair : ∀ l l', Out.WeilIs A L k (P l) (P l') (unitS s b.ζ ^ Out.stdSymp g l l') := fun l l' =>
    GlobalTheory.T.weilIs_local_on_base_of_openCover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
      (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) k (P l) (P l') (fun i => (t i).pt l)
      (fun i => (t i).pt l') _ (fun i => hP l i) (fun i => hP l' i) (fun i => by
        rw [map_zpow, hunit i]
        exact (t i).pairing l l')
  have hhom : ∀ w, IsMonHom (F w) := fun w =>
    h82.2 (F w) (fun i => (t i).act w) (fun i => hF w i) (fun i => (t i).hom w)
  let t₀ : TObj g k J b s :=
    { A := A
      grp := inst
      ab := hA
      dim := hab.2 g (fun i => (t i).dim)
      L := L
      isLB := hL
      rigid := hrigL
      sym := hsym
      ample := hamp
      ktriv := hkt
      pt := P
      torsion := htor
      bij := hbij
      pairing := hpair
      act := F
      hom := hhom }
  exact ⟨t₀, fun i => ⟨ψ i, hgp i, hLi i, fun l => hP l i, fun w => hF w i⟩⟩

end GlobalTheory
