import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionFlatLocallyQuasiFiniteStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicSplittingExtensionStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsSplitField

open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem exists_poly_split_torsion {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] (xK : Sp K ⟶ X) (q : ℕ) (hq : q ≠ 0) :
    ∃ f : Polynomial K, f ≠ 0 ∧ ∀ (L : Type) [Field L] [Algebra K L], (f.map (algebraMap K L)).Splits →
      ∀ (Ω : Type) [Field Ω] (j : L →+* Ω) (b : Sp Ω ⟶ X), b = spMap (j.comp (algebraMap K L)) ≫ xK →
        ∀ w : Over.mk b ⟶ t.G, w ^ q = 1 → ∃ w₀ : Sp L ⟶ t.G.left, spMap j ≫ w₀ = w.left := by
  classical
  have hsemi := t.semi
  have := hsemi.quasiCompact
  have := hsemi.separated
  have hLQF : LocallyQuasiFinite (torsion t.G q).hom := (GlobalTheory.T.torsion_flat_locallyQuasiFinite X t.G t.semi q hq).2
  have hcl : IsClosedImmersion η[t.G].left := by
    have : IsClosedImmersion (η[t.G].left ≫ t.G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ t.G.hom
  have : IsClosedImmersion (torsion.ι t.G q).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GlobalTheory.GrpTangent.isPullback_torsion t.G q).flip hcl
  have hQC : QuasiCompact (torsion t.G q).hom := by
    rw [← Over.w (torsion.ι t.G q)]; infer_instance
  obtain ⟨⟨x0, ψ⟩, hxK⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective xK
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hxK
  have hfib : ((torsion t.G q).hom ⁻¹' {x0}).Finite := (torsion t.G q).hom.finite_preimage_singleton x0
  have hgen : ∀ z : (torsion t.G q).left, letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra;
      ∃ s : Finset ((torsion t.G q).left.residueField z),
        Submodule.span (X.residueField ((torsion t.G q).hom z)) (s : Set ((torsion t.G q).left.residueField z)) = ⊤ := by
    intro z
    letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
    have : Module.Finite (X.residueField ((torsion t.G q).hom z)) ((torsion t.G q).left.residueField z) :=
      GlobalTheory.T.residueFieldMap_finite_of_quasiFinite _ z
    exact Module.Finite.fg_top
  choose s hs using hgen
  have hint : ∀ (z : (torsion t.G q).left) (c : (torsion t.G q).left.residueField z),
      letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra;
      IsIntegral (X.residueField ((torsion t.G q).hom z)) c := by
    intro z c
    letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
    have : Module.Finite (X.residueField ((torsion t.G q).hom z)) ((torsion t.G q).left.residueField z) :=
      GlobalTheory.T.residueFieldMap_finite_of_quasiFinite _ z
    exact Algebra.IsIntegral.isIntegral c
  let P : ∀ z : (torsion t.G q).left, (torsion t.G q).left.residueField z → Polynomial K := fun z c =>
    if h : (torsion t.G q).hom z = x0 then
      letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
      (minpoly (X.residueField ((torsion t.G q).hom z)) c).map ((X.residueFieldCongr h).hom ≫ ψ).hom
    else 1
  obtain ⟨f, hfdef⟩ : ∃ f : Polynomial K, f = ∏ z ∈ hfib.toFinset, ∏ c ∈ s z, P z c := ⟨_, rfl⟩
  have hf0 : f ≠ 0 := by
    rw [hfdef, Finset.prod_ne_zero_iff]; intro z _; rw [Finset.prod_ne_zero_iff]; intro c _
    simp only [P]; split_ifs with h
    · letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
      exact ((minpoly.monic (hint z c)).map _).ne_zero
    · exact one_ne_zero
  refine ⟨f, hf0, ?_⟩
  intro L _ _ hspl Ω _ j b hb w hw
  obtain ⟨v, hv⟩ : ∃ v : Over.mk b ⟶ torsion t.G q, v ≫ torsion.ι t.G q = w :=
    ⟨pullback.lift w (toUnit _) (by rw [GlobalTheory.GrpTangent.comp_mulN, hw, Hom.one_def]), pullback.lift_fst _ _ _⟩
  obtain ⟨⟨z, φ⟩, hvz⟩ := (Scheme.SpecToEquivOfField Ω (torsion t.G q).left).symm.surjective v.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hvz
  have hb' : Spec.map ((torsion t.G q).hom.residueFieldMap z ≫ φ) ≫ X.fromSpecResidueField ((torsion t.G q).hom z) =
      Spec.map (ψ ≫ CommRingCat.ofHom (j.comp (algebraMap K L))) ≫ X.fromSpecResidueField x0 := by
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, hvz]
    have h1 := Over.w v
    simp only [Over.mk_hom] at h1
    rw [h1, hb, Spec.map_comp, Category.assoc, hxK]
  obtain ⟨e, he⟩ := GlobalTheory.SS.residue_embedding_unique _ _ hb'
  have hzf : z ∈ hfib.toFinset := by simpa using e
  letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
  have hcomp : (j.comp (algebraMap K L)).comp ((X.residueFieldCongr e).hom ≫ ψ).hom =
      φ.hom.comp ((torsion t.G q).hom.residueFieldMap z).hom := by
    have := congrArg CommRingCat.Hom.hom he
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this
    rw [this]; rfl
  have hroot : ∀ c ∈ s z, φ.hom c ∈ j.fieldRange := by
    intro c hc
    have hP : ((P z c).map (j.comp (algebraMap K L))).IsRoot (φ.hom c) := by
      simp only [P, dif_pos e, Polynomial.map_map]
      rw [hcomp, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← RingHom.algebraMap_toAlgebra
        ((torsion t.G q).hom.residueFieldMap z).hom, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hdvd : P z c ∣ f := by
      rw [hfdef]
      exact (Finset.dvd_prod_of_mem _ hc).trans (Finset.dvd_prod_of_mem (fun z => ∏ c ∈ s z, P z c) hzf)
    have hF : ((f.map (algebraMap K L)).map j).IsRoot (φ.hom c) := by
      rw [Polynomial.map_map]
      exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hP
    exact RingHom.mem_fieldRange.2 (RingHom.mem_range.1 (hspl.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) hF))
  have hall : ∀ c, φ.hom c ∈ j.fieldRange := by
    intro c
    have hc : c ∈ Submodule.span (X.residueField ((torsion t.G q).hom z)) (s z : Set _) := by rw [hs z]; trivial
    induction hc using Submodule.span_induction with
    | mem x hx => exact hroot x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hx
      have h2 := congrArg (fun h => h a) hcomp
      simp only [RingHom.comp_apply] at h2
      rw [RingHom.algebraMap_toAlgebra, ← h2]
      exact ⟨_, rfl⟩
  let e' := j.rangeRestrictFieldEquiv
  let g' : (torsion t.G q).left.residueField z →+* L := e'.symm.toRingHom.comp (φ.hom.codRestrict j.fieldRange hall)
  have hg' : CommRingCat.ofHom g' ≫ CommRingCat.ofHom j = φ := by
    ext c
    exact congrArg Subtype.val (e'.apply_symm_apply ⟨φ.hom c, hall c⟩)
  refine ⟨Spec.map (CommRingCat.ofHom g') ≫ (torsion t.G q).left.fromSpecResidueField z ≫ (torsion.ι t.G q).left, ?_⟩
  rw [← hv, Over.comp_left, ← hvz, spMap, ← Category.assoc, ← Spec.map_comp, hg', Category.assoc]

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem splitTors_finite_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x : Sp A ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ SplitTors t (spMap (algebraMap A A') ≫ x) q := by
  intro E _ _ _ H X _ t A _ _ _ _ _ x q hq
  obtain ⟨f, hf0, hf⟩ := exists_poly_split_torsion t (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ x) q hq
  obtain ⟨A', i1, i2, i3, σ, hfin, hinj, hic, hζ, hspl, hcomm⟩ := GlobalTheory.T.exists_cyclotomic_splitting_extension A f hf0 q hq
  refine ⟨A', i1, i2, i3, hfin, hinj, hic, hζ, ?_⟩
  intro Ω _ io w hw
  letI : Algebra (FractionRing A) (FractionRing A') := σ.toAlgebra
  refine hf (FractionRing A') (by simpa [RingHom.algebraMap_toAlgebra] using hspl) Ω io _ ?_ w hw
  rw [RingHom.algebraMap_toAlgebra, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', RingHom.comp_assoc,
    RingHom.comp_assoc, hcomm]

end GlobalTheory.TorsSplitField
