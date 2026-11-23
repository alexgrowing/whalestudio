import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitivStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfFramedPointOverIntegralStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.CoverPoint

theorem exists_finite_subfield {R F k : Type} [CommRing R] [Field F] [Field k] [Algebra F k] [Algebra.IsAlgebraic F k]
    {X : Scheme.{0}} (s : X ⟶ Sp R) [LocallyOfFiniteType s] (ρ : R →+* F) (p : Sp k ⟶ X)
    (hp : p ≫ s = spMap ((algebraMap F k).comp ρ)) :
    ∃ K : IntermediateField F k, FiniteDimensional F K ∧ ∃ q : Sp K ⟶ X, spMap (algebraMap K k) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint k))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(X, U) ⟶ CommRingCat.of k, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum k) y (IsLocalRing.closedPoint k)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(X, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom ((algebraMap F k).comp ρ) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap F k (ρ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(X, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType R Γ(X, U) from hft).out
  let S : Set k := (t.image f.hom : Finset k)
  let K := IntermediateField.adjoin F S
  refine ⟨K, IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (t : Set Γ(X, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin F S (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(X, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem epi_spMap {K k : Type} [Field K] [Field k] (f : K →+* k) : Epi (spMap f) := by
  have h1 : Flat (spMap f) := by
    let _ := f.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (show (algebraMap K k).Flat from
      RingHom.flat_algebraMap_iff.2 inferInstance)
  have h2 : Surjective (spMap f) := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_ext_lift_to_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (io₂ : d.c₂.F →+* T'.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T' io₂), IsExt y iT e y' ∧ T'.FinRes ∧ (∀ a : c.F, io₂ (d.eF a) = iT (io a)) ∧ (letI := (iT.comp io).toAlgebra; letI := io₂.toAlgebra; FrOver d y₂.1 y'.1) := by
  intro E _ _ _ H Dw l Xo c n d hd T io y hT
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  let j : d.c₂.F →+* c.F := d.eF.symm.toAlgHom.toRingHom
  have hj : ∀ a : c.F, j (d.eF a) = a := fun a => d.eF.symm_apply_apply a
  let k := AlgebraicClosure T.Fr
  have key : ∃ p : Sp k ⟶ d.Xo₂.X, p ≫ d.r = spMap (algebraMap T.Fr k) ≫ xOf y ∧
      p ≫ d.Xo₂.s = spMap ((algebraMap T.Fr k).comp
        ((io.comp j).comp (IntermediateField.inclusion d.c₂.le).toRingHom)) := by
    letI := io.toAlgebra
    letI : Algebra c.F k := ((algebraMap T.Fr k).comp io).toAlgebra
    letI : Algebra d.c₂.F k := ((algebraMap T.Fr k).comp (io.comp j)).toAlgebra
    let ψ : T.Fr →ₐ[c.F] k := { algebraMap T.Fr k with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T.Fr k ψ y.1
    obtain ⟨z₂, hz₂⟩ := hd.2.2.2.2.2.2.1 k (fun a => by
      change algebraMap T.Fr k (io (j (d.eF a))) = algebraMap T.Fr k (io a)
      rw [hj]) z
    exact ⟨z₂.x, hz₂.1.trans hz.1, z₂.x_over⟩
  obtain ⟨p, hp1, hp2⟩ := key
  haveI := d.Xo₂.smooth
  haveI : Smooth d.Xo₂.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨K, hK, q, hq⟩ := exists_finite_subfield d.Xo₂.s _ p hp2
  haveI := epi_spMap (algebraMap K k)
  have hKk : (algebraMap K k).comp (algebraMap T.Fr K) = algebraMap T.Fr k := rfl
  have hq1 : q ≫ d.r = spMap (algebraMap T.Fr K) ≫ xOf y := by
    rw [← cancel_epi (spMap (algebraMap K k)), ← Category.assoc, hq, hp1, ← Category.assoc, spMap_comp', hKk]
  have hq2 : q ≫ d.Xo₂.s = spMap ((algebraMap T.Fr K).comp
      ((io.comp j).comp (IntermediateField.inclusion d.c₂.le).toRingHom)) := by
    rw [← cancel_epi (spMap (algebraMap K k)), ← Category.assoc, hq, hp2, spMap_comp']
    rfl
  obtain ⟨T', iT, e, ψ, φ, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T K
  have hψ' : ψ.toRingHom.comp (algebraMap T.Fr K) = iT := RingHom.ext hψ
  obtain ⟨⟨y', hy'⟩, hx⟩ := GlobalTheory.T.exists_integralFramedPoint_baseChange_cdvr_transitive E H Dw l Xo c T T' io y iT e he hv
  have hx' := (hx y' hy').1
  let io₂ : d.c₂.F →+* T'.Fr := iT.comp (io.comp j)
  have hio : ∀ a : c.F, io₂ (d.eF a) = iT (io a) := fun a => by
    change iT (io (j (d.eF a))) = _
    rw [hj]
  letI := (iT.comp io).toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨y₂, -, hy₂⟩ := (GlobalTheory.frames_lift_to_cover hL E H Dw l Xo c n d).1 T'.Fr hio y'.1
    (spMap ψ.toRingHom ≫ q)
    (by rw [Category.assoc, hq1, ← Category.assoc, spMap_comp', hψ']; exact hx'.symm)
    (by rw [Category.assoc, hq2, spMap_comp', ← RingHom.comp_assoc, hψ']; rfl)
  exact ⟨T', iT, e, y', io₂, ⟨y₂, GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y₂,
    GlobalTheory.T.integral_of_framed_point_over_integral E H Dw l Xo c n d T' (iT.comp io) io₂ y' hio y₂ hy₂⟩, hy', hfin hT, hio, hy₂⟩

end GlobalTheory.CoverPoint
