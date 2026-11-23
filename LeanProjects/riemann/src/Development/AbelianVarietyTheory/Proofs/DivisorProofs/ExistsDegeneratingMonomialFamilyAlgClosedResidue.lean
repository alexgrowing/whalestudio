import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFamThrough
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartGeo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem nontrivial_of_not_mem_range {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V)
    (C : MonoFam Xo c φ V) {S T : Scheme.{0}} (s : S ⟶ T) [IsSeparated s] (j : Xo.XF c ⟶ S) (ξV : Sp V ⟶ S)
    (hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ s = g ≫ s)
    (hy : C.y ≫ j = jK V ≫ ξV) (hx : ξV (closedPoint V) ∉ Set.range j) : Nontrivial C.P.D.toPre.X := by
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  haveI : IsEmpty (Fin C.m) := ⟨fun i =>
    C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => by
      rw [Subsingleton.elim a 0]; simp)⟩
  have hprod : ∏ i, C.s i = 1 := by simp [Finset.univ_eq_empty]
  obtain ⟨yo, -, -, -, hg⟩ := GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ V hV C
  let A := Localization.Away (∏ i, C.s i)
  let e : V ≃ₐ[V] A := IsLocalization.atUnit V A (∏ i, C.s i) (by rw [hprod]; exact isUnit_one)
  let h : A →+* V := e.symm.toRingEquiv.toRingHom
  have hcomp : h.comp (algebraMap V A) = RingHom.id V := by
    ext r
    show e.symm (algebraMap V A r) = r
    exact e.symm.commutes r
  have hid : spMap h ≫ spMap (algebraMap V A) = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  have hψ : jK V ≫ spMap h ≫ yo = C.y := by
    rw [← Category.assoc]
    exact hg _ (by rw [Category.assoc, hid, Category.comp_id])
  have hgen : jK V ≫ (spMap h ≫ yo) ≫ j = jK V ≫ ξV := by
    rw [← Category.assoc, hψ, hy]
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have heq : (spMap h ≫ yo) ≫ j = ξV :=
    ext_of_isDominant_of_isSeparated s (hs _ _ hgen) (jK V) hgen
  exact hx ⟨(spMap h ≫ yo) (closedPoint V), by
    show ((spMap h ≫ yo) ≫ j) (closedPoint V) = _
    rw [heq]⟩

end GlobalTheory.UChartGeo

namespace GlobalTheory.UChartGeo

set_option maxHeartbeats 1000000 in

theorem exists_monoFam_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hV, hy, hxV⟩ :=
    GlobalTheory.UChartTrait.exists_monoFam_through Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨Nn, ιP, hci, hι⟩ := hU.2.2.2.2.1.2.1
  haveI : IsSeparated (π ≫ zs) := by rw [← hι]; infer_instance
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ π ≫ zs = g ≫ π ≫ zs := fun f g hfg =>
    ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) (jK V) (by
      rw [← Category.assoc, hfg, Category.assoc])
  have hX : Nontrivial C.P.D.toPre.X :=
    nontrivial_of_not_mem_range hV C (π ≫ zs) j ξV hs hy (hxV ▸ hx)
  obtain ⟨y0, hy0⟩ := exists_ne (0 : C.P.D.toPre.X)
  obtain ⟨i0, -⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy0
  have hnf : ¬ IsField V := by
    intro hf
    have hm := C.s_mem i0
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).1 hf, Ideal.mem_bot] at hm
    exact C.s_ne_zero i0 hm
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  obtain ⟨W, _, _, _, ρ, hcomp, hac, hinj, hloc⟩ := GlobalTheory.T.exists_complete_dvr_algClosed_residue_injective_local V hnf ⟨C.b.comp (algebraMap ℚ c.F)⟩
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hne : ∀ k, ρ (C.s k) ≠ 0 := fun k h0 => C.s_ne_zero k (hinj (h0.trans (map_zero ρ).symm))
  choose w u hwu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne k) hϖ
  have hW : GlobalTheory.UU.CDVR W := ⟨inferInstance, hcomp, inferInstance⟩
  obtain ⟨t, P, e, be, -, htK, hbe, -, hmono, -⟩ := trait_pull C hV W hW ϖ ρ hinj hloc w u hwu
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp ρ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  obtain ⟨gam, hgam⟩ : ∃ gam : FractionRing V →+* FractionRing W,
      gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ρ :=
    ⟨IsFractionRing.lift hinj', RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj' r⟩
  have hκ : spMap gam ≫ jK V = jK W ≫ spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hgam]
  obtain ⟨tK, h1, h2⟩ := htK (spMap gam) hκ
  have hover : (spMap gam ≫ C.y) ≫ pullback.snd _ _ = jK W ≫ spMap (ρ.comp C.b) := by
    rw [Category.assoc, C.y_over, ← Category.assoc, hκ, Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom C.b) (CommRingCat.ofHom ρ)).symm
  let F : Fam Xo c W := ⟨ρ.comp C.b, t, P, spMap gam ≫ C.y, hover, ⟨tK, h1, h2⟩⟩
  let β : LinearMap.BilinForm ℤ P.D.toPre.X := ∑ k, (w k : ℤ) • pull e.toLinearMap (C.δ k)
  have hβ : β ∈ balForms H.bar P.D.toPre.X :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pull_mem _ (C.cone.mem k))
  have hbeq : be = (l.M' : ℤ) • β := by
    rw [hbe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext a b
    simp only [LinearMap.smul_apply, pull_apply, smul_eq_mul]
    ring
  have hmono' : IsMonomial F.P.D.toPre ![ϖ] ![(l.M' : ℤ) • β] := hbeq ▸ hmono
  have hϖm : ϖ ∈ maximalIdeal W := (mem_maximalIdeal _).2 hϖ.not_isUnit
  obtain ⟨C', hC'⟩ := F.exists_monoFam hpf hϖm hβ hmono'
  have hyC : C'.toFam.y = spMap gam ≫ C.y := by rw [hC']
  refine ⟨W, inferInstance, inferInstance, inferInstance, C', spMap ρ ≫ ξV,
    ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩, hac, ?_, ?_, ?_⟩
  · rw [hC']
    exact e.symm.injective.nontrivial
  · show C'.toFam.y ≫ j = _
    rw [hyC, Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · show ξV (spMap ρ (closedPoint W)) = x
    have hcl : spMap ρ (closedPoint W) = closedPoint V := IsLocalRing.comap_closedPoint ρ
    rw [hcl, hxV]

end GlobalTheory.UChartGeo
