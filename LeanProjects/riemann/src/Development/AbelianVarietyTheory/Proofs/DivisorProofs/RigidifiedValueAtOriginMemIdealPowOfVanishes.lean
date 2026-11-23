import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigVan

theorem stalkMap_gs {X Y Z : Scheme.{0}} (t : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (t z) ∈ U)
    (a : Γ(X, U)) : (t.stalkMap z).hom (gs r (t z) U a) = gs (t ≫ r) z U a := by
  rw [gs_eq r (t z) U h, gs_eq (t ≫ r) z U h]
  exact Scheme.Hom.germ_stalkMap_apply t (r ⁻¹ᵁ U) z h _

theorem stalkMap_stalkOf {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (z : Sp S) (v : R) :
    ((Spec.map (CommRingCat.ofHom φ)).stalkMap z).hom (stalkOf ((Spec.map (CommRingCat.ofHom φ)) z) v) =
      stalkOf z (φ v) := by
  have e := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  refine (Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) ⊤ z trivial _).trans ?_
  exact congrArg ((Sp S).presheaf.germ ⊤ z trivial).hom e.symm

theorem eq_zero_of_stalkOf {S : Type} [CommRing S] (w : S) (h : ∀ z : Sp S, stalkOf z w = 0) : w = 0 := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom w = 0 := by
    apply TopCat.Presheaf.section_ext (Sp S).sheaf ⊤
    intro x hx
    exact (h x).trans (map_zero _).symm
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom h1
  simpa using h2

end GlobalTheory.Mum.OrigVan

namespace GlobalTheory.Mum
open OrigVan

theorem origVal_mem_of_vanMod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (α : D.X)
    (b : D.SecB k α) (v : R) (e : ℕ), OrigVal D b v → VanMod I b e → v ∈ I ^ (e + 1) := by
  intro R _ _ I D k α b v e hO hV
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_zero_of_stalkOf _ fun z => ?_
  choose J hJ using fun χ : Sp R ⟶ D.P.A.left => exists_chart D.P.isLB (χ (thick R I e z))
  have hG : Good D.P.L (thick R I e z) J := hJ
  have h1 := congrArg ((thick R I e).stalkMap z).hom (hO (thick R I e z) J hG)
  have hm := hG.mem (D.famφB α) (unitW D.P.A)
  have hu : unitW D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w (η[D.P.A])
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ pullback D.P.A.hom (thick R I e) :=
    pullback.lift (thick R I e ≫ unitW D.P.A) (𝟙 _) (by rw [Category.assoc, hu, Category.comp_id, Category.id_comp])
  have hs : s ≫ pullback.fst D.P.A.hom (thick R I e) = thick R I e ≫ unitW D.P.A := pullback.lift_fst _ _ _
  have hm' : (s ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈
      LB.wchart D.P.L (D.famφB α) (fun k => J (unitW D.P.A ≫ D.famφB α k)) := by
    rw [hs]; exact hm
  have h0 : ((thick R I e).stalkMap z).hom (sval b (unitW D.P.A) (thick R I e z) J) = 0 := by
    refine (stalkMap_gs (thick R I e) (unitW D.P.A) z _ hm _).trans ?_
    rw [← hs]
    refine (gs_pull s _ z _ hm' _).symm.trans ?_
    refine (congrArg (gs s z _) (hV _)).trans ?_
    refine (gs_eq s z _ hm' _).trans ?_
    rw [map_zero, map_zero]
  rw [h0, map_mul, map_pow, stalkMap_stalkOf] at h1
  exact (((Units.isUnit _).map _).pow k).mul_left_eq_zero.1 h1.symm

end GlobalTheory.Mum
