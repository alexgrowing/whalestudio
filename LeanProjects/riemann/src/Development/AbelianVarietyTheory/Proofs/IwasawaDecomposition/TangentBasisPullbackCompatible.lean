import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieFrameField

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] (tK : SAB H (Sp K))

def ptMap {S : Type} [CommRing S] (y : Sp S ⟶ Sp K) : K →+* S := (Spec.preimage y).hom

theorem spMap_ptMap {S : Type} [CommRing S] (y : Sp S ⟶ Sp K) : spMap (ptMap y) = y := Spec.map_preimage y

theorem ptMap_comp {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (y : Sp S ⟶ Sp K) (y' : Sp S' ⟶ Sp K)
    (e : spMap φ ≫ y = y') : ptMap y' = φ.comp (ptMap y) := by
  have h : spMap (φ.comp (ptMap y)) = spMap (ptMap y') := by
    rw [spMap_ptMap y', ← e]
    conv_rhs => rw [← spMap_ptMap y]
    exact Spec.map_comp _ _
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h).symm

variable {tK} in

theorem exists_basis {d : ℕ} {v : Fin d → (epsR K ⟶ tK.G)} (hv : IsLieBasis v) {S : Type} [CommRing S]
    (f : K →+* S) (x : Sp S ⟶ Sp K) (hx : spMap f = x) :
    ∃ b : Module.Basis (Fin d) S (TanM x tK.G), ∀ j, (tv (b j)).left = spMap (dualMap f) ≫ (v j).left := by
  subst hx
  have hp : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' tK (spMap f)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap f) tK
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨m⟩⟩ := hp
  obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange K S f tK.G t'.G m.φ m.cart tK.semi.smooth d v hv
  let u : Fin d → TanM (spMap f) tK.G := fun j =>
    mkT (pushHom m.cart (epsR S) (v' j)) ((PullbackSections.isTangent_iff m.cart _).1 (hb.1 j))
  have hcomb : ∀ (a : Fin d → S) (w : epsR S ⟶ t'.G), IsLieComb a v' w ↔
      pushHom m.cart (epsR S) w = tv (∑ i, a i • u i) := fun a w => by
    rw [PullbackSections.isLieComb_iff m.cart, tv_sum']
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination S u) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj m.cart (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff m.cart p).2 (by rw [hp]; exact tv_mem W)
    refine (existsUnique_congr fun a => ?_).1 (hb.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (tanM_ext e).symm, fun e => by rw [e]⟩
  let e := LinearEquiv.ofBijective _ hbij
  have he : ∀ j, (Pi.basisFun S (Fin d)).map e j = u j := fun j => by
    simp [e, Fintype.linearCombination_apply_single]
  exact ⟨(Pi.basisFun S (Fin d)).map e, fun j => by rw [he]; exact hv' j⟩

theorem exists_lieFrame (tK : SAB H (Sp K)) :
    ∃ (d : ℕ) (B : ∀ (S : Type) [CommRing S] (y : Sp S ⟶ Sp K),
      Module.Basis (Fin d) S (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM y tK.G)),
      ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (y : Sp S ⟶ Sp K) (y' : Sp S' ⟶ Sp K)
        (e : spMap φ ≫ y = y') (j : Fin d), tanPull φ e (B S y j) = B S' y' j := by
  obtain ⟨d, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis tK.G tK.semi.smooth
  have hB := fun (S : Type) [CommRing S] (y : Sp S ⟶ Sp K) => exists_basis hv (ptMap y) y (spMap_ptMap y)
  refine ⟨d, fun S _ y => (hB S y).choose, fun S S' _ _ φ y y' e j => ?_⟩
  apply tan_ext_left
  rw [tanPull_left, (hB S y).choose_spec j, (hB S' y').choose_spec j, ptMap_comp φ y y' e, GlobalTheory.FlagMod.dualMap_comp,
    ← spMap_comp', Category.assoc]

theorem lieFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    (tK : SAB H (Sp K)), ∃ (d : ℕ) (B : ∀ (S : Type) [CommRing S] (y : Sp S ⟶ Sp K),
      Module.Basis (Fin d) S (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM y tK.G)),
      ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (y : Sp S ⟶ Sp K) (y' : Sp S' ⟶ Sp K)
        (e : spMap φ ≫ y = y') (j : Fin d), tanPull φ e (B S y j) = B S' y' j := fun _ _ _ _ _ _ _ tK => exists_lieFrame tK

end GlobalTheory.LieFrameField
