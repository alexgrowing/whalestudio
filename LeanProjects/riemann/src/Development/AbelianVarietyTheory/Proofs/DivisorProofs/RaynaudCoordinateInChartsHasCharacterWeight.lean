import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

namespace GlobalTheory.HeatConn.CoordWt

theorem isWt_xc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (W : Y.H.left.Opens), W ≤ xU Y α t → IsWt Y α W (rsT (xc Y α t).val W) := by
  intro R _ _ Q O _ _ _ oa Y α t W hW
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ W → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b W (rsT (xc Y α t).val W))) =
        gs b z (xU Y α t) (xc Y α t).val := by
    intro b hb z
    rw [valR, dif_pos hb, Iso.hom_inv_id_apply, rsT, dif_pos hW]
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z W (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hW (hb trivial) _
  have key : ∀ (xx : Over.mk (spMap φ) ⟶ Y.H), ⊤ ≤ xx.left ⁻¹ᵁ W → ∀ z J, Good Q.P.L z J →
      gs xx.left z (xU Y α t) (xc Y α t).val =
        (trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε xx.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (xx.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k))).val *
        (val ((Y.Φ _ xx).s α) (𝟙 _) z J).val := by
    intro xx hb z J hJ
    have hp := ((GlobalTheory.TorusModel.isPull_iff xx _ _).1 (Y.rep.1 _ _ xx (𝟙 _))).2 α z J hJ
    rw [Category.comp_id] at hp
    have hmem : xx.left z ∈ xU Y α t := hW (hb trivial)
    rw [gs_unit xx.left z _ hmem, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) xx.left z hmem (hJ.mem _ xx.left), Units.val_mul]
    congr 1
    exact congrArg Units.val hp.symm
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  have hφ : ∀ k, x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k = x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k :=
    fun k => by rw [gtφT_eq, ← Category.assoc, hqq, Category.assoc]
  have htr : ∀ z (J : (Sp S ⟶ Q.P.A.left) → Q.P.L.ι),
      trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x'.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) =
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) := by
    intro z J
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hφ k]
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a _ _ => a.elim) (fun k => k.elim)
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
    gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₂ z, germ _ hV₁ z, key x' hV₂ z J hJ, key x hV₁ z J hJ, htr,
    hc α z J hJ, show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial, Units.val_mul]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.HeatConn.CoordWt
