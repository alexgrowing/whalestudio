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
namespace GlobalTheory.Mum.OrigValPull

theorem gs_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)) :
    gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h, gs_eq f z (g ⁻¹ᵁ U) h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _).symm

theorem gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    (gm (f ≫ g) z U a).val = (f.stalkMap z).hom (gm g (f z) U a).val := by
  rw [← gs_unit (f ≫ g) z U h, ← gs_unit g (f z) U h, gs_comp f g z U h]

theorem stalkMap_stalkOf {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (z : Sp R') (v : R) :
    ((spMap φ).stalkMap z).hom (stalkOf (spMap φ z) v) = stalkOf z (φ v) := by
  have h := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine (Scheme.Hom.germ_stalkMap_apply (spMap φ) ⊤ z trivial _).trans ?_
  exact congrArg ((Sp R').presheaf.germ ⊤ z trivial).hom h.symm

theorem unit_fam {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (α : D.X) (κ : Fin 4) :
    unitW D.P.A ≫ D.famφB α κ = ![unitW D.P.A, (D.c α).left, (D.c α).left, unitW D.P.A] κ := by
  have u : η[D.P.A] ≫ toUnit D.P.A = 𝟙 _ := Subsingleton.elim _ _
  fin_cases κ
  · exact Category.comp_id _
  · show (η[D.P.A] ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (D.c α).left
    congr 1
    show η[D.P.A] ≫ (lift (𝟙 D.P.A) (toUnit _ ≫ D.c α) ≫ μ[D.P.A]) = _
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, u, Category.id_comp]
    have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Sp R)))) (D.c α)
    simpa using this
  · show (η[D.P.A] ≫ toUnit _ ≫ D.c α).left = (D.c α).left
    rw [← Category.assoc, u, Category.id_comp]
  · show (η[D.P.A] ≫ toUnit _ ≫ η[D.P.A]).left = η[D.P.A].left
    rw [← Category.assoc, u, Category.id_comp]

theorem origVal_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (x : D'.X) (b : D.SecB k (hD.xe x)) (b' : D'.SecB k x) (v : R), PullB hD x b b' → OrigVal D b v → OrigVal D' b' (φ v) := by
  intro R R' _ _ _ _ φ D D' hD k x b b' v hP hO z J' hJ'
  choose J hJ using fun χ : Sp R ⟶ D.P.A.left => exists_chart D.P.isLB (χ (spMap φ z))
  have hJ : Good D.P.L (spMap φ z) J := hJ
  have he : unitW D'.P.A ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = spMap φ ≫ unitW D.P.A := hD.he
  have hc : ∀ κ, (unitW D'.P.A ≫ D'.famφB x κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
      spMap φ ≫ unitW D.P.A ≫ D.famφB (hD.xe x) κ := fun κ => by
    rw [unit_fam, unit_fam]
    fin_cases κ
    exacts [he, hD.c_pr x, hD.c_pr x, he]
  have h₁ := hP (Sp R') (unitW D'.P.A) z (fun κ => J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))
    (fun κ => J' (unitW D'.P.A ≫ D'.famφB x κ))
    (fun κ => (congrArg (fun q : Sp R' ⟶ D.P.A.left => q z ∈ D.P.L.U (J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))) (hc κ)).mpr
      (hJ _)) (fun κ => hJ' _)
  have hprod : (∏ κ, gw hD.w (unitW D'.P.A ≫ D'.famφB x κ) z (J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))
      (J' (unitW D'.P.A ≫ D'.famφB x κ)) ^ (DegPre.famε k) κ) =
      gw hD.w (unitW D'.P.A) z (J (unitW D.P.A)) (J' (unitW D'.P.A)) ^ k := by
    simp only [unit_fam, Fin.prod_univ_four, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [_root_.mul_assoc (_ ^ _), ← zpow_add, add_neg_cancel, zpow_zero, _root_.mul_one, ← zpow_add, sub_add_cancel,
      zpow_natCast]
  have h₂ := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le _ _ hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig (Sp R') (idW R') z
    (fun _ => J (idW R ≫ eSec D.P.A)) (fun _ => J' (idW R' ≫ eSec D'.P.A))
    (fun _ => (congrArg (fun q : Sp R' ⟶ D.P.A.left => q z ∈ D.P.L.U (J (idW R ≫ eSec D.P.A))) he).mpr
      (hJ _)) (fun _ => hJ' _)
  have h₃ : ((spMap φ).stalkMap z).hom (val D.rig (idW R) (spMap φ z) J).val =
      (gw hD.w (unitW D'.P.A) z (J (unitW D.P.A)) (J' (unitW D'.P.A))).val * (val D'.rig (idW R') z J').val := by
    have i : idW R ≫ eSec D.P.A = unitW D.P.A := Category.id_comp _
    have i' : idW R' ≫ eSec D'.P.A = unitW D'.P.A := Category.id_comp _
    have c : spMap φ ≫ idW R = idW R' ≫ specOf φ := (Category.comp_id _).trans (Category.id_comp _).symm
    refine (gm_comp (spMap φ) (idW R) z _ (hJ.mem (fun _ : PUnit => eSec D.P.A) (idW R)) _).symm.trans ?_
    rw [c, ← Units.val_mul]
    refine congrArg Units.val (h₂.trans (congrArg₂ (· * ·) ?_ rfl))
    rw [Fintype.prod_unique, zpow_one, i, i']
  have h₄ := congrArg ((spMap φ).stalkMap z).hom (hO (spMap φ z) J hJ)
  rw [map_mul, map_pow, stalkMap_stalkOf, h₃] at h₄
  have h₅ := (gs_comp (spMap φ) (unitW D.P.A) z _ (hJ.mem (D.famφB (hD.xe x)) (unitW D.P.A)) _).trans h₄
  rw [he, hprod] at h₁
  have h₆ := h₁.symm.trans h₅
  rw [mul_pow, _root_.mul_left_comm, ← Units.val_pow_eq_pow_val] at h₆
  exact (Units.mul_right_inj _).1 h₆

end GlobalTheory.Mum.OrigValPull
