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
namespace GlobalTheory.Mum.OrigValExists

theorem mem_of_closed {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : f (closedPoint R) ∈ U) (z : Sp R) : f z ∈ U := by
  have : f ⁻¹ᵁ U = ⊤ := (closedPoint_mem_iff (f ⁻¹ᵁ U)).1 h
  show z ∈ f ⁻¹ᵁ U
  rw [this]; trivial

theorem exists_stalkOf {R : Type} [CommRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : ∀ z, f z ∈ U) (a : Γ(X, U)) : ∃ r : R, ∀ z, gs f z U a = stalkOf z r := by
  have hle : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ U := fun z _ => h z
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE hle).op).hom ((f.app U).hom a)), fun z => ?_⟩
  rw [gs_eq f z U (h z)]
  have e : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply x
  refine Eq.trans ?_ (congrArg ((Sp R).presheaf.germ ⊤ z trivial).hom (e _)).symm
  exact (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE hle) z trivial _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (α : D.X)

theorem unit_fam_zero : unitW D.P.A ≫ D.famφB α 0 = idW R ≫ eSec D.P.A :=
  (Category.comp_id _).trans (Category.id_comp _).symm

theorem unit_fam_one : unitW D.P.A ≫ D.famφB α 1 = unitW D.P.A ≫ D.famφB α 2 := by
  change η[D.P.A].left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = η[D.P.A].left ≫ (toUnit D.P.A ≫ D.c α).left
  rw [← Over.comp_left, ← Over.comp_left]; congr 1
  simp only [padd, comp_lift_assoc, Category.comp_id]
  have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Sp R)))) (η[D.P.A] ≫ toUnit D.P.A ≫ D.c α)
  rwa [Category.id_comp] at this

theorem unit_fam_three : unitW D.P.A ≫ D.famφB α 3 = idW R ≫ eSec D.P.A := by
  refine Eq.trans ?_ (Category.id_comp _).symm
  change η[D.P.A].left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = η[D.P.A].left
  rw [← Over.comp_left]; congr 1
  rw [← Category.assoc, Subsingleton.elim (η[D.P.A] ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem trF_unit (k : ℕ) (z : Sp R) (J I : (Sp R ⟶ D.P.A.left) → D.P.L.ι) :
    trF (L := D.P.L) (D.famφB α) (DegPre.famε k) (unitW D.P.A) z (fun i => J (unitW D.P.A ≫ D.famφB α i))
      (fun i => I (unitW D.P.A ≫ D.famφB α i)) =
    trF (L := D.P.L) (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) (idW R) z (fun _ => J (idW R ≫ eSec D.P.A))
      (fun _ => I (idW R ≫ eSec D.P.A)) ^ k := by
  let h : (Sp R ⟶ D.P.A.left) → ((Sp R).presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (I ψ)) (D.P.L.g (J ψ) (I ψ))
  show ∏ i, h (unitW D.P.A ≫ D.famφB α i) ^ DegPre.famε k i = (∏ _i : PUnit, h (idW R ≫ eSec D.P.A) ^ (1 : ℤ)) ^ k
  rw [Fin.prod_univ_four, unit_fam_zero, unit_fam_one, unit_fam_three, Fintype.prod_unique]
  generalize h (idW R ≫ eSec D.P.A) = A
  generalize h (unitW D.P.A ≫ D.famφB α 2) = B
  show A ^ ((k : ℤ) - 1) * B ^ (1 : ℤ) * B ^ (-1 : ℤ) * A ^ (1 : ℤ) = (A ^ (1 : ℤ)) ^ k
  rw [zpow_sub_one, zpow_natCast, zpow_neg, zpow_one, zpow_one, mul_inv_cancel_right, inv_mul_cancel_right]

end GlobalTheory.Mum.OrigValExists

namespace GlobalTheory.Mum
open OrigValExists

theorem exists_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ v : R, OrigVal D b v := by
  intro R _ _ _ D k α b
  obtain ⟨I, hI₀, -⟩ := exists_good D.P.L D.P.isLB (Z := Sp R) (closedPoint R) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hI : ∀ z, Good D.P.L z I := fun z ψ => mem_of_closed ψ _ (hI₀ ψ) z
  obtain ⟨a, ha⟩ := exists_stalkOf (unitW D.P.A) _ (fun z => (hI z).mem (D.famφB α) (unitW D.P.A))
    (b.f (fun i => I (unitW D.P.A ≫ D.famφB α i)))
  obtain ⟨u, hu⟩ := exists_stalkOf (idW R) _ (fun z => (hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R))
    ((D.rig.s (fun _ => I (idW R ≫ eSec D.P.A)))⁻¹).val
  refine ⟨a * u ^ k, fun z J hJ => ?_⟩
  have e₁ : sval b (unitW D.P.A) z J = _ * sval b (unitW D.P.A) z I :=
    sec_trans b (unitW D.P.A) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₂ : val D.rig (idW R) z J = _ * val D.rig (idW R) z I :=
    gen_trans D.rig_gen (idW R) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₃ : sval b (unitW D.P.A) z I = stalkOf z a := ha z
  have e₄ : stalkOf z u = ((val D.rig (idW R) z I)⁻¹).val :=
    (hu z).symm.trans ((gs_unit (idW R) z _ ((hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R)) _).trans
      (congrArg Units.val (map_inv _ _)))
  rw [e₁, e₂, e₃, trF_unit, map_mul, map_pow, e₄]
  generalize trF (K := PUnit) _ _ _ _ _ _ = A
  generalize val D.rig (idW R) z I = B
  rw [_root_.mul_assoc, ← mul_pow, ← Units.val_mul, _root_.mul_comm A B, inv_mul_cancel_left, Units.val_pow_eq_pow_val, _root_.mul_comm]

end GlobalTheory.Mum
