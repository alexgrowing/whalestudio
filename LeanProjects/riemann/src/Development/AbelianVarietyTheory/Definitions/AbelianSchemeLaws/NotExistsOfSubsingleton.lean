import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsIsLocallyFreeDataUnique

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
namespace GlobalTheory.AbLaw.LbSheafModel
open GlobalTheory.LB
variable {X X' : Scheme.{0}}

def noChart (X : Scheme.{0}) : LB X := ⟨PEmpty, fun i => i.elim, fun i => i.elim⟩

theorem triv_noChart : Triv (noChart X) := ⟨⟨fun i => i.elim⟩, fun i => i.elim⟩

theorem bijective_app {F G : X.Modules} (e : F ≅ G) (V : X.Opens) :
    Function.Bijective (e.hom.app V) := ConcreteCategory.bijective_of_isIso (e.hom.app V)

theorem not_exists_of_subsingleton [Nonempty X] (F : X.Modules) (hF : ∀ V, Subsingleton Γ(F, V)) :
    ¬ ∃ M : LB X, M.IsLB ∧ Nonempty (lbSheaf M ≅ F) := by
  rw [lbSheaf.exists_iso_iff]
  intro h
  obtain ⟨U, hx, ⟨e⟩⟩ := h (Classical.arbitrary X)
  have : Nonempty U.toScheme := ⟨⟨_, hx⟩⟩
  have : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨Classical.arbitrary _, trivial⟩⟩
  have : Subsingleton Γ(F.restrict U.ι, ⊤) := hF _
  have : Subsingleton Γ(U.toScheme, ⊤) := (bijective_app e ⊤).1.subsingleton
  exact not_subsingleton _ this

theorem triv_and_not_iso [Nonempty X] :
    Triv (noChart X) ∧ ¬ Nonempty (lbSheaf (noChart X) ≅ unitMod X) := by
  refine ⟨triv_noChart, fun ⟨e⟩ => ?_⟩
  have : IsEmpty (noChart X).ι := inferInstanceAs (IsEmpty PEmpty)
  obtain ⟨e'⟩ := (lbSheaf.triv_iff (Inh.trivLB_isLB X)).1 (triv_trivLB X)
  exact not_exists_of_subsingleton _ (SheafModel.subsingleton_of_isEmpty (L := noChart X))
    ⟨_, Inh.trivLB_isLB X, ⟨e' ≪≫ e.symm⟩⟩

theorem noChart_empty [IsEmpty X] :
    (noChart X).IsLB ∧ Nonempty (lbSheaf (noChart X) ≅ unitMod X) :=
  have h : (noChart X).IsLB :=
    ⟨TopologicalSpace.Opens.ext (Set.ext fun x => isEmptyElim x), fun i => i.elim, fun i => i.elim⟩
  ⟨h, (lbSheaf.triv_iff h).1 triv_noChart⟩

theorem coord_secEquivHom {M M' : LB X} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Sec (LB.div M' M))
    {V O : X.Opens} (s : SecOn M V) (p : M'.ι) (q : M.ι) (hp : O ≤ V ⊓ M'.U p)
    (hq : O ≤ V ⊓ M.U q) (h : O ≤ M'.U p ⊓ M.U q) :
    rs X hp (coord ((lbSheaf.secEquivHom hM hM' w).app V s) p) =
      rs X h (w.f (p, q)) * rs X hq (coord s q) :=
  coord_homOfSec_app hM hM' w s p q hp hq h

theorem isoOfGen_hom {M M' : LB X} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Gen (LB.div M' M))
    (hw : w.IsGen) :
    (lbSheaf.isoOfGen hM hM' w hw).hom = lbSheaf.secEquivHom hM hM' (DVR.genSec w hw) := rfl

theorem hom_ext_one {F : X.Modules} {φ ψ : unitMod X ⟶ F}
    (h : φ.app ⊤ (1 : Γ(X, ⊤)) = ψ.app ⊤ (1 : Γ(X, ⊤))) : φ = ψ := by
  ext V a : 3
  exact (SheafModel.hom_app_eq_smul φ V a).trans
    (h ▸ (SheafModel.hom_app_eq_smul ψ V a).symm)

section Line
open Geo.Tor
variable (R : Type) [CommRing R] [IsDomain R]

theorem subsingleton_div_negOne :
    Subsingleton (LB.Sec (LB.div (SheafModel.negOne R) (Inh.trivLB (PSpace R 1)))) := by
  rw [(lbSheaf.secEquivHom (Inh.trivLB_isLB _) (SheafModel.negOne_isLB R)).subsingleton_congr]
  refine ⟨fun φ ψ => (cancel_epi (trivIso _).hom).1 (hom_ext_one ?_)⟩
  exact (SheafModel.subsingleton_negOne R).elim _ _

theorem nontrivial_div_one :
    Nontrivial (LB.Sec (LB.div (GlobalTheory.ProjSpace.O1 R 1) (Inh.trivLB (PSpace R 1)))) := by
  rw [(lbSheaf.secEquivHom (Inh.trivLB_isLB _) (GlobalTheory.ProjSpace.O1_isLB R 1)).nontrivial_congr]
  refine ⟨(trivIso _).inv ≫ unitHom (ProjSpace.coord R 1 0), (trivIso _).inv ≫ unitHom 0,
    fun h => ?_⟩
  have e := congrArg (fun φ => φ.app ⊤ (1 : Γ(PSpace R 1, ⊤))) ((cancel_epi _).1 h)
  simp only [unitHom_app, one_smul] at e
  have e0 : ofSec (0 : LB.Sec (GlobalTheory.ProjSpace.O1 R 1)) ⊤ = 0 := map_zero (globalEquiv _).symm
  refine one_ne_zero (SheafModel.coord_independent R 1 0 ?_).1
  rw [e, e0]
  simp

theorem not_triv_div :
    ¬ Triv (LB.div (SheafModel.negOne R) (GlobalTheory.ProjSpace.O1 R 1)) := by
  rw [lbSheaf.triv_div_iff (GlobalTheory.ProjSpace.O1_isLB R 1) (SheafModel.negOne_isLB R)]
  rintro ⟨e⟩
  have := SheafModel.subsingleton_negOne R
  have := (bijective_app e ⊤).1.subsingleton
  exact one_ne_zero (SheafModel.coord_independent R 1 0 (this.elim _ _)).1

theorem not_triv_pull_id : ¬ Triv ((GlobalTheory.ProjSpace.O1 R 1).pull (𝟙 _)) := by
  rw [lbSheaf.triv_pull_iff (GlobalTheory.ProjSpace.O1_isLB R 1)]
  rintro ⟨e⟩
  exact SheafModel.not_exists_gen R ((lbSheaf.triv_iff (GlobalTheory.ProjSpace.O1_isLB R 1)).2
    ⟨((Scheme.Modules.pullbackId _).app _).symm ≪≫ e⟩)

end Line

theorem triv_pull_chart {M : LB X} (hM : M.IsLB) (i : M.ι) : Triv (M.pull (M.U i).ι) :=
  (lbSheaf.triv_pull_iff hM _).2
    ⟨((Scheme.Modules.restrictFunctorIsoPullback (M.U i).ι).app _).symm ≪≫
      (lbSheaf.chartIso hM i).symm⟩

theorem pullback_unit (π : X' ⟶ X) :
    Nonempty ((Scheme.Modules.pullback π).obj (unitMod X) ≅ unitMod X') := by
  obtain ⟨e⟩ := (lbSheaf.triv_pull_iff (Inh.trivLB_isLB X) π).1
    ⟨⟨fun _ => 1⟩, fun i j => by rw [map_one, map_one, Inh.linComb_triv_g, _root_.one_mul]⟩
  exact ⟨(Scheme.Modules.pullback π).mapIso (trivIso X) ≪≫ e⟩

theorem triv_div_pull_comp {X'' : Scheme.{0}} {M : LB X} (hM : M.IsLB) (π : X' ⟶ X)
    (ρ : X'' ⟶ X') : Triv (LB.div ((M.pull π).pull ρ) (M.pull (ρ ≫ π))) :=
  (lbSheaf.triv_div_iff (LB.isLB_pull hM _) (LB.isLB_pull (LB.isLB_pull hM _) _)).2
    ⟨(lbSheaf.pullbackIso hM _).symm ≪≫ ((Scheme.Modules.pullbackComp ρ π).app _).symm ≪≫
      (Scheme.Modules.pullback ρ).mapIso (lbSheaf.pullbackIso hM π) ≪≫
      lbSheaf.pullbackIso (LB.isLB_pull hM π) ρ⟩

theorem pullback_local {M : LB X} (hM : M.IsLB) (R : Type) [CommRing R] [IsLocalRing R]
    (π : Spec (CommRingCat.of R) ⟶ X) :
    Nonempty ((Scheme.Modules.pullback π).obj (lbSheaf M) ≅ unitMod _) :=
  (lbSheaf.triv_pull_iff hM π).1
    ((subsingleton_pic_iff R).1 inferInstance _ (LB.isLB_pull hM π))

def unitGen (u : Γ(X, ⊤)ˣ) : LB.Gen (LB.div (Inh.trivLB X) (Inh.trivLB X)) :=
  ⟨fun _ => res le_top u⟩

theorem unitGen_isGen (u : Γ(X, ⊤)ˣ) : (unitGen u).IsGen := by
  intro i j
  change res _ (res _ u) = res _ 1 * (res _ 1)⁻¹ * res _ (res _ u)
  rw [map_one, map_one, inv_one]
  exact (LB.res_res _ _ _).trans ((LB.res_res _ _ _).symm.trans ((_root_.one_mul _).symm.trans
    (congrArg (· * _) (_root_.one_mul 1).symm)))

theorem isoOfGen_unitGen (u : Γ(X, ⊤)ˣ) (s : SecOn (Inh.trivLB X) ⊤) :
    (lbSheaf.isoOfGen (Inh.trivLB_isLB X) (Inh.trivLB_isLB X) (unitGen u)
      (unitGen_isGen u)).hom.app ⊤ s = u.val • s := by
  refine sec_ext fun i => ?_
  have h := SecOn.coord_congr (Inh.trivLB_isLB X) (Inh.trivLB_isLB X) (unitGen u)
    (unitGen_isGen u) s i i le_rfl le_rfl (le_inf le_top le_top)
  rw [rs_self, rs_self] at h
  exact h.trans (congrArg (· * coord s i) (rs_rs _ _ _))

end GlobalTheory.AbLaw.LbSheafModel
