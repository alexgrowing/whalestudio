import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HTSummand.LieMod

variable {R : Type} [CommRing R]

def epsIso : epsR R ≅ GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) := Over.isoMk (Iso.refl _) (by simp)

@[simp] lemma epsIso_hom_left : (epsIso (R := R)).hom.left = 𝟙 _ := rfl
@[simp] lemma epsIso_inv_left : (epsIso (R := R)).inv.left = 𝟙 _ := rfl

lemma one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Scheme.{0}} (x : X ⟶ S) :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

lemma comp_prod {S : Scheme.{0}} {G Y Z : Over S} [GrpObj G] (f : Z ⟶ Y) (l : List (Y ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [MonObj.comp_mul, ih]

lemma isLieImage_sum {A : Over (Sp R)} [GrpObj A] : ∀ (n : ℕ) (u : Fin n → HdR A) (w : Fin n → (epsR R ⟶ A)),
    (∀ i, IsLieImage (u i) (w i)) → IsLieImage (∑ i, u i) (List.ofFn w).prod
  | 0, u, w, _ => by simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, u, w, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact (h 0).add (isLieImage_sum n _ _ fun i => h i.succ)

lemma isLieImage_eq {A : Over (Sp R)} [GrpObj A] (H : LieExact A) {h h' : HdR A} {v v' : epsR R ⟶ A}
    (e : IsLieImage h v) (e' : IsLieImage h' v') (hd : h - h' ∈ Fil A) : v = v' := by
  have k : IsLieImage (h' + (h - h')) (v' * 1) := e'.add (isLieImage_one_iff.2 hd)
  rw [add_sub_cancel, _root_.mul_one] at k
  exact (H.1 h).unique e k

lemma tan_of {A : Over (Sp R)} [GrpObj A] {v : epsR R ⟶ A} (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsIso.inv ≫ v).left =
      (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, Category.id_comp, Over.comp_left, epsIso_inv_left, Category.id_comp]
  exact hv

lemma tan_to {A : Over (Sp R)} [GrpObj A] {w : GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) ⟶ A}
    (hw : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left) :
    IsTangent (epsIso.hom ≫ w) := by
  rw [one_left, Category.id_comp] at hw
  show _ ≫ (epsIso.hom ≫ w).left = _
  rw [Over.comp_left, epsIso_hom_left, Category.id_comp]
  exact hw

end GlobalTheory.HTSummand.LieMod

namespace GlobalTheory.HTSummand

open LieMod in

theorem lie_mod_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  intro p _ D R _ b N C₀ _ _ β s hs o₀ y hy
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab
  have H : LieExact o₀.A := (GlobalTheory.abelianDeRham.2.1 C₀ o₀.A g o₀.ab hg).1
  obtain ⟨v, hv, -⟩ := H.1 y
  set ωO := algebraMap (𝓞 D.F) D.O D.ω
  haveI := o₀.act.hom ωO
  have hω : v ≫ o₀.act.act ωO = GlobalTheory.GrpTangent.epsScale (β b.ρ) ≫ v :=
    isLieImage_eq H (hv.push (o₀.act.act ωO)) (hv.smul (β b.ρ)) hy
  have hx : 𝟙 (Sp C₀) ≫ s = spMap β := by rw [Category.id_comp, hs]
  have hvT : GlobalTheory.UPel.HT.IsTanScal o₀.act (𝟙 (Sp C₀)) ωO (β b.ρ) (epsIso.inv ≫ v) := by
    refine ⟨tan_of hv.1, ?_⟩
    rw [Category.assoc, Over.comp_left, hω, Over.comp_left, Over.comp_left, epsIso_inv_left, Category.id_comp,
      Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
  obtain ⟨w, hw, hprod⟩ := o₀.lie C₀ β (𝟙 (Sp C₀)) hx (epsIso.inv ≫ v) hvT
  have hwT : ∀ i, IsTangent (epsIso.hom ≫ w i) := fun i => tan_to (hw i 0).1
  choose u hu using fun i => H.2 _ (hwT i)
  refine ⟨u, fun i c => ?_, ?_⟩
  · haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e : (epsIso.hom ≫ w i) ≫ o₀.act.act (algebraMap (𝓞 D.F) D.O c) =
        GlobalTheory.GrpTangent.epsScale (β (b.t i c)) ≫ epsIso.hom ≫ w i := by
      ext1
      simp only [Over.comp_left, epsIso_hom_left, Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
      rw [← Over.comp_left]
      exact (hw i c).2
    have k₁ := (hu i).push (o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    rw [e] at k₁
    exact k₁.sub_mem ((hu i).smul (β (b.t i c)))
  · have k := isLieImage_sum D.a u _ hu
    have e : (List.ofFn fun i => epsIso.hom ≫ w i).prod = v := by
      rw [show (List.ofFn fun i => epsIso.hom ≫ w i) = (List.ofFn w).map (epsIso.hom ≫ ·) from
        List.map_ofFn.symm, ← comp_prod, ← hprod, Iso.hom_inv_id_assoc]
    rw [e] at k
    exact hv.sub_mem k

end GlobalTheory.HTSummand
