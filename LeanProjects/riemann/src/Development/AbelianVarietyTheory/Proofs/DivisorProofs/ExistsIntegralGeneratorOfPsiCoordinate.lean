import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PsiIntGen

theorem gs_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Spec (CommRingCat.of B)) (a : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      gs (𝟙 (Spec (CommRingCat.of B))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have e' : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a) =
      ((Spec.map (CommRingCat.ofHom f)).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := e
  rw [e']
  have := gs_pull (𝟙 (Spec (CommRingCat.of B))) (Spec.map (CommRingCat.ofHom f)) z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [Category.id_comp] at this
  exact this.symm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)), gam.IsGen ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  intro V _ _ D mu r hr
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨t, ht, vt⟩ := PsiSpread.exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)
    j (fun y => Set.mem_iInter.2 fun _ => hj trivial) ⊤ (fun _ => trivial) 1
  refine ⟨t, ht, fun z J hJ => ?_⟩
  have q : jFK (R := V) (FractionRing V) ≫ ptK (D.c mu) =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left := (Category.assoc _ _ _).symm
  have a := gen_trans (D.psi_gen mu) (jFK (R := V) (FractionRing V)) z (j' := j) (hJ.mem _ _) (h trivial)
  have b := vt _ (toUnit (TF (R := V) (FractionRing V))).left z _ (hJ.mem _ _)
  rw [map_one, _root_.mul_one] at b
  have c : (gm (jFK (R := V) (FractionRing V)) z (LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c mu)) j)
      ((D.psi mu).s j)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) := by
    refine (gs_unit _ _ _ (h trivial) _).symm.trans ?_
    refine (gs_res (jFK (R := V) (FractionRing V)) z h trivial ((D.psi mu).s j).val).symm.trans ?_
    refine (congrArg (gs (jFK (R := V) (FractionRing V)) z _) e.symm).trans ?_
    refine (gs_pull (jFK (R := V) (FractionRing V)) (jK V) z ⊤ trivial _).trans ?_
    refine (gs_res _ z (le_top : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ ⊤) trivial _).trans ?_
    have s : jFK (R := V) (FractionRing V) ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
      rw [← Spec.map_comp]; rfl
    rw [s]
    exact gs_specMap _ z r
  have d : trF (L := D.P.L) (K := PUnit) (fun _ => ptK (D.c mu)) (fun _ => -1) (jFK (R := V) (FractionRing V)) z
      (fun _ => J (jFK (R := V) (FractionRing V) ≫ ptK (D.c mu))) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1) (toUnit (TF (R := V) (FractionRing V))).left z
      (fun _ => J ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left)) j :=
    congrArg (fun ψ => ∏ k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (j k)) (D.P.L.g (J ψ) (j k)) ^ (-1 : ℤ)) q
  refine (congrArg Units.val a).trans ((Units.val_mul _ _).trans ((_root_.mul_comm _ _).trans ?_))
  exact congrArg₂ (· * ·) c (congrArg Units.val (d.trans b.symm))

end GlobalTheory.Poinc.PsiIntGen
