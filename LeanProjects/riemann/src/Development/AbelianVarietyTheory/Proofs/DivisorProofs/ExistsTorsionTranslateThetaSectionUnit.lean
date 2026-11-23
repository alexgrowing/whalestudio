import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h a, gs_eq f z _ h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).symm

theorem formEq_famφB_zero {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) {Y : Scheme.{0}} (h : Y ⟶ D.P.A.left) :
    FormEq (fun i => h ≫ D.famφB 0 i) (DegPre.famε 1) (fun _ : Fin 1 => h) (fun _ => (1 : ℤ)) := by
  intro U _ hh
  have e0 : D.famφB 0 0 = 𝟙 _ := rfl
  have e1 : D.famφB 0 1 = 𝟙 _ := by
    show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
    rw [ThetaOne.c_zero, MonObj.comp_one]
    show ((𝟙 D.P.A) * 1).left = _
    rw [_root_.mul_one]; rfl
  have e2 : D.famφB 0 2 = D.famφB 0 3 := by
    show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
    rw [ThetaOne.c_zero, MonObj.comp_one]
    rfl
  simp only [Fin.prod_univ_four, Fin.prod_univ_one, e0, e1, e2]
  simp [DegPre.famε]

theorem exists_unitAt_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ N : ℕ, 2 ≤ N → IsUnit (N : V) → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)), IntTerm.Exhausts D.P N b → ∀ a : 𝟙_ (Over (Sp V)) ⟶ D.P.A, ∃ c, IntTerm.UnitAt D θ (a * b c) := by
  intro V _ _ _ D θ hθ N hN hNV C b hb a
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  let k := AlgebraicClosure (ResidueField V)
  let f : V →+* k := (algebraMap (ResidueField V) k).comp (residue V)
  let r : Sp k ⟶ Sp V := Spec.map (CommRingCat.ofHom f)
  have hNk : (N : k) ≠ 0 := by
    have := (hNV.map f).ne_zero
    rwa [map_natCast] at this
  let θ' := ThetaOne.pullTo D f θ
  have hbasis := hθ k f θ' (ThetaOne.isPullSecLC_pullTo D f θ)
  obtain ⟨j₀, hj₀⟩ := ThetaOne.exists_ne_zero D f θ' hbasis
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB (formEq_famφB_zero D (snd (Over.mk r) D.P.A).left) θ'
  have hne : SecM.ofSec D.P.A (L := D.P.L) (a := 1) (T := Over.mk r) th ≠ 0 := by
    intro h0
    apply hj₀
    have hz : ∀ j, th.f j = 0 := fun j => congrFun (congrArg Subtype.val h0) j
    refine sec_ext_val D.P.isLB (s' := H1.SectionArithmetic.secZero _) (fun y J hJ => ?_) j₀
    rw [← hth _ (𝟙 _) y J hJ]
    show gs _ y _ (th.f _) = gs _ y _ 0
    erw [hz]
    have gz : ∀ {Y : Scheme.{0}} (y : Y) (U : Y.Opens), gs (𝟙 Y) y U 0 = 0 := fun y U => by
      unfold gs; split_ifs <;> simp only [map_zero]
    exact (gz _ _).trans (gz _ _).symm
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange D.P r hN hNk th hne
    (toUnit (Over.mk r) ≫ a)
  obtain ⟨c, hc⟩ := hb k r y hy
  refine ⟨c, ?_⟩
  have hmul : (toUnit (Over.mk r) ≫ a) * y = toUnit (Over.mk r) ≫ (a * b c) := by rw [hc, MonObj.comp_mul]
  rw [hmul] at hu
  let g := a * b c
  let q : Sp k := closedPoint k
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h1 := hu q J hJ
  have hρ : (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left ≫ (snd (Over.mk r) D.P.A).left = r ≫ g.left := by
    rw [← Over.comp_left, ptSecT, lift_snd, Over.comp_left]
    congr 1
  have hθ'e : θ' = H1.SectionArithmetic.pullSec θ (snd (Over.mk r) D.P.A).left :=
    SecOps.sec_ext fun j => ThetaOne.isPullSecLC_pullTo D f θ j
  have h2 : IsUnit (sval θ (r ≫ g.left) q J) := by
    have e := hth _ (ptSecT D.P.A (toUnit (Over.mk r) ≫ g)).left q J hJ
    rw [← hρ, ← H1.SectionArithmetic.sval_pullSec θ _ _ q hJ, ← hθ'e, ← e]
    exact h1
  have hrq : r q = closedPoint V := by
    show (Spec.map (CommRingCat.ofHom f)).base (closedPoint k) = _
    rw [Spec.map_base]
    exact IsLocalRing.comap_closedPoint f
  refine ⟨fun σ => J (r ≫ σ), fun σ => ?_, ?_⟩
  · have := hJ (r ≫ σ)
    rwa [Scheme.Hom.comp_apply, hrq] at this
  · rw [sval_of θ (r ≫ g.left) q J (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) (fun i => by rw [Category.assoc])] at h2
    have hm : g.left (r q) ∈ (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U
        (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) :=
      show g.left (r q) ∈ LB.wchart D.P.L (D.famφB 0) (fun i => J (r ≫ g.left ≫ D.famφB 0 i)) from Set.mem_iInter.2 fun i => by
        have := hJ (r ≫ g.left ≫ D.famφB 0 i)
        simpa [Scheme.Hom.comp_apply] using this
    have h2' : IsUnit ((r.stalkMap q).hom (gs g.left (r q) _ (θ.f (fun i => J (r ≫ g.left ≫ D.famφB 0 i))))) := by
      rw [← gs_comp_stalkMap r g.left q _ hm]; exact h2
    have h3 := isUnit_of_map_unit (r.stalkMap q).hom _ h2'
    rw [hrq] at h3
    exact h3

end GlobalTheory.Poinc.IntTerm
