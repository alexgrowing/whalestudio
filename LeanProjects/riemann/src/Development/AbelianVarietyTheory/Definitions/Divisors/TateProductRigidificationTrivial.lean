import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

structure Factor (D D' : DegPre R) where

  O : Type
  [ring : Ring O]
  [star : StarRing O]
  [mod : Module O D'.X]

  o : D'.OAct O

  e : O

  f : O

  inc : D.P.A ⟶ D'.P.A

  pr : D'.P.A ⟶ D.P.A

  xi : D.X →+ D'.X

  xp : D'.X →+ D.X

  w : letI := D.P.isAb.comm; letI := D'.P.isAb.comm
    LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o.onB.act f) : G2 D.P.A ⟶ G2 D'.P.A).left)
  idem : e * e = e
  inc_hom : IsMonHom inc
  pr_hom : IsMonHom pr
  inc_pr : inc ≫ pr = 𝟙 _
  pr_inc : pr ≫ inc = o.onB.act e
  xp_xi : ∀ y, xp (xi y) = y
  xi_xp : ∀ z, xi (xp z) = e • z
  c_xi : ∀ y, D'.c (xi y) = D.c y ≫ inc
  inj : Function.Injective fun y => Star.star e • f • xi y
  onto : ∀ z, ∃ y, Star.star e • z = Star.star e • f • xi y
  w_gen : w.IsGen
  tau : ∀ a b z J J', Good D'.P.L z J → Good D.P.L z J' →
    val (D.tau a b) (𝟙 _) z J' =
      GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J J' *
        val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J

attribute [instance] Factor.ring Factor.star Factor.mod

theorem Factor.isFactor {D D' : DegPre R} (F : Factor D D') : IsFactor D D' :=
  ⟨F.O, _, _, _, F.o, F.e, F.f, F.inc, F.pr, F.xi, F.xp, F.w, F.idem, F.inc_hom, F.pr_hom, F.inc_pr, F.pr_inc, F.xp_xi,
    F.xi_xp, F.c_xi, ⟨F.inj, F.onto⟩, F.w_gen, F.tau⟩

def SamePol (D D' : DegPre R) : Prop :=
  ∃ (Q : GlobalTheory.PolDeg.Data R) (e : D.X ≃+ Q.X) (e' : D'.X ≃+ Q.X),
    GlobalTheory.PolDeg.Refines Q (RingHom.id R) D e ∧ GlobalTheory.PolDeg.Refines Q (RingHom.id R) D' e'

abbrev Kb (R : Type) [CommRing R] [IsDomain R] : Type := AlgebraicClosure (FractionRing R)

abbrev Labels (D : DegPre R) (A : PolAV (Sp (FractionRing R))) : Type :=
  ∀ k : ℕ, QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)

def Induces {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegPre R} {A : PolAV (Sp (FractionRing R))}
    (lab : Labels D A) (φ : R →+* W) {D' : DegData W I} {A' : PolAV (Sp (FractionRing W))} {G' : Over (Sp W)} [GrpObj G']
    [IsCommMonObj G'] (U' : Unif I D' A' G') (hD : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left) (k : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F),
    (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r))) →
    ∀ (p : QkPt D (Kb R) k) (p₁ : QkPt D F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := W) F ⟶ A'.A),
      QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD F p₁.g p'.g →
      x'.left ≫ a = spMap em.toRingHom ≫ (lab k p).left → QkToAkU U'.toUnifPre F k p' x'

def GalEq {D : DegPre R} {A : PolAV (Sp (FractionRing R))} (lab : Labels D A) : Prop :=
  ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D (Kb R) k, QkExt σ.toRingHom p p' →
    (lab k p').left = spMap σ.toRingHom ≫ (lab k p).left

def IsFib {W : Type} [CommRing W] [IsDomain W] (φ : R →+* W) (A : PolAV (Sp (FractionRing R)))
    (A' : PolAV (Sp (FractionRing W))) (a : A'.A.left ⟶ A.A.left) : Prop :=
  ∃ ga : FractionRing R →+* FractionRing W, (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
    IsGrpPullback A'.A A.A (spMap ga) a ∧ LBIso A'.L (A.L.pull a)

def OneTrait [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (lab : Labels D A) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (U' : Unif (maximalIdeal W) D' A' G') (hD : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left)
    (_ : Algebra (FractionRing R) (Kb W)) (em : Kb R →ₐ[FractionRing R] Kb W),
    GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsSemiAbelian G' ∧ IsFib φ A A' a ∧
    (∀ r, algebraMap (FractionRing R) (Kb W) (algebraMap R _ r) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D (Kb R) k) (p₁ : QkPt D (Kb W) k) (p' : QkPt D'.toPre (Kb W) k)
      (x' : TFK (R := W) (Kb W) ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD (Kb W) p₁.g p'.g →
      x'.left ≫ a = spMap em.toRingHom ≫ (lab k p).left → QkToAkU U'.toUnifPre (Kb W) k p' x'

end

structure Emb {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) [GrpObj G] where

  N : ℕ

  H : G.left.Opens
  H_all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ H

  f : H.toScheme ⟶ PSpace R N
  f_over : f ≫ PSpace.str R N = H.ι ≫ G.hom ≫ π

  Y : Over (Sp (ResidueField R))
  [grp : GrpObj Y]
  smooth : Smooth Y.hom

  j : Y.left ⟶ PSpace R N
  j_over : j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R)
  imm : IsImmersion j
  fib : ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : ResidueField R →+* Ω), x ≫ π = spMap (κ.comp (residue R)) →
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω')
      (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (l : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ H.toScheme), IsMonHom e.hom ∧
      l ≫ H.ι = pullback.fst G.hom (spMap io ≫ x) ∧ l ≫ f = e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j

attribute [instance] Emb.grp

def Emb.Theta {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (E : Emb π G)
    (L : LB G.left) : Prop :=
  ∃ (θ : L.Sec) (O : E.Y.left.Opens), (O : Set E.Y.left).Nonempty ∧ ∀ (g : E.H.toScheme) (y : E.Y.left), y ∈ O →
    π (G.hom (E.H.ι g)) = closedPoint R → E.f g = E.j y → ∃ i : L.ι, E.H.ι g ∈ G.left.basicOpen (θ.f i)

theorem Wit.isMonHom_pullbackComp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsMonHom (M := (Over.pullback (s ≫ p)).obj G)
      (N := (Over.pullback s).obj ((Over.pullback p).obj G))
      ((Over.pullbackComp s p).hom.app G) := by
  let m : (Over.pullback (s ≫ p)).mapMon.obj (Mon.mk G) ≅
      (Over.pullback s).mapMon.obj ((Over.pullback p).mapMon.obj (Mon.mk G)) :=
    (Functor.mapMonNatIso (Over.pullbackComp s p) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
  have h : IsMonHom m.hom.hom := inferInstance
  have e : m.hom.hom = (Over.pullbackComp s p).hom.app G := Category.comp_id _
  rw [e] at h
  exact h

theorem Wit.pullbackComp_fst {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) :
    ((Over.pullbackComp s p).hom.app G).left ≫ pullback.fst _ s ≫ pullback.fst G.hom p = pullback.fst G.hom (s ≫ p) := by
  simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]

def Emb.ofImm {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] {N : ℕ}
    (i : G.left ⟶ PSpace R N) [IsImmersion i] (hi : i ≫ PSpace.str R N = G.hom) : Emb (𝟙 (Sp R)) G where
  N := N
  H := ⊤
  H_all _ _ := trivial
  f := Scheme.Opens.ι _ ≫ i
  f_over := by simp [hi]
  Y := (Over.pullback (spMap (residue R))).obj G
  smooth := inferInstanceAs (Smooth (pullback.snd G.hom (spMap (residue R))))
  j := pullback.fst G.hom (spMap (residue R)) ≫ i
  j_over := by rw [Category.assoc, hi]; exact pullback.condition
  imm := by
    have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
    have : IsClosedImmersion (pullback.fst G.hom (spMap (residue R))) := inferInstance
    infer_instance
  fib Ω _ x κ hx := by
    have hx' : spMap (RingHom.id Ω) ≫ x = spMap ((RingHom.id Ω).comp κ) ≫ spMap (residue R) := by
      rw [Category.comp_id] at hx
      rw [hx, ← Spec.map_comp, ← Spec.map_comp]; rfl
    refine ⟨Ω, inferInstance, RingHom.id Ω, ?_⟩
    rw [hx']
    refine ⟨(Over.pullbackComp _ _).app G, pullback.fst _ _ ≫ G.left.topIso.inv, ?_, by simp, ?_⟩
    · exact Wit.isMonHom_pullbackComp _ _ G
    · have h : ((Over.pullbackComp (spMap ((RingHom.id Ω).comp κ)) (spMap (residue R))).app G).hom.left ≫
          pullback.fst _ (spMap ((RingHom.id Ω).comp κ)) ≫ pullback.fst G.hom (spMap (residue R)) = pullback.fst _ _ :=
        Wit.pullbackComp_fst _ _ G
      refine Eq.trans ?_ ((congrArg (· ≫ i) h).symm.trans (by simp))
      simp

def Wit.toL (R : Type) [CommRing R] : MvPolynomial {j : Fin 3 // j ≠ 0} R →ₐ[R] LaurentPolynomial R :=
  MvPolynomial.aeval fun j => if j.1 = 1 then LaurentPolynomial.T 1 else LaurentPolynomial.T (-1)

theorem Wit.toL_surj (R : Type) [CommRing R] : Function.Surjective (Wit.toL R) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  rintro p -
  have h1 : LaurentPolynomial.T 1 ∈ (Wit.toL R).range := ⟨MvPolynomial.X ⟨1, by decide⟩, by simp [Wit.toL]⟩
  have h2 : LaurentPolynomial.T (-1) ∈ (Wit.toL R).range := ⟨MvPolynomial.X ⟨2, by decide⟩, by simp [Wit.toL]⟩
  have hT : ∀ n : ℤ, LaurentPolynomial.T n ∈ (Wit.toL R).range := fun n => by
    induction n using Int.induction_on with
    | zero => exact one_mem _
    | succ n ih => rw [LaurentPolynomial.T_add]; exact mul_mem ih h1
    | pred n ih => rw [sub_eq_add_neg, LaurentPolynomial.T_add]; exact mul_mem ih h2
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => exact add_mem hp hq
  | C_mul_T n a => exact mul_mem (Subalgebra.algebraMap_mem _ a) (hT n)

def Wit.embGm (R : Type) [CommRing R] [IsLocalRing R] : Emb (𝟙 (Sp R)) (splitTorusAff (CommRingCat.of R) ℤ) :=
  haveI : Smooth (splitTorusAff (CommRingCat.of R) ℤ).hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    have : IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
      IsScalarTower.of_algebraMap_eq fun r => (Polynomial.toLaurent_C r).symm
    have : Algebra.Smooth (Polynomial R) (LaurentPolynomial R) := Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial R)
    have : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
    exact RingHom.smooth_algebraMap.2 (Algebra.Smooth.comp R (Polynomial R) _)
  haveI : IsClosedImmersion (spMap (Wit.toL R).toRingHom) := IsClosedImmersion.spec_of_surjective _ (Wit.toL_surj R)
  haveI : IsImmersion (spMap (Wit.toL R).toRingHom ≫ GlobalTheory.ProjSpace.chartι R 2 0) := inferInstance
  @Emb.ofImm R _ _ (splitTorusAff (CommRingCat.of R) ℤ) _ _ 2 (spMap (Wit.toL R).toRingHom ≫ GlobalTheory.ProjSpace.chartι R 2 0) this (by
    change (spMap (Wit.toL R).toRingHom ≫ GlobalTheory.ProjSpace.chartι R 2 0) ≫ PSpace.str R 2 = spMap (algebraMap R (LaurentPolynomial R))
    rw [Category.assoc, GlobalTheory.ProjSpace.chartι_str, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => (Wit.toL R).commutes r)

namespace Wit
open InhTate Inh

def tate2 : DegPre InhTate.R :=
  { tatePre with
    X := ℤ × ℤ
    addX := inferInstance
    freeX := inferInstance
    finX := inferInstance
    c := fun _ => toUnit _ ≫ η[P0.A]
    c_add := fun _ _ => toUnit_unique _ _
    psi := fun n => cg _ _ (pi0 ^ (n.1 ^ 2 + n.2 ^ 2))
    psi_gen := fun _ => cg_isGen _ _ _ }

theorem psi2 (n : ℤ × ℤ) : IsConst (tate2.psi n) (pi0 ^ (n.1 ^ 2 + n.2 ^ 2)) := cg_isConst _ _ _

theorem tateProduct_rigidification_trivial : IsConst tate2.rigK 1 := ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))

theorem tau2 (a b : ℤ × ℤ) : IsConst (tate2.tau a b) (pi0 ^ (2 * a.1 * b.1 + 2 * a.2 * b.2)) := by
  unfold DegPre.tau
  refine (isConst_mulGen (isConst_mulGen (isConst_mulGen (psi2 (a + b))
    (isConst_invGen (psi2 a))) (isConst_invGen (psi2 b)))
    (isConst_invGen tateProduct_rigidification_trivial)).of_eq ?_
  rw [inv_one, _root_.mul_one, ← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add, Prod.fst_add, Prod.snd_add]
  congr 1 <;> ring

instance : Module (ℤ × ℤ) tate2.X := inferInstanceAs (Module (ℤ × ℤ) (ℤ × ℤ))

theorem tateProduct_period_value (a b : ℤ × ℤ) (z J) (hJ : Good tate2.P.L z J) :
    val (tate2.tau a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (pi0 ^ (2 * a.1 * b.1 + 2 * a.2 * b.2)) := by
  unfold val
  erw [tau2]
  exact gm_res _ z _ (hJ.mem _ _) _

def act2 : tate2.OAct (ℤ × ℤ) where
  onB := zeroOAct _ _
  c_lin _ _ := toUnit_unique _ _
  tau_bal a u hu h y y' := by
    refine corr_of_val tate2.P.isLB fun z J hJ => ?_
    have hp : tate2.pt2 y y' = (toUnit (TK InhTate.R)).left ≫ zero2 tate2.P.A := by
      have : lift (toUnit (TK InhTate.R) ≫ tate2.c y) (toUnit (TK InhTate.R) ≫ tate2.c y') =
          toUnit (TK InhTate.R) ≫ lift η[tate2.P.A] η[tate2.P.A] := by
        rw [comp_lift]; congr 1
      exact congrArg (fun q => q.left) this
    have h1 := val_corr hJ h (toUnit (TK InhTate.R)).left
    rw [val_pull hJ, val_one] at h1
    rw [val_mul hJ, val_pull hJ, Category.id_comp, hp, h1, _root_.mul_one]
    refine (tateProduct_period_value _ _ z J hJ).trans (Eq.trans ?_ (tateProduct_period_value _ _ z J hJ).symm)
    congr 2
    show 2 * (a.1 * (y : ℤ × ℤ).1) * (y' : ℤ × ℤ).1 + 2 * (a.2 * (y : ℤ × ℤ).2) * (y' : ℤ × ℤ).2 =
      2 * (y : ℤ × ℤ).1 * (a.1 * (y' : ℤ × ℤ).1) + 2 * (y : ℤ × ℤ).2 * (a.2 * (y' : ℤ × ℤ).2)
    ring

def fac : Factor tatePre tate2 where
  O := ℤ × ℤ
  o := act2
  e := (1, 0)
  f := 1
  inc := 𝟙 _
  pr := 𝟙 _
  xi := AddMonoidHom.inl ℤ ℤ
  xp := AddMonoidHom.fst ℤ ℤ
  w := ⟨fun _ => 1⟩
  idem := by simp
  inc_hom := inferInstanceAs (IsMonHom (𝟙 P0.A))
  pr_hom := inferInstanceAs (IsMonHom (𝟙 P0.A))
  inc_pr := Category.id_comp _
  pr_inc := Category.id_comp _
  xp_xi _ := rfl
  xi_xp (z : ℤ × ℤ) := by show ((z.1, 0) : ℤ × ℤ) = (1 * z.1, 0 * z.2); simp
  c_xi _ := toUnit_unique _ _
  inj (a : ℤ) (b : ℤ) h := by
    have : (1 * (1 * a) : ℤ) = 1 * (1 * b) := congrArg Prod.fst h
    exact (by simpa using this : a = b)
  onto (z : ℤ × ℤ) := ⟨z.1, by show ((1 * z.1, 0 * z.2) : ℤ × ℤ) = (1 * (1 * z.1), 0 * (1 * 0)); simp⟩
  w_gen := by
    refine (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_
    unfold gw
    erw [map_one, linComb_triv_g, map_one, map_one]
    simp
  tau (a : ℤ) (b : ℤ) z J J' hJ hJ' := by
    unfold val GlobalTheory.PolDeg.lamVal
    erw [tau_isConst a b, tau2, map_one, _root_.one_mul]
    refine (gm_res _ z _ (hJ'.mem _ _) _).trans (Eq.trans ?_ (gm_res _ z _ (hJ.mem _ _) _).symm)
    congr 2
    show 2 * a * b = 2 * a * (1 * b) + 2 * 0 * (1 * 0)
    ring
end Wit

theorem Wit.fac_e : Wit.fac.e ≠ 0 ∧ Wit.fac.e ≠ 1 :=
  ⟨fun h => one_ne_zero (congrArg Prod.fst (h : ((1, 0) : ℤ × ℤ) = 0)), fun h => zero_ne_one (congrArg Prod.snd (h : ((1, 0) : ℤ × ℤ) = 1))⟩

theorem SamePol.refl {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (h : D.TauBimult) : SamePol D D :=
  ⟨_, _, _, GlobalTheory.PolDeg.Wit.refines_ofDeg D h, GlobalTheory.PolDeg.Wit.refines_ofDeg D h⟩

theorem Emb.theta_triv {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (E : Emb π G) : E.Theta (Inh.trivLB G.left) := by
  refine ⟨⟨fun _ => 1, fun i j => ?_⟩, ⊤, ⟨(η[E.Y]).left (closedPoint (ResidueField R)), trivial⟩,
    fun g y _ _ _ => ⟨PUnit.unit, ?_⟩⟩
  · exact (map_one _).trans ((_root_.one_mul _).trans (map_one _)).symm
  · rw [Scheme.basicOpen_one]; trivial

end GlobalTheory.Mum
