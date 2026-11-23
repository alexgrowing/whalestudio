import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfSvalWhiskerRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.OneDim

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

def zeroSec {Y : Scheme.{0}} (M : LB Y) : LB.Sec M :=
  ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem expF_zero (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) :
    U.ExpF F k (zeroSec _) (fun _ => zeroSec _) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, ?_⟩
  · intro Z rA y rG _ _ z JA JG _ _
    rw [Fin.sum_univ_zero]
    exact (congrArg (_ * ·) (gs_zero _ _ _)).trans (mul_zero _)
  · intro α Z rF rB _ z J _
    rw [Fin.sum_univ_zero]
    exact gs_zero _ _ _

theorem appTop_injective (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e₂ : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have a := Over.w (toUnit (TF (R := R) F))
    exact ((Category.comp_id _).symm.trans a).trans (Spec.map_comp _ _).symm
  rw [e₂]
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have i : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))).hom :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [← n] at i
  exact Function.Injective.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom) i

theorem eq_zero_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h : U.PullG F (toUnit _) k σ t) (ht : ∀ j, t.f j = 0) (j) : σ.f j = 0 := by
  have hs : Smooth G.hom := U.semi.smooth
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  refine GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero _ G (𝟙_ _) (TF (R := R) F) (toUnit _) (appTop_injective F)
    _ U.P.L.L U.P.L.isLB _ _ _ σ (fun z J hJ => ?_) j
  have w : (snd (TF (R := R) F) G).left ≫ G.hom =
      ((fst (TF (R := R) F) G).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (snd (TF (R := R) F) G)).trans ((Over.w (fst (TF (R := R) F) G)).symm.trans (Category.assoc _ _ _).symm)
  let y : (TF (R := R) F ⊗ G).left ⟶ ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w
  have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  have w' : (fst (TF (R := R) F) G).left ≫ jFK (R := R) F = (y ≫ U.gen.hom.left) ≫ A.A.hom := by
    rw [Category.assoc, e₄]
    exact (pullback.lift_snd _ _ _).symm
  let rA : (TF (R := R) F ⊗ G).left ⟶ (TFK (R := R) F ⊗ A.A).left := pullback.lift _ _ w'
  obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
  refine (h _ rA y (toUnit (TF (R := R) F) ▷ G).left (pullback.lift_snd _ _ _) ?_ ?_ z JA J hJA hJ).symm.trans ?_
  · exact (congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) G)).trans
      (pullback.lift_fst _ _ w).symm
  · refine (congrArg CommaMorphism.left (whiskerRight_fst (toUnit (TF (R := R) F)) G)).trans ?_
    rw [← Category.assoc]
    exact congrArg (· ≫ (toUnit (TF (R := R) F)).left) (pullback.lift_fst _ _ w').symm
  · exact (congrArg (_ * ·) ((congrArg (gs rA z _) (ht _)).trans (gs_zero _ _ _))).trans (mul_zero _)

end

theorem exists_smul_of_finrank_one {F B M : Type} [Field F] [CommRing B] [AddCommGroup M] [Module B M]
    (e : F ≃+* B) (h : Module.finrank B M = 1) {v : M} (hv : v ≠ 0) (w : M) : ∃ c : F, e c • v = w := by
  letI : Field B := (e.symm.toMulEquiv.isField (Field.toIsField F)).toField
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := B) v hv).1 h w
  exact ⟨e.symm c, by rw [e.apply_symm_apply]; exact hc⟩

theorem expF_one_dim : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → (∃ j, th.f j ≠ 0) ∧ U.ExpF (Kbar V) 1 th s₀ ∧ ∀ t s, U.ExpF (Kbar V) 1 t s → ∃ c : (Kbar V), ∀ α j, (s α).f j = DegPre.constBF D (Kbar V) c _ * (s₀ α).f j) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hG hB
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hn
    obtain ⟨j, hj⟩ := hθ.2
    exact hj (eq_zero_of_pullG U (Kbar V) 1 θ th hG (fun j => by_contra fun h => hn ⟨j, h⟩) j)
  have hE := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 1 θ f th s₀ hθ.1 hG hB
  refine ⟨hne, hE, fun t s hts => ?_⟩
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) 1
    (by rw [Nat.cast_one]; exact one_ne_zero)
  rw [one_pow] at hr
  have hv : SecM.ofSec A.A th ≠ 0 := fun h => by
    obtain ⟨j, hj⟩ := hne
    exact hj (congrFun (congrArg Subtype.val h) j)
  obtain ⟨c, hc⟩ := exists_smul_of_finrank_one
    (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).symm.commRingCatIsoToRingEquiv hr hv (SecM.ofSec A.A t)
  let s' : Raw D (Kbar V) 1 := fun α =>
    ⟨fun j => DegPre.constBF D (Kbar V) c _ * (s₀ α).f j, fun i j => by
      rw [map_mul, map_mul, (s₀ α).compat i j, mul_left_comm]
      congr 2
      exact fn_ext fun x hx => (gs_res _ x _ hx _).trans ((gs_res _ x _ hx.1 _).trans
        ((gs_res _ x _ hx _).trans (gs_res _ x _ hx.2 _)).symm)⟩
  have hs' : U.ExpF (Kbar V) 1 t s' :=
    GlobalTheory.UU.ExpLin.expF_linear V hV D A G U (Kbar V) 1 th (zeroSec _) t s₀ (fun _ => zeroSec _) s' c hE
      (expF_zero U _ 1) (fun j => ((congrFun (congrArg Subtype.val hc) j).symm).trans (add_zero _).symm)
      (fun α j => (add_zero _).symm)
  have e : s = s' := (GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U (Kbar V) 1 t t s s' hts hs').1 rfl
  exact ⟨c, fun α j => by rw [e]⟩

end GlobalTheory.UU.OneDim
end
