import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBasis

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {m : ℕ} (a : Fin m → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by simp only [gs_eq f y U h, map_sum]

theorem comb_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {m : ℕ} (s : LB.Sec (LB.LinComb L φ ε)) (b : Fin m → LB.Sec (LB.LinComb L φ ε)) (r : Fin m → Γ(Y, ⊤)) :
    (∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (r i) * (b i).f j) ↔
      ∀ y J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (r i) * sval (b i) (𝟙 Y) y J := by
  have key : ∀ (j : K → L.ι) (y : Y) (hy : y ∈ LB.wchart L φ j),
      gs (𝟙 Y) y (LB.wchart L φ j)
        (∑ i, (Y.presheaf.map (homOfLE (le_top : (LB.LinComb L φ ε).U j ≤ ⊤)).op).hom (r i) * (b i).f j :
          Γ(Y, (LB.LinComb L φ ε).U j)) =
      ∑ i, gs (𝟙 Y) y ⊤ (r i) * gs (𝟙 Y) y (LB.wchart L φ j) ((b i).f j) := fun j y hy =>
    (gs_sum (𝟙 Y) y _ hy _).trans (Finset.sum_congr rfl fun i _ =>
      (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg (· * _) (gs_res (𝟙 Y) y le_top hy _)))
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (key _ y (hJ.mem φ (𝟙 Y)))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    refine ((sec_trans s (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans ?_)).trans
      (key j y hy).symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (b i) (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y)), mul_left_comm]
    rfl

theorem exists_basis_of_formEq {S : Scheme.{0}} {A T : Over S} {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((T ⊗ A).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((T ⊗ A).left ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') {m : ℕ}
    {b : Fin m → LB.Sec (LB.LinComb L φ ε)} (hb : IsSecBasis _ b) :
    ∃ b' : Fin m → LB.Sec (LB.LinComb L φ' ε'), IsSecBasis _ b' := by
  choose b' hb' using fun i => exists_sec hL h (b i)
  refine ⟨b', fun t => ?_⟩
  obtain ⟨s, hs⟩ := exists_sec hL (φ := φ') (ε := ε') (φ' := φ) (ε' := ε) (fun U _ g => (h U g).symm) t
  refine (existsUnique_congr fun r => ?_).1 (hb s)
  refine (comb_iff hL s b fun i => (fst T A).left.appTop.hom (r i)).trans
    (Iff.trans ?_ (comb_iff hL t b' fun i => (fst T A).left.appTop.hom (r i)).symm)
  refine forall_congr' fun y => forall_congr' fun J => forall_congr' fun hJ => ?_
  rw [hs _ _ y J hJ]
  simp only [hb' _ _ _ y J hJ]

theorem translPt_one {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  have e : translPt A (1 : T ⟶ A) = (fst T A ≫ (1 : T ⟶ A)) * snd T A := rfl
  rw [e, MonObj.comp_one, _root_.one_mul]

theorem exists_basis_pow (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : 1 ≤ k) (R : Type) [CommRing R]
    [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S) :
    ∃ b : Fin (k ^ P.g) → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk t)), IsSecBasis _ b := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT S P k hk R t 1
  refine exists_basis_of_formEq P.isLB (fun U _ g => ?_) hb
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, translPt_one, Fintype.prod_unique]
  rw [← zpow_add, sub_add_cancel]

theorem exists_basis_pow_field : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃! c : Fin (k ^ A.g) → F, ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j := by
  intro hT R _ _ A F _ _ k hk
  obtain ⟨b, hb⟩ := exists_basis_pow hT A k hk F (jFK (R := R) F)
  refine ⟨b, fun t => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb t
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun x => liftFun A.A _ x * (b i).f j)
      ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply (r i)).symm
  · have e := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) hc
    funext i
    rw [← congrFun e i]
    exact ((Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (c i)).symm

end GlobalTheory.PowBasis
