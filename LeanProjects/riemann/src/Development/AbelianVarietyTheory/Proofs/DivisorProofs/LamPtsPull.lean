import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorNontrivial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem lamPts_comp {S : Scheme.{0}} {B T T' : Over S} [GrpObj B] (f : T' ⟶ T) (x y : T ⟶ B) (l : Fin 4) :
    f.left ≫ GlobalTheory.PolDeg.lamPts x y l = GlobalTheory.PolDeg.lamPts (f ≫ x) (f ≫ y) l := by
  fin_cases l <;> simp [GlobalTheory.PolDeg.lamPts, ← Over.comp_left, MonObj.comp_mul]

theorem lamPts_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (l : Fin 4) :
    (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A).left ≫
      GlobalTheory.PolDeg.lamPts (fst D'.P.A D'.P.A ≫ T.pr i) (snd D'.P.A D'.P.A ≫ T.pr j) l =
    GlobalTheory.PolDeg.lamPts (if i = i₀ then fst D.P.A D.P.A else 1) (snd D.P.A D.P.A ^ m j i₀) l := by
  have h1 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      fst D'.P.A D'.P.A ≫ T.pr i = if i = i₀ then fst D.P.A D.P.A else 1 := by
    rw [lift_fst_assoc, Category.assoc, T.inc_pr']
    split_ifs <;> simp
  have h2 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      snd D'.P.A D'.P.A ≫ T.pr j = snd D.P.A D.P.A ^ m j i₀ := by
    rw [lift_snd_assoc, Category.assoc, Category.assoc, T.act_pr]
    have e : ∀ k, (snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then snd D.P.A D.P.A else 1 := fun k => by
      rw [Category.assoc, T.inc_pr']; split_ifs <;> simp
    rw [← Category.assoc]
    change preHom (snd D.P.A D.P.A ≫ T.inc i₀) (∏ k, T.pr k ^ m j k) = _
    rw [map_prod]
    simp only [map_zpow]
    change ∏ k, ((snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k) ^ m j k = _
    simp only [e]
    rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
  rw [lamPts_comp, h1, h2]

theorem xe_xi {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ i : Fin r) (a : D.X) : T.xe (T.xi i₀ a) i = if i = i₀ then a else 0 := by
  simp [Tens.xi, Pi.single_apply]

theorem c_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (n : ℤ) (b : D.X) : D.c (n • b) = D.c b ^ n := by
  let φ : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (D.c x)) (fun a b => by
      show Additive.ofMul (D.c (a + b)) = Additive.ofMul (D.c a * D.c b)
      rw [D.c_add]; rfl)
  exact congrArg Additive.toMul (map_zsmul φ n b)

theorem pt_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (a b : D.X) (a' b' : D'.X)
    (ha : ∀ i, T.xe a' i = if i = i₀ then a else 0) (hb : ∀ j, T.xe b' j = m j i₀ • b) :
    (lift (toUnit (TK R) ≫ D'.c a') (toUnit (TK R) ≫ D'.c b') : TK R ⟶ G2 D'.P.A) =
      lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) ≫
        lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) := by
  have c0 : D.c 0 = 1 := by
    have := c_zsmul D 0 a; rwa [zero_smul, zpow_zero] at this
  rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  congr 1
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, ha, T.inc_pr']
    split_ifs <;> simp [c0]
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, hb, c_zsmul, T.act_pr]
    have e : ∀ k, (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then toUnit (TK R) ≫ D.c b else 1 := fun k => by
      rw [Category.assoc, Category.assoc, T.inc_pr']; split_ifs <;> simp
    calc toUnit (TK R) ≫ D.c b ^ m i i₀ = (toUnit (TK R) ≫ D.c b) ^ m i i₀ := map_zpow (preHom (toUnit (TK R))) _ _
      _ = ∏ k, ((toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k) ^ m i k := by
        simp only [e]
        rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
      _ = (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ ∏ k, T.pr k ^ m i k := by
        change _ = preHom (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) (∏ k, T.pr k ^ m i k)
        rw [map_prod]
        simp only [map_zpow]
        rfl
      _ = _ := by simp only [Category.assoc]

end GlobalTheory.TensPair
