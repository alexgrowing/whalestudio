import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIsoStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SqCompare

open GlobalTheory.CoordCompare GlobalTheory.PrimNorm GlobalTheory.MulPull in

theorem sq_law {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hT : ∃ t : LB.Gen (Theta A M), t.IsGen) {Y : Over S} (y : Y ⟶ A) (a b : 𝟙_ (Over S) ⟶ A)
    (v : LB.Gen (LB.LinComb M (diffφ y a b) ![2, -2, 2, -2])) (hv : v.IsGen) :
    ∃ v' : LB.Gen (LB.LinComb M (diffφ y (a * a) (b * b)) ![1, -1, 1, -1]), v'.IsGen := by
  have hc := fun p q s : Y ⟶ A => diff₃_ptCls (T := Y) hM hT p q s
  have h := (hasGen_iff hM _ _).1 ⟨v, hv⟩
  rw [Fin.prod_univ_four] at h
  refine (hasGen_iff hM _ _).2 ?_
  rw [Fin.prod_univ_four]
  set m := ptCls M Y with hm
  set α := toUnit Y ≫ a
  set β := toUnit Y ≫ b
  have cα : toUnit Y ≫ (a * a) = α * α := MonObj.comp_mul _ _ _
  have cβ : toUnit Y ≫ (b * b) = β * β := MonObj.comp_mul _ _ _
  change m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ) = 1 at h
  change m (y * (toUnit Y ≫ (b * b))) ^ (1 : ℤ) * m (y * (toUnit Y ≫ (a * a))) ^ (-1 : ℤ) *
    m (toUnit Y ≫ (a * a)) ^ (1 : ℤ) * m (toUnit Y ≫ (b * b)) ^ (-1 : ℤ) = 1
  rw [cα, cβ]
  have kα := diff₂_mul_right hc y α α
  have kβ := diff₂_mul_right hc y β β
  calc _ = (diff₂ m y (β * β) * (diff₂ m y β * diff₂ m y β)⁻¹) *
        (diff₂ m y (α * α) * (diff₂ m y α * diff₂ m y α)⁻¹)⁻¹ *
        (m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ)) := by
        apply Additive.ofMul.injective
        simp only [diff₂, ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
    _ = 1 := by rw [← kα, ← kβ, h, mul_inv_cancel, mul_inv_cancel, inv_one, _root_.mul_one, _root_.mul_one]

open GlobalTheory.CoordCompare TorusCoord in

theorem sq_desc {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G)
    (Φ : D'.P.A ⟶ D.P.A) [IsMonHom Φ] [Mono Φ.left] (hp : g'.pG ≫ Φ = g.pG)
    (w : LB.Iso (LB.LinComb D'.P.L (K := Fin 1) (fun _ => 𝟙 D'.P.A.left) (fun _ => 2))
      ((LB.LinComb D.P.L (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => 2)).pull Φ.left)) (hw : w.IsGen)
    (χ : D.X) (χ' : D'.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D'.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
      val (g.t χ) r z J = val (g'.t χ') r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ)) ![2, -2, 2, -2]), v.IsGen := by
  obtain ⟨t, ht, W, hW⟩ := GlobalTheory.T.exists_square_generator_through_squareIso D.P.isLB D'.P.isLB w hw (D'.Oφ g'.pG χ') Oinvε (g'.t χ') (g'.t_gen χ')
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) (ε' := ![2, -2, 2, -2])
    (fun U _ h => by
      have e2 := prod_diff (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) ((Over.map (thick R I e)).map g.q) h
      have e3 : ∏ k, h (g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^ (![2, -2, 2, -2] : Fin 4 → ℤ) k =
          (∏ k, h (((Over.map (thick R I e)).map g.q).left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^
            (![1, -1, 1, -1] : Fin 4 → ℤ) k) ^ (2 : ℤ) := by
        simp only [Fin.prod_univ_four, mul_zpow, ← zpow_mul]
        rfl
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (e3.trans (congrArg (· ^ (2 : ℤ)) e2)).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, Oφ_comp_hom, hp, Fintype.prod_sum_type]
      simp only [Fin.prod_univ_four]
      let T := (Over.map (thick R I e)).obj (thickObj R I e G)
      show h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left ^ (2 * (-1 : ℤ)) * h (toUnit T ≫ D'.c χ' ≫ Φ).left ^ (2 * (1 : ℤ)) *
          h g.pG.left ^ (2 * (1 : ℤ)) * h (1 : T ⟶ D.P.A).left ^ (2 * (-1 : ℤ)) *
        ((h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ)) *
         (h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ))) =
        (h (g.pG * (toUnit T ≫ D.c χ)).left * (h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left)⁻¹ *
          h (toUnit T ≫ D'.c χ' ≫ Φ).left * (h (toUnit T ≫ D.c χ).left)⁻¹) ^ (2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t χ)) (LB.invGen D.P.L _ _ (g.t χ))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))
      (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))))
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
    obtain ⟨h₁, h₂⟩ := ratio_invariant g g' Φ hp χ χ' hker r r' z J J' hJ hJ' h
    have hWeq : (fun k => r ≫ D'.Oφ g'.pG χ' k) = (fun k => r' ≫ D'.Oφ g'.pG χ' k) :=
      funext (Oφ_congr χ' g'.pG r r' h₁)
    rw [hu' Z r z J hJ, hu' Z r' z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
      hW Z r z J J' hJ hJ', hW Z r' z J J' hJ hJ', hWeq]
    calc _ = W Z z (fun k => r' ≫ D'.Oφ g'.pG χ' k) J J' *
          (val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹) ^ 2 := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel
      _ = _ := by
          rw [h₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel)
  exact ⟨v, hv⟩

end GlobalTheory.SqCompare

open GlobalTheory.CoordCompare in

theorem GlobalTheory.SqCompare.c_two_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' hL Φ w hw hΦ hpG xe hval x
  obtain ⟨hN, -, hC, -⟩ := hR
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hpG e)
  have hmono : Mono Φ.hom.left := inferInstance
  set a := D'.toPre.c x ≫ Φ.hom
  set b := D.toPre.c (xe x)
  have desc : ∀ n, ∃ v : LB.Gen (LB.LinComb D.toPre.P.L
      (diffφ (D.toPre.prBe (maximalIdeal R) n) (a * a) (b * b)) ![1, -1, 1, -1]), v.IsGen := fun n => by
    obtain ⟨v, hv⟩ := GlobalTheory.SqCompare.sq_desc (U.gt n) (U'.gt n) Φ.hom (hp' n) w hw (xe x) x
      (fun Z r z J J' hJ hJ' h h' => hval n Z r z J J' hJ hJ' h h' x)
    exact GlobalTheory.SqCompare.sq_law D.toPre.P.isLB ⟨D.toPre.cub.t, D.toPre.cub.isGen⟩ _ _ _ v hv
  have hab : a * a = b * b := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
      D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ (a * a)) (toUnit _ ≫ (b * b)) fun n => by
        obtain ⟨v, hv⟩ := desc n
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
            pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.toPre.P.A] ≫ ·) h
  have e1 : D'.toPre.c (2 • x) ≫ Φ.hom = a * a := by
    rw [two_nsmul, D'.toPre.c_add, padd, ← Hom.mul_def, MonObj.mul_comp]
  have e2 : D.toPre.c (xe (2 • x)) = b * b := by
    rw [map_nsmul, two_nsmul, D.toPre.c_add, padd, ← Hom.mul_def]
  rw [e1, e2, hab]
