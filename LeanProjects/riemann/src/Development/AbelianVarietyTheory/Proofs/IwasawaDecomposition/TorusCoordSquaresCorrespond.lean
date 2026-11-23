import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TSq

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.LamBiext

section Generic

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_sqGen (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) φ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        val u r z (fun q _ => J q) = val t r z J ^ 2 := by
  have hF : FormEq (Sum.elim φ φ) (Sum.elim ε ε) (flatφ (fun _ : Fin 1 => 𝟙 X) φ)
      (flatε (fun _ : Fin 1 => (2 : ℤ)) ε) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, flatφ, flatε, Category.comp_id]
    rw [zpow_mul, zpow_two]
  obtain ⟨s, hs, hv⟩ := exists_gen hL hF (LB.mulGen L φ ε φ ε t t) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht)
  refine ⟨nest L _ _ _ _ s, nest_isGen hs, fun Z r z J hJ => ?_⟩
  rw [val_nest hs r (GlobalTheory.SqCube.good_sq hJ) hJ, hv _ _ z J hJ, val_mul hJ]
  simp only [GlobalTheory.SqCube.adj_sq hL hJ, one_zpow, Finset.prod_const_one, _root_.one_mul]
  exact (sq _).symm

theorem eq_of_ratio_inv {Y' S₀ : Scheme.{0}} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) [Flat m]
    [Surjective m] [QuasiCompact m] (p : Y ⟶ S₀) (e₀ : S₀ ⟶ Y') (he : (e₀ ≫ m) ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (u u' : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε))
    (hu : u.IsGen) (hu' : u'.IsGen)
    (hinv : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ Y') (z : Z), r ≫ m = r' ≫ m → ∃ J, Good L z J ∧
      val u r z J * (val u' r z J)⁻¹ = val u r' z J * (val u' r' z J)⁻¹)
    (h₁ : ∀ y : S₀, ∃ J, Good L y J ∧ val u e₀ y J = val u' e₀ y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J) (hJ : Good L z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := fun k => m ≫ (PEmpty.elim k : Y ⟶ X))
    (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have tv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J J' : (Z ⟶ X) → L.ι), val t r z J = val t r z J' :=
    fun Z r z J J' => by
      rw [val_of t r z J PEmpty.elim (fun k => k.elim), val_of t r z J' PEmpty.elim (fun k => k.elim)]
  have rv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      val t r z J = val u r z J * (val u' r z J)⁻¹ :=
    fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv]
  obtain ⟨v, hvg, hvv⟩ := CoordCompare.exists_gen_of_val_eq hL (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim m t ht
    (fun Z r r' z J hJ h => by
      obtain ⟨J₀, hJ₀, e⟩ := hinv Z r r' z h
      rw [tv Z r z J J₀, tv Z r' z J J₀, rv _ _ _ _ hJ₀, rv _ _ _ _ hJ₀, e])
  have one := gen_unique hL p (e₀ ≫ m) he hp hvg (u' := LB.oneGen L (Y := Y))
    (isGen_of_gm _ fun y j j' _ _ => (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _)
      (map_one _)).trans (_root_.mul_one _)))) (fun y J hJ => by
      obtain ⟨J₀, hJ₀, e⟩ := h₁ y
      rw [hvv _ e₀ y J hJ, val_one, tv _ e₀ y J J₀, rv _ _ _ _ hJ₀, e, mul_inv_cancel])
  have := (rv Z r z J hJ).symm.trans ((hvv Z r z J hJ).symm.trans ((one Z (r ≫ m) z J hJ).trans (val_one _)))
  exact mul_inv_eq_one.1 this

end Generic

end GlobalTheory.TSq

namespace GlobalTheory.TSq

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem sq_ratio {V : Type} [CommGroup V] {a b a' b' O : V} (h : b * a⁻¹ = b' * a'⁻¹) :
    a ^ 2 * (O * b ^ 2)⁻¹ = a' ^ 2 * (O * b' ^ 2)⁻¹ := by
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e ⊢
  linear_combination (norm := abel) (-2 : ℤ) • e

end GlobalTheory.TSq

open GlobalTheory.TSq ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.torus_coord_squares_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ β : D'.toPre.X, D'.toPre.c (2 • β) ≫ Φ.hom = D.toPre.c (xe (2 • β)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val ((U.gt e).t (xe (2 • β))) r z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' Φ w hw hΦ hpG xe hMatch β hc e Z r z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM := DVR.linComb_isLB (Y := D.toPre.P.A.left) _ hL (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)
  have hM' := DVR.linComb_isLB (Y := D'.toPre.P.A.left) _ hL' (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left)
    (fun _ => 2)
  have hp' : (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := Over.OverMorphism.ext (hpG e)
  haveI : Mono Φ.hom.left := ⟨fun a b h => by
    have k := congrArg (· ≫ Φ.inv.left) h
    simp only [Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id] at k
    exact k⟩
  haveI := (U.gt e).q_flat
  haveI := (U.gt e).q_surj
  haveI := (U.gt e).q_affine
  obtain ⟨T, hT, vT⟩ := exists_sqGen hL ((U.gt e).t (xe (2 • β))) ((U.gt e).t_gen _)
  obtain ⟨T', hT', vT'⟩ := exists_sqGen hL' ((U'.gt e).t (2 • β)) ((U'.gt e).t_gen _)
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_up ((isGen_iff w).1 hw) hM hM' T' hT'
  have hφ : ∀ k, D.toPre.Oφ (U.gt e).pG (xe (2 • β)) k =
      (U.gt e).q.left ≫ D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R _ e)).map (U.gt e).q) (D.toPre.prBe _ e) _ k).symm
  have hψ : ∀ k, D'.toPre.Oφ (U'.gt e).pG (2 • β) k ≫ Φ.hom.left = D.toPre.Oφ (U.gt e).pG (xe (2 • β)) k := by
    intro k
    rw [CoordCompare.Oφ_comp_hom, hp', hc]
    rfl
  obtain ⟨a, ha, va⟩ := exists_gen hM
    (φ' := fun k => (U.gt e).q.left ≫ D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k) (ε' := Oinvε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by rw [hφ k]) T hT
  obtain ⟨b, hb, vb⟩ := exists_gen hM
    (φ' := fun k => (U.gt e).q.left ≫ D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k) (ε' := Oinvε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => by rw [hψ k, hφ k]) t₁ ht₁
  have va' : ∀ {Z : Scheme.{0}} (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J → val a r z (fun q _ => J q) = val ((U.gt e).t (xe (2 • β))) r z J ^ 2 :=
    fun r z J hJ => (va _ r z _ (GlobalTheory.SqCube.good_sq hJ)).trans (vT _ r z J hJ)
  have vb' : ∀ {Z : Scheme.{0}} (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      val b r z (fun q _ => J q) = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
    intro Z r z J J' hJ hJ'
    have hJP := GlobalTheory.SqCube.good_sq hJ
    have hJP' := GlobalTheory.SqCube.good_sq hJ'
    rw [vb _ r z _ hJP, ← vT' _ r z J' hJ']
    refine (hv₁ _ r z _ _ (hJP.mem _ r) (hJP'.mem _ r)).trans ?_
    simp only [pw, ExpTrans.om, Category.assoc]
    rfl

  have hinv : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z),
      r ≫ (U.gt e).q.left = r' ≫ (U.gt e).q.left → ∃ JP, Good (LB.LinComb D.toPre.P.L (K := Fin 1)
        (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)) z JP ∧
        val a r z JP * (val b r z JP)⁻¹ = val a r' z JP * (val b r' z JP)⁻¹ := by
    intro Z r r' z h
    choose J₀ hJ₀ using fun ψ : Z ⟶ D.toPre.P.A.left => exists_chart hL (ψ z)
    choose J₀' hJ₀' using fun ψ : Z ⟶ D'.toPre.P.A.left => exists_chart hL' (ψ z)
    have hJ₀ : Good D.toPre.P.L z J₀ := hJ₀
    have hJ₀' : Good D'.toPre.P.L z J₀' := hJ₀'
    obtain ⟨h₁, h₂⟩ := CoordCompare.ratio_invariant (U.gt e) (U'.gt e) Φ.hom hp' (xe (2 • β)) (2 • β)
      (fun Z r z J J' hJ hJ' c c' => hMatch e Z r z J J' hJ hJ' c c' (2 • β)) r r' z J₀ J₀' hJ₀ hJ₀' h
    refine ⟨fun q _ => J₀ q, GlobalTheory.SqCube.good_sq hJ₀, ?_⟩
    rw [va' r z J₀ hJ₀, va' r' z J₀ hJ₀, vb' r z J₀ J₀' hJ₀ hJ₀', vb' r' z J₀ J₀' hJ₀ hJ₀']
    have ho : (∏ κ, ExpTrans.om w z (fun q _ => J₀ q) (fun q _ => J₀' q)
        (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) = ∏ κ, ExpTrans.om w z (fun q _ => J₀ q)
        (fun q _ => J₀' q) (r' ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ :=
      Finset.prod_congr rfl fun κ _ => by rw [CoordCompare.Oφ_congr (2 • β) (U'.gt e).pG r r' h₁ κ]
    rw [ho]
    exact sq_ratio h₂
  have hone : ∀ y : (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left, ∃ JP,
      Good (LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)) y JP ∧
      val a (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y JP =
      val b (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y JP := by
    intro y
    choose J₀ hJ₀ using fun ψ : (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ⟶
      D.toPre.P.A.left => exists_chart hL (ψ y)
    choose J₀' hJ₀' using fun ψ : (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ⟶
      D'.toPre.P.A.left => exists_chart hL' (ψ y)
    have hJ₀ : Good D.toPre.P.L y J₀ := hJ₀
    have hJ₀' : Good D'.toPre.P.L y J₀' := hJ₀'
    refine ⟨fun q _ => J₀ q, GlobalTheory.SqCube.good_sq hJ₀, ?_⟩
    have u₁ : val ((U.gt e).t (xe (2 • β))) (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀ = 1 :=
      TorusCoord.val_unit (U.gt e) (Z := Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))) _ hJ₀
    have u₂ : val ((U'.gt e).t (2 • β)) (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀' = 1 :=
      TorusCoord.val_unit (U'.gt e) (Z := Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))) _ hJ₀'
    have a₁ := va' (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀ hJ₀
    have b₁ := vb' (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J₀ J₀' hJ₀ hJ₀'
    refine (a₁.trans ((congrArg (· ^ 2) u₁).trans (one_pow 2))).trans (Eq.trans ?_ b₁.symm)
    refine Eq.trans ?_ (congrArg (_ * ·) ((congrArg (· ^ 2) u₂).trans (one_pow 2))).symm
    rw [_root_.mul_one]
    let Tt := (Over.map (thick R (maximalIdeal R) e)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))))
    let f := fun ψ => ExpTrans.om w y (fun q _ => J₀ q) (fun q _ => J₀' q) ψ
    have e0 : ∀ k, (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) k =
        D'.toPre.Oφ (1 : Tt ⟶ D'.toPre.P.A) (2 • β) k :=
      fun k => (WeightPf.Oφ_comp ((Over.map (thick R _ e)).map 1) (U'.gt e).pG _ k).trans
        (congrArg (D'.toPre.Oφ · _ k) (TorusCoord.im_one (U'.gt e)))
    refine Eq.symm ((Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_)
    rw [Fin.prod_univ_four]
    show f ((1 : Tt ⟶ D'.toPre.P.A) * (toUnit Tt ≫ D'.toPre.c (2 • β))).left ^ (-1 : ℤ) *
      f (toUnit Tt ≫ D'.toPre.c (2 • β)).left ^ (1 : ℤ) * f (1 : Tt ⟶ D'.toPre.P.A).left ^ (1 : ℤ) *
      f (1 : Tt ⟶ D'.toPre.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  have key := eq_of_ratio_inv hM (fun k => D.toPre.Oφ (D.toPre.prBe _ e) (xe (2 • β)) k) Oinvε (U.gt e).q.left
    (thickObj R (maximalIdeal R) e D.toPre.P.A).hom
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G).left
    (Over.w ((1 : Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
      thickObj R (maximalIdeal R) e G) ≫ (U.gt e).q))
    (GlobalTheory.globalFns_holds _ _ (TLinPf.isAb_pullback _ _ D.toPre.P.isAb)).2 a b ha hb hinv hone Z r z
    (fun q _ => J q) (GlobalTheory.SqCube.good_sq hJ)
  rw [va' r z J hJ, vb' r z J J' hJ hJ'] at key
  exact key
