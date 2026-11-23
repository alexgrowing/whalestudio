import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportLinCombIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSumTwistCubeIdentityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslC

theorem exists_flat_transport : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := GlobalTheory.T.exists_generator_transport_linCombIso

theorem formEq_twist : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := GlobalTheory.T.formalSum_twist_cube_identity

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def θpt (g : GtCoord I D e G) (C b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ G3 D.P.A :=
  lift g.pG (lift (toUnit _ ≫ C) (toUnit _ ≫ b))

theorem θpt_congr (g : GtCoord I D e G) (C b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) {Z : Scheme.{0}}
    (r r' : Z ⟶ (thickObj R I e G).left) (h : r ≫ g.pG.left = r' ≫ g.pG.left) :
    r ≫ (θpt g C b).left = r' ≫ (θpt g C b).left := by
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hw : r ≫ T.hom = r' ≫ T.hom := by rw [← Over.w g.pG, reassoc_of% h]
  let a : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r hw
  let a' : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r' rfl
  have ha : a ≫ g.pG = a' ≫ g.pG := Over.OverMorphism.ext h
  have hu : a ≫ toUnit T = a' ≫ toUnit T := toUnit_unique _ _
  have : a ≫ θpt g C b = a' ≫ θpt g C b := by
    simp only [θpt, comp_lift, ha, ← Category.assoc]
    rw [toUnit_unique (a ≫ toUnit _) (a' ≫ toUnit _)]
  exact congrArg (fun q => q.left) this

theorem exists_ratio_gen (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (hp : g₂.pG ≫ β = g.pG) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β b) twε)) (hw : w.IsGen) (χ₂ : D₂.X) (χ : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ CoordCompare.diffφ (D.prBe I e) (D₂.c χ₂ ≫ β) (D.c χ) k)
      ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
        Good D.P.L z J → Good D₂.P.L z J' →
        val u r z J = (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ twφ D₂ D β b i))
          (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' *
          val D.cub.t (r ≫ (θpt g (D₂.c χ₂ ≫ β) b).left) z J * (val (g.t χ) r z J)⁻¹ := by
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_flat_transport D.P.isLB D₂.P.isLB _ _ w hw _ _ (g₂.t χ₂) (g₂.t_gen χ₂)
  have hF := formEq_twist D₂ D ((Over.map (thick R I e)).map g.q) (D.prBe I e) g₂.pG β hp b χ₂ χ
  obtain ⟨u, hu, hv⟩ := exists_gen D.P.isLB hF
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (θpt g (D₂.c χ₂ ≫ β) b).left))
      (LB.invGen D.P.L _ _ (g.t χ)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁
      (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)) (DVR.invGen_isGen _ _ _ _ (g.t_gen χ)))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  exact (hv Z r z J hJ).trans ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ r).trans
    (congrArg₂ (· * ·) (hv₁ Z r z J J' hJ hJ') (val_pull hJ _ _ r))) (val_inv _ r)))

theorem rearr {U : Type} [CommGroup U] (W a θ c : U) : W * a * θ * c⁻¹ = W * θ * (a * c⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_desc_gen (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    [Mono β.left] (hp : g₂.pG ≫ β = g.pG) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β b) twε)) (hw : w.IsGen) (χ₂ : D₂.X) (χ : D.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A →
      val (g.t χ) r z J = val (g₂.t χ₂) r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (CoordCompare.diffφ (D.prBe I e) (D₂.c χ₂ ≫ β) (D.c χ)) ![1, -1, 1, -1]),
      v.IsGen := by
  obtain ⟨u, hu, hu'⟩ := exists_ratio_gen g g₂ β hp b w hw χ₂ χ
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := CoordCompare.exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.P.L D₂.P.isLB z
    obtain ⟨h₁, h₂⟩ := CoordCompare.ratio_invariant g g₂ β hp χ χ₂ hker r r' z J J' hJ hJ' h
    have h₀ : r ≫ g.pG.left = r' ≫ g.pG.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.prBe I e).left) h).trans (Category.assoc _ _ _))
    rw [hu' Z r z J J' hJ hJ', hu' Z r' z J J' hJ hJ', θpt_congr g _ b r r' h₀, rearr, rearr, h₂]
    congr 2
    exact Finset.prod_congr rfl fun k _ => by rw [CoordCompare.Oφ_congr χ₂ g₂.pG r r' h₁ k])
  exact ⟨v, hv⟩

end Level

theorem c_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ) := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hlift A₂ D₂ U₂ hL β hβ hp xe hker w hw χ
  obtain ⟨⟨_, -, -, _⟩, -⟩ := hR
  have : Mono β.hom.left := inferInstance
  have hp' : ∀ e, (U₂.gt e).pG ≫ β.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hp e)
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  have := D.toPre.P.isAb.proper
  have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
    D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ D₂.toPre.c χ ≫ β.hom) (toUnit _ ≫ D.toPre.c (xe χ)) fun n => by
      obtain ⟨v, hv⟩ := exists_desc_gen (U.gt n) (U₂.gt n) β.hom (hp' n) g.b w hw χ (xe χ)
        (fun Z r z J J' hJ hJ' h h' => hker n Z r z J J' hJ hJ' h h' χ)
      have h₁ := CoordCompare.thick_eq _ _ v hv
      have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
          pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
  simpa using congrArg (η[D.toPre.P.A] ≫ ·) h

end GlobalTheory.MumCmp.TranslC
