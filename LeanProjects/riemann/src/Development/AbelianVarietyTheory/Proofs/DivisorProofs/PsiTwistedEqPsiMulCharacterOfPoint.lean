import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwPsi

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point

variable {R : Type} [CommRing R] [IsDomain R]

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem cancel {A : Type} [CommRing A] [IsDomain A] {S S₂ : A} {ψ rig G N W Wc W1 ψ₂ rig₂ : Aˣ} (hs : S₂ ≠ 0)
    (e : S * (ψ * rig).val * (G * N).val = (W * Wc⁻¹ * W1).val * (S₂ * (ψ₂ * rig₂).val))
    (e4 : S * N.val = W.val * S₂) : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂) := by
  refine Units.ext (mul_left_cancel₀ (mul_ne_zero W.ne_zero hs) ?_)
  simp only [Units.val_mul] at e ⊢
  linear_combination e - ((ψ : A) * G * rig) * e4

theorem core {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ))
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β g.b) twε))
    (f : ∀ α : D.X, D.SecB 1 α) (f₂ : ∀ α : D₂.X, D₂.SecB 1 α)
    (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]))
    (h : LevelOneEq D f) (h₂ : LevelOneEq D₂ f₂)
    (hf : ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
      (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' →
      sval (f (xe χ)) (r ≫ twφ D₂ D β g.b 0) z J *
        (val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * sval (f₂ χ) r z J')
    [IsIntegral (DegPre.BF D₂ (FractionRing R)).left]
    (χ : D₂.X) (z : (DegPre.BF D₂ (FractionRing R)).left) (J : _ → D.P.L.ι) (J' : _ → D₂.P.L.ι)
    (hJ : Good D.P.L z J) (hJ' : Good D₂.P.L z J')
    (ne : sval (f₂ 0) (DegPre.prB D₂ (FractionRing R)).left z J' ≠ 0) :
    val (D.psi (xe χ)) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J *
        val (g.s (xe χ)) (toUnit (DegPre.BF D₂ (FractionRing R))).left z J *
        val D.rig (DegPre.BF D₂ (FractionRing R)).hom z J =
      (wv w (cP D₂ (DegPre.BF D₂ (FractionRing R)) χ).left z J J')⁻¹ *
        wv w (1 : DegPre.BF D₂ (FractionRing R) ⟶ D₂.P.A).left z J J' *
        (val (D₂.psi χ) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J' *
          val D₂.rig (DegPre.BF D₂ (FractionRing R)).hom z J') := by
  let T := DegPre.BF D₂ (FractionRing R)
  let κ : T ⟶ TF (R := R) (FractionRing R) := fst _ _
  let Φ : D₂.P.A ⟶ D.P.A := padd D.P.A β (toUnit D₂.P.A ≫ g.b)
  have hΦ : ∀ u : T ⟶ D₂.P.A, u ≫ Φ = (u ≫ β) * (toUnit T ≫ g.b) := fun u => by
    show u ≫ (β * (toUnit D₂.P.A ≫ g.b)) = _
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  have hU : ∀ u : T ⟶ D₂.P.A, u.left ≫ (toUnit D₂.P.A).left = (toUnit T).left := fun u => by
    rw [← Over.comp_left, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ D₂.P.A, y * cP D₂ T χ = DegPre.prB D₂ (FractionRing R) :=
    ⟨_, inv_mul_cancel_right _ _⟩
  have hyΦ : (y ≫ Φ) * cP D T (xe χ) = DegPre.prB D₂ (FractionRing R) ≫ Φ := by
    rw [hΦ, hΦ, ← hy, MonObj.mul_comp, cP_comp β (hc χ), mul_right_comm]
  have e₁ := h (xe χ) 0 rfl T κ (y ≫ Φ) z J hJ
  have e₂ := h₂ χ 0 rfl T κ y z J' hJ'
  have e₃ := hf χ _ y.left z J J' hJ hJ'
  have e₄ := hf 0 _ (DegPre.prB D₂ (FractionRing R)).left z J J' hJ hJ'
  have p₃ := prod_famB D₂ y χ (fun q => wv w q z J J')
  have p₄ := prod_famB D₂ (DegPre.prB D₂ (FractionRing R)) 0 (fun q => wv w q z J J')
  rw [hy] at p₃ e₂
  rw [cPoint_zero, _root_.mul_one, inv_mul_cancel_right] at p₄
  rw [hyΦ] at e₁
  change _ = (∏ κ, wv w (y.left ≫ D₂.famφB χ κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₃
  change _ = (∏ κ, wv w ((DegPre.prB D₂ (FractionRing R)).left ≫ D₂.famφB 0 κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₄
  rw [p₃, hU, show y.left ≫ twφ D₂ D β g.b 0 = (y ≫ Φ).left from rfl, e₁, e₂] at e₃
  rw [p₄, hU, map_zero xe, val_corr hJ g.s_zero, val_one, _root_.one_mul,
    show (DegPre.prB D₂ (FractionRing R)).left ≫ twφ D₂ D β g.b 0 = (DegPre.prB D₂ (FractionRing R) ≫ Φ).left from rfl] at e₄
  exact cancel ne e₃ e₄

theorem grp {U : Type} [CommGroup U] {ψ0 ψ₂0 rig rig₂ W1 ψ G Wc ψ₂ : U} (h0 : ψ0 = W1⁻¹ * ψ₂0)
    (c0 : ψ0 * rig = ψ₂0 * rig₂) (c : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂)) : ψ * G = Wc⁻¹ * ψ₂ := by
  subst h0
  apply Additive.ofMul.injective
  have e0 := congrArg Additive.ofMul c0
  have e := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at e0 e ⊢
  linear_combination (norm := abel) e - e0

theorem formEq {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ)) (χ : D₂.X) :
    FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (xe χ)))
        (fun k => (toUnit (TK R)).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) k))
      (Sum.elim (fun _ => -1) DegPre.gtε) (fun i => D₂.xK χ ≫ twφ D₂ D β g.b i) (fun i => -1 * twε i) := by
  let u := toUnit (TK R)
  have k : ∀ a : TK R ⟶ 𝟙_ (Over (Sp R)), a = u := fun a => toUnit_unique _ _
  have m0 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 0 = D₂.xK χ ≫ twφ D₂ D β g.b 0 := by
    show u.left ≫ ((toUnit _ ≫ D.c (xe χ)) * g.b).left = (u ≫ D₂.c χ).left ≫ (β * (toUnit _ ≫ g.b)).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [MonObj.comp_mul, ← Category.assoc]
    rw [k (u ≫ toUnit _), k ((u ≫ D₂.c χ) ≫ toUnit _), Category.assoc, hc]
  have m1 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 1 = ptK (D.c (xe χ)) := by
    show u.left ≫ (toUnit _ ≫ D.c (xe χ)).left = (u ≫ D.c (xe χ)).left
    rw [← Over.comp_left, ← Category.assoc, k (u ≫ toUnit _)]
  have m2 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 2 = D₂.xK χ ≫ twφ D₂ D β g.b 1 := by
    show u.left ≫ g.b.left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ g.b).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, k ((u ≫ D₂.c χ) ≫ toUnit _)]
  have m3 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 3 = D₂.xK χ ≫ twφ D₂ D β g.b 2 := by
    show u.left ≫ (toUnit _ ≫ η[D.P.A]).left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, ← Category.assoc, k (u ≫ toUnit _),
      k ((u ≫ D₂.c χ) ≫ toUnit _)]
  intro U _ h
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Fintype.prod_unique, Sum.elim_inl,
    Sum.elim_inr]
  rw [m0, m1, m2, m3]
  simp only [DegPre.gtε, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_succ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

end GlobalTheory.MumCmp.TwPsi

namespace GlobalTheory.MumCmp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point GlobalTheory.MumCmp.TwPsi in

theorem psi_maps_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ _ D D₂ g β hβ xe hc w hw ⟨t₀, m₀, c₀⟩ f f₂ ν _ h h₂ hne hf χ
  have hL := D.toPre.P.isLB
  have hL' := D₂.toPre.P.isLB
  have := D₂.toPre.P.isAb.smooth
  have := D₂.toPre.P.isAb.geomConnected
  have : IsIntegral (DegPre.BF D₂.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D₂.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D₂.toPre.P.A.hom).flip
  let T := DegPre.BF D₂.toPre (FractionRing R)
  let π : T.left ⟶ (TK R).left :=
    (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)
  have hπ : π ≫ jK R = T.hom := by
    rw [Category.assoc]; exact Over.w (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A)
  have hT0 : π ≫ D₂.toPre.xK 0 = (1 : T ⟶ D₂.toPre.P.A).left := by
    rw [Uniq.xK_zero, ← Category.assoc, hπ]; rfl
  have hTχ : π ≫ D₂.toPre.xK χ = (cP D₂.toPre T χ).left := by
    let k : T ⟶ TK R := Over.homMk π hπ
    exact congrArg (fun q => q.left) (comp_cP D₂.toPre k χ)
  have hTU : π ≫ (toUnit (TK R)).left = (toUnit T).left := by
    rw [toUnit_left_eq, toUnit_left_eq]; exact hπ
  have key : ∀ (z : T.left) J J', Good D.toPre.P.L z J → Good D₂.toPre.P.L z J' →
      val (D.toPre.psi (xe χ)) π z J * val (g.s (xe χ)) (π ≫ (toUnit (TK R)).left) z J =
        (wv w (π ≫ D₂.toPre.xK χ) z J J')⁻¹ * val (D₂.toPre.psi χ) π z J' := by
    intro z J J' hJ hJ'
    have ne : sval (f₂ 0) (DegPre.prB D₂.toPre (FractionRing R)).left z J' ≠ 0 := fun e => hne (h₂.eq_zero z hJ' e)
    have cχ := core g β.hom xe hc w f f₂ ν h h₂ hf χ z J J' hJ hJ' ne
    have c0 := core g β.hom xe hc w f f₂ ν h h₂ hf 0 z J J' hJ hJ' ne
    rw [map_zero xe, val_corr hJ g.s_zero, val_one, _root_.mul_one, cPoint_zero, inv_mul_cancel, _root_.one_mul] at c0
    have h0 : val (D.toPre.psi 0) π z J = (wv w (π ≫ D₂.toPre.xK 0) z J J')⁻¹ * val (D₂.toPre.psi 0) π z J' := by
      have e := Uniq.gm_mapsAtExp m₀ π z (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
        (J' (π ≫ D₂.toPre.xK 0)) (Set.mem_iInter.2 fun k => hJ _) (hJ' _)
      rw [← val_of t₀ π z J (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
          (fun k => congrArg J (Category.assoc π _ _).symm), val_corr hJ c₀, val_mul hJ, val_pull hJ,
        val_corr hJ g.s_zero, val_one, _root_.mul_one] at e
      rw [e, zpow_neg_one]; rfl
    rw [hT0] at h0
    rw [hTχ, hTU]
    exact grp h0 c0 cχ
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_gen hL (formEq g β.hom xe hc χ)
    (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))
    (mulGen_isGen _ _ _ _ _ _ _ (D.toPre.psi_gen _) (pullGen_isGen _ _ _ _ (g.isGen _) _))
  have R₁ := reg_val (L' := D₂.toPre.P.L) ht₁ π
  have R₂ := reg_wv (L := D.toPre.P.L) (L' := D₂.toPre.P.L) hw (π ≫ D₂.toPre.xK χ)
  have R₃ := (reg_val' (L := D.toPre.P.L) (D₂.toPre.psi_gen χ) π).inv
  obtain ⟨a, ha⟩ := ((R₁.mul R₂).mul R₃).glue hL hL' (fun U _ h h' => by
    simp only [Category.assoc, Fintype.prod_unique, zpow_neg_one, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_prod, ofMul_one]
    simp only [neg_mul, _root_.one_mul, neg_zsmul, Finset.sum_neg_distrib]
    abel)
  have ha1 : a = 1 := unit_ext fun x _ => by
    obtain ⟨J, hJ⟩ := good_exists hL x
    obtain ⟨J', hJ'⟩ := good_exists hL' x
    rw [← ha _ (𝟙 _) x J J' hJ hJ', map_one]
    show val t₁ (𝟙 _ ≫ π) x J * wv w (𝟙 _ ≫ π ≫ D₂.toPre.xK χ) x J J' * (val (D₂.toPre.psi χ) (𝟙 _ ≫ π) x J')⁻¹ = 1
    rw [Category.id_comp, Category.id_comp, hv₁ _ _ x J hJ, val_mul hJ, val_pull hJ, key x J J' hJ hJ']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have H : ∀ (y : (TK R).left) J J', Good D.toPre.P.L y J → Good D₂.toPre.P.L y J' →
      val t₁ (𝟙 _) y J = wv w (D₂.toPre.xK χ) y J J' ^ (-1 : ℤ) * val (D₂.toPre.psi χ) (𝟙 _) y J' := by
    intro y J J' hJ hJ'
    have e := ha _ (DegPre.zF D₂.toPre (FractionRing R)).left y J J' hJ hJ'
    rw [ha1, map_one] at e
    have hz : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π = 𝟙 _ := PsiCompare.zF_fst D₂.toPre
    change val t₁ ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J *
      wv w ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ) y J J' *
      (val (D₂.toPre.psi χ) ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J')⁻¹ = 1 at e
    have hz' : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ = D₂.toPre.xK χ := by
      rw [← Category.assoc (DegPre.zF D₂.toPre (FractionRing R)).left π, hz, Category.id_comp]
    rw [hz', hz] at e
    rw [zpow_neg_one, ← mul_inv_eq_one, mul_inv, inv_inv, ← _root_.mul_assoc]
    exact e
  exact ⟨t₁, mapsAtExp_of_val hL hL' hw (D₂.toPre.psi_gen χ) ht₁ H, corr_of_val hL fun y J hJ => hv₁ _ _ y J hJ⟩

end GlobalTheory.MumCmp
