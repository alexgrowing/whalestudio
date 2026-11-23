import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSecondPartialLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushSecondLaw

open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw

section Values

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
  {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}

theorem val_pmaps {φ : K → (Y ⟶ X)} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : PMaps w φ' φ ε a t h) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val t (r ≫ h) z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val a r z J' := by
  have e := H _ r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ _) (fun k => hJ' _)
  refine Eq.trans ?_ e
  refine val_of _ _ _ _ _ fun k => congrArg J ?_
  rw [Category.assoc, Category.assoc, hc]

theorem val_carries {g : LB.Gen (LB.LinComb L' φ' ε)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)}
    (H : Carries L F w φ' ε g c) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val c r z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val g r z J' := by
  have P : PMaps w φ' (fun k => φ' k ≫ F) ε g c (𝟙 Y') :=
    (maps_iff w φ' _ ε g c (𝟙 Y') (flatGen L F φ' ε c) (fun j => wchart_pull_le L F φ' j) (fun j => rfl)).1 H
  have e := val_pmaps P (fun k => (Category.id_comp _).symm) hJ hJ' r
  rwa [Category.comp_id] at e

end Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem val_scaleGenG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
    (c : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

set_option maxHeartbeats 4000000 in

theorem prod_second_law {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) ^ cε 2 I) :
    ∏ I, h ((lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3))
        (jptG t x0 d x m (0 : Fin 3)))).left ≫ thφ t.G (x3 t.G) I) ^ thε I =
      P ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] *
        ((P ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])⁻¹ *
          (P ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])⁻¹) := by
  have hQ : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h (psum t.G
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m,
        Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m] I.down).left ^ cε 2 I := fun φ => by
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    exact (hP φ).trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (pe_pt m _ I))
  simp only [hQ, th_pt, Matrix.cons_val_zero, Matrix.cons_val_one, pt_X, pt_law hch]
  erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  rw [prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
    prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  have ha2 : jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3) =
      jptG t x0 d x m (1 : Fin 3) * (jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3)) := _root_.mul_assoc _ _ _
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
  erw [ha2]
  abel!

theorem lift_comp_cube {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (n : CubeMap G G') {T : Over S} {a b c : T ⟶ G} {a' b' c' : T ⟶ G'} (ha : a'.left = a.left ≫ n.F)
    (hb : b'.left = b.left ≫ n.F) (hc : c'.left = c.left ≫ n.F) :
    (lift a' (lift b' c')).left = (lift a (lift b c)).left ≫ n.F3 := hom_ext_triple _ fun i => by
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  fin_cases i
  · simpa [x3] using ha
  · simpa [x3] using hb
  · simpa [x3] using hc

theorem alg_step {U : Type} [CommGroup U] {θ θ' u A B C A' B' C' p a b c : U} (k : θ = u * (A * (B⁻¹ * C⁻¹)))
    (hθ : θ' = p * θ) (hA : A' = a * A) (hB : B' = b * B) (hC : C' = c * C) (hp : p = a * (b⁻¹ * c⁻¹)) :
    θ' = u * (A' * (B'⁻¹ * C'⁻¹)) := by
  subst k hθ hA hB hC hp
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem famPh2_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh2 t (𝟙 (Sp V)) d x F ph e → FamPh2 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hcub hx _ hfr F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J' hJ' => ?_⟩
  choose J hJ using fun χ : (jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  replace hJ : Good t.PP.L y J := hJ
  obtain ⟨W, hW⟩ : ∃ W : ((jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left) → ((jOG (𝟙 (Sp V)) d m 3).left.presheaf.stalk y)ˣ,
    W = fun q => gw w q y (J' (q ≫ n.φ)) (J q) := ⟨_, rfl⟩
  obtain ⟨-, c, -, hc, hcar⟩ := hfr m
  have hpt : ∀ i : Fin 3, (jptG t' (𝟙 (Sp V)) d x' m i).left = (jptG t (𝟙 (Sp V)) d x m i).left ≫ n.φ := fun i => by
    rw [jptG, jptG, Over.comp_left, Over.comp_left, hx m, Category.assoc]
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J' =
        (∏ I : ULift.{0} (Finset (Fin 2)), W ((homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I) ^ cε 2 I) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J := fun φ => by
    refine (val_pull hJ' _ _ _).trans ((val_corr hJ' hc _).symm.trans ((val_carries hcar hJ' hJ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ (val_pull hJ _ _ _).symm
    rw [hW, Category.id_comp]
  have P : PMaps w (thφ t.G (x3 t.G)) (thφ t'.G (x3 t'.G)) thε t.cub.t t'.cub.t n.cm.F3 :=
    (maps_iff w _ _ thε t.cub.t t'.cub.t n.cm.F3 _ (fun j => n.cm.theta_le t'.PP.L j) (fun j => rfl)).1 hcub.2
  have hθ := val_pmaps P (fun I => n.cm.psum_comm I.down) hJ' hJ
    (lift (jptG t (𝟙 (Sp V)) d x m (1 : Fin 3)) (lift (jptG t (𝟙 (Sp V)) d x m (2 : Fin 3))
      (jptG t (𝟙 (Sp V)) d x m (0 : Fin 3)))).left
  rw [← hW, ← lift_comp_cube n.cm (hpt 1) (hpt 2) (hpt 0)] at hθ
  have k := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hcor (𝟙 _)).trans ((val_scaleGenG t hJ _ _ _).trans
    (congrArg _ ((val_mul hJ _ _ _).trans (congrArg _ ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  rw [Category.id_comp] at k
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ ((val_scaleGenG t' hJ' _ _ _).trans
    (congrArg _ ((val_mul hJ' _ _ _).trans (congrArg _ ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  rw [Category.id_comp]
  exact alg_step k hθ (hpe _) (hpe _) (hpe _) (prod_second_law hch m W _ (fun _ => rfl))

end GlobalTheory.PushSecondLaw
