import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapId
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.PushAd

section Bundles
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}

def wv {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (χ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ :=
  gw w χ z (J (χ ≫ F)) (J' χ)

theorem val_carries {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)}
    (h : Carries L F w φ ε g g') {Z : Scheme.{0}} (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}
    (hJ : Good L z J) (hJ' : Good L' z J') :
    val g' r z J = (∏ k, wv w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have H := (maps_iff w φ (fun k => φ k ≫ F) ε g g' (𝟙 Y) (flatGen L F φ ε g') (wchart_pull_le L F φ)
    (fun j => congrArg (res (wchart_pull_le L F φ j)) (Units.ext rfl)) ).1 h Z r z
    (fun k => J ((r ≫ φ k) ≫ F)) (fun k => J' (r ≫ φ k)) (fun k => hJ ((r ≫ φ k) ≫ F)) (fun k => hJ' (r ≫ φ k))
  rw [Category.comp_id] at H
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  exact H

theorem carried_trans (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y)
    (z : Z) (p p' : K → L.ι) (q q' : K → L'.ι) (hp : r z ∈ LB.wchart L (fun k => φ k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ k ≫ F) p') (hq : r z ∈ LB.wchart L' φ q) (hq' : r z ∈ LB.wchart L' φ q') :
    (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) =
      trF (fun k => φ k ≫ F) ε r z p p' *
        ((∏ k, gw w (r ≫ φ k) z (p' k) (q' k) ^ ε k) * gm r z (LB.wchart L' φ q') (g.s q')) := by
  rw [gen_trans hg r z hq hq', ← _root_.mul_assoc, ← _root_.mul_assoc, trF, trF, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← mul_zpow, ← mul_zpow, (isGen_iff w).1 hw Z (r ≫ φ k) z (p k) (p' k) (q k) (q' k) (Set.mem_iInter.1 hp k)
    (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k) (Set.mem_iInter.1 hq' k), Category.assoc, mul_right_comm _ (gw _ _ _ _ _),
    inv_mul_cancel_right]

theorem exists_carried (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) :
    ∃ g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), g'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val g' r z J = (∏ k, wv w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have glue : ∀ p : K → L.ι, ∃ a : Γ(Y, LB.wchart L (fun k => φ k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
      gm r z _ a = (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => φ k ≫ F) p ⊓ LB.wchart L' φ q
    have le : ∀ q k, W q ≤ φ k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := fun q k y hy =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 k), Set.mem_iInter.1 hy.2 k⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ q, Γ(Y, W q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gm r z (W q) (u q) = (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) :=
      ⟨fun q => (∏ k, res (le q k) (pullU (φ k) _ (w.s (fun _ => p k, q k))) ^ ε k) *
          res (inf_le_right : W q ≤ LB.wchart L' φ q) (g.s q), fun Z r z q hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
          (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans
            (gm_pull r (φ k) z ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) (le q k hz) _))))) (gm_res r z _ hz _))⟩
    obtain ⟨a, ha⟩ := glue_unit (LB.wchart L (fun k => φ k ≫ F) p) W (fun q => inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) u (fun q q' y hy => by
        rw [hu _ _ y q hy.1, hu _ _ y q' hy.2, carried_trans w hw hg (𝟙 Y) y p p q q' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          mul_eq_left.1 (trF_trans hL _ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.1), _root_.one_mul])
    refine ⟨a, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz a).symm.trans ((congrArg (gm r z (W q)) (ha q)).trans (hu Z r z q hz))
  choose a ha using glue
  refine ⟨⟨a⟩, fun p p' => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · choose q hq using fun k => exists_chart hL' (φ k y)
    have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ q := Set.mem_iInter.2 hq
    refine (gm_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_linComb L _ ε (𝟙 Y) y p p' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (ha p' _ (𝟙 Y) y q hy.2 m)))).symm)
    exact (ha p _ (𝟙 Y) y q hy.1 m).trans (carried_trans w hw hg (𝟙 Y) y p p' q q hy.1 hy.2 m m)
  · refine (ha _ Z r z _ (hJ.mem _ r) (hJ'.mem φ r)).trans ?_
    simp only [wv, Category.assoc]
    rfl

end Bundles

section Points
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem cube_pre (t : SAB H X0) {T T' : Over X0} (h : T' ⟶ T) (a b : T ⟶ t.G) (I : ULift (Finset (Fin 2))) :
    h.left ≫ cφG t ![a, b] I = cφG t ![h ≫ a, h ≫ b] I := by
  rw [show (![h ≫ a, h ≫ b] : Fin 2 → (T' ⟶ t.G)) = fun i => h ≫ ![a, b] i from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact congrArg (fun z => z.left) (foldr_padd_pre h ![a, b] _).symm

theorem cube_push (t t' : SAB H X0) (f : t.G ⟶ t'.G) [IsMonHom f] {T : Over X0} (a b : T ⟶ t.G)
    (I : ULift (Finset (Fin 2))) : cφG t ![a, b] I ≫ f.left = cφG t' ![a ≫ f, b ≫ f] I := by
  rw [show (![a ≫ f, b ≫ f] : Fin 2 → (T ⟶ t'.G)) = fun i => ![a, b] i ≫ f from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact congrArg (fun z => z.left) (foldr_padd_comp f ![a, b] _)

theorem val_scale (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

theorem subst_act (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
    {n n' : ℕ} (m : ℕ) (f : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (α : t.G ⟶ t.G)
    (hα : x m ≫ α = Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2)) ≫ x m)
    (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = psIn d m ![k] (f j)) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k ≫ α := by
  rw [jptG, jptG, Category.assoc, hα, ← Category.assoc, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp,
    Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp]
  congr 2
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  have e : (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.X ∘ fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin n') p.1, p.2) := by
    funext p
    simp
  simp only [AlgHom.comp_apply, jetCopy, jetSubstP, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X, h, psIn,
    MvPolynomial.constantCoeff_rename, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [e, ← MvPolynomial.rename_eq_aeval]

end Points

theorem famAd_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ad : 𝓞 E → PS V 2 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamAd t (𝟙 (Sp V)) d x act ad e → FamAd t' (𝟙 (Sp V)) d x' act ad e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hcub hx _ hpush F act κ _ tg uv ad hch had a
  obtain ⟨ψ, hψ, hmon, hact, -, -⟩ := exists_iso_of_sabMap_id E H V t t' n
  have hx' : ∀ m, x' m = x m ≫ ψ.hom := fun m => Over.OverMorphism.ext (by rw [hx m, Over.comp_left, hψ])
  have hj : ∀ m (i : Fin 2), jptG t' (𝟙 (Sp V)) d x' m i = jptG t (𝟙 (Sp V)) d x m i ≫ ψ.hom := fun m i => by
    rw [jptG, jptG, hx' m, Category.assoc]
  obtain ⟨wL, hwL, hall⟩ := had a
  obtain ⟨wc, hwc, vc⟩ := exists_carried w t.PP.isLB t'.PP.isLB hcub.1 hwL
  have hinv : ∀ b, ψ.inv ≫ t.act.act b ≫ ψ.hom = t'.act.act b := fun b => by
    rw [hact b, Iso.inv_hom_id_assoc]
  have hfam : (fun k => (ψ.inv ⊗ₘ ψ.inv).left ≫
      Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) k ≫ n.φ) =
      Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)])
        (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G]) := by
    funext k
    rcases k with I | I
    all_goals
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← hψ, cube_push, cube_pre]
      simp [hinv]
  obtain ⟨wL', hwL', vL⟩ := exists_gen t'.PP.isLB (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ _) (congrFun hfam k))
    (LB.pullGen t'.PP.L _ _ wc (ψ.inv ⊗ₘ ψ.inv).left) (DVR.pullGen_isGen _ _ _ _ hwc _)
  refine ⟨wL', hwL', fun m => ?_⟩
  obtain ⟨u, hu, hcor⟩ := hall m
  obtain ⟨-, c, -, hc, hcar⟩ := hpush m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  choose J' hJ' using fun χ : _ ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  have hJ' : Good t.PP.L y J' := hJ'
  have k := val_corr hJ' hcor (𝟙 _)
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J =
        (∏ I, wv w y J J' ((Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I) ^ cε 2 I) *
        val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J' := fun φ => by
    refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).symm.trans ((val_carries w hcar _ hJ hJ').trans ?_))
    exact congrArg₂ (· * ·) (by rw [Category.id_comp]) (val_pull hJ' _ _ _).symm
  rw [val_mul hJ', val_scale t hJ', val_pull hJ'] at k
  rw [val_mul hJ, val_scale t' hJ, val_pull hJ, vL _ _ _ _ hJ, val_pull hJ, hpe, hpe, vc _ _ _ _ _ hJ hJ']
  have hl : (lift (jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2))).left ≫
      (ψ.inv ⊗ₘ ψ.inv).left = (lift (jptG t (𝟙 (Sp V)) d x m (0 : Fin 2)) (jptG t (𝟙 (Sp V)) d x m (1 : Fin 2))).left := by
    rw [← Over.comp_left, lift_map, hj, hj]
    simp
  simp only [Category.id_comp] at k ⊢
  rw [hl, _root_.mul_mul_mul_comm, k, mul_left_comm]
  refine congrArg (_ * ·) (congrArg (· * _) ?_)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, cube_pre]
  rw [subst_act t _ d x m (act a) _ (hch.act m a) _ 0 0 (fun j => rfl),
    Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.subst_jpt t _ d x m _ 1 1 ?h1,
    Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.subst_jpt t _ d x m _ 0 0 ?h2,
    subst_act t _ d x m (act (H.bar a)) _ (hch.act m (H.bar a)) _ 1 1 (fun j => rfl)]
  case h1 => exact fun j => rfl
  case h2 => exact fun j => rfl
  simp only [lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, zpow_neg, Finset.prod_inv_distrib,
    inv_mul_cancel_right]

end GlobalTheory.ChartCmp.PushAd
