import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFrames

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameAdjDown

section General

variable {X0 X' Y Z A A' : Scheme.{0}} {L : LB X0} {L' : LB X'} {F : X' ⟶ X0} {K K₂ : Type} [Fintype K] [Fintype K₂]

def scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

theorem val_scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X0) → L.ι} (hJ : Good L z J) : val (scl u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem pmaps_of_flat (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) :
    PMaps w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h
  refine unit_ext fun y hy => ?_
  have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
  have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
    wchart_pull_le L F φ' j hy
  refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
  refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
  have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
  rw [Category.comp_id] at e
  exact e.symm

theorem corr_down (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F))
    {ψ : K → (A ⟶ X0)} {ψ' : K → (A' ⟶ X')} {ε : K → ℤ} {U : A' ⟶ A} (hψ : ∀ k, ψ' k ≫ F = U ≫ ψ k)
    {g : LB.Gen (LB.LinComb L ψ ε)} {g' : LB.Gen (LB.LinComb L' ψ' ε)} (hg : PMaps w ψ' ψ ε g' g U)
    {φ : K₂ → (Y ⟶ X0)} {φ' : K₂ → (Y ⟶ X')} {δ : K₂ → ℤ} {e : LB.Gen (LB.LinComb L φ δ)}
    {e' : LB.Gen (LB.LinComb L' φ' δ)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) δ)}
    (hc : LB.Gen.Corr L _ _ _ _ c e) (hm : LB.Gen.Maps (LB.linCombIso w φ' δ) e' (flatGen L F φ' δ c))
    {l : Y ⟶ A} {l' : Y ⟶ A'} (hl : l' ≫ U = l) (σ₁ σ₂ : Y ⟶ Y) (u : Γ(Y, ⊤)ˣ)
    (hF : ∀ (V : Type) [CommGroup V] (h : (Y ⟶ X') → V),
      (∏ k, h (l' ≫ ψ' k) ^ ε k) * ∏ k, h (σ₁ ≫ φ' k) ^ δ k = ∏ k, h (σ₂ ≫ φ' k) ^ δ k)
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ g l) (LB.pullGen L _ _ e σ₁))
      (scl u (LB.pullGen L _ _ e σ₂))) :
    LB.Gen.Corr L' _ _ _ _ (LB.mulGen L' _ _ _ _ (LB.pullGen L' _ _ g' l') (LB.pullGen L' _ _ e' σ₁))
      (scl u (LB.pullGen L' _ _ e' σ₂)) := by
  refine corr_of_val hL' fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have h0 := val_corr hJ H (𝟙 Y)
  rw [val_mul hJ, val_scl _ _ _ hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
    Category.id_comp] at h0
  rw [val_mul hJ', val_scl _ _ _ hJ', val_pull hJ', val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp,
    Category.id_comp]
  have he : ∀ σ : Y ⟶ Y, val e σ y J =
      (∏ k, gw w (σ ≫ φ' k) y (J ((σ ≫ φ' k) ≫ F)) (J' (σ ≫ φ' k)) ^ δ k) * val e' σ y J' := fun σ => by
    have := DegPull.pmaps_val (fun k => (Category.id_comp _).symm) (pmaps_of_flat w φ' δ e' c hm) σ y hJ hJ'
    rw [Category.comp_id] at this
    exact (val_corr hJ hc σ).symm.trans this
  have h1 := DegPull.pmaps_val hψ hg l' y hJ hJ'
  rw [hl] at h1
  have h2 := hF _ (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [h1, he, he, ← h2, _root_.mul_mul_mul_comm, mul_left_comm (gm (𝟙 Y) y ⊤ u)] at h0
  exact mul_left_cancel h0

end General

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameAdjSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_act' {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → PS S 1 d}
    (h : ∀ m (b : 𝓞 E), x m ≫ t.act.act b =
      homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m)
    (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← homAt_comp, Category.assoc, ← h m a, ← Category.assoc, ren_one]
  try rfl

theorem push_act {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) {T : Over S'}
    (p : T ⟶ t'.G) (a : 𝓞 E) : pushPt mp.cart.1.w (p ≫ t'.act.act a) = pushPt mp.cart.1.w p ≫ t.act.act a :=
  Over.OverMorphism.ext (by
    show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
    rw [Category.assoc, mp.act, Category.assoc])

def sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) :
    Over.mk ((t'.G ⊗ t'.G).hom ≫ f) ⟶ t.G ⊗ t.G :=
  lift (pushPt mp.cart.1.w (fst t'.G t'.G)) (pushPt mp.cart.1.w (snd t'.G t'.G))

theorem adj_comm {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) (a b : 𝓞 E)
    (k : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))) :
    Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act b])
        (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G]) k ≫ mp.φ =
      (sqMap mp).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act b])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) k := by
  rcases k with I | I
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · simp [sqMap]
    · exact (push_act mp _ _).trans (by simp [sqMap])
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · exact (push_act mp _ _).trans (by simp [sqMap])
    · simp [sqMap]

theorem lift_sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f)
    {T' : Over S'} {T : Over S} (p' q' : T' ⟶ t'.G) (p q : T ⟶ t.G) (h : T'.left ⟶ T.left)
    (hp : p'.left ≫ mp.φ = h ≫ p.left) (hq : q'.left ≫ mp.φ = h ≫ q.left) :
    (lift p' q').left ≫ (sqMap mp).left = h ≫ (lift p q).left := by
  apply pullback.hom_ext
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (fst t.G t.G).left = (h ≫ (lift p q).left) ≫ (fst t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_fst, lift_fst, ← hp]
    show (lift p' q').left ≫ (fst t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (snd t.G t.G).left = (h ≫ (lift p q).left) ≫ (snd t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_snd, lift_snd, ← hq]
    show (lift p' q').left ≫ (snd t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

set_option maxHeartbeats 2000000 in

theorem adjoint_series_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e e' _ _ htie act ad a _ hact ⟨wL, hwL, hu⟩
  obtain ⟨wL', hwL', hp⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (sqMap mp).left
    (adj_comm mp a (H.bar a)) wL hwL
  refine ⟨wL', hwL', fun m => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hu m
  obtain ⟨c, hc, hm⟩ := htie m
  refine ⟨u, hu1, ?_⟩
  have hj : ∀ i : Fin 2, (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = 𝟙 _ ≫ (jptG t x0 d x m i).left := fun i => by
    show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
      𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
    rw [Category.assoc, hx, Category.id_comp]
    rfl
  have hl₀ := lift_sqMap mp (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))
    (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2)) (𝟙 (Sp (Jet S (Fin 2 × Fin d) m))) (hj 0) (hj 1)
  have hl : (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left ≫
      (sqMap mp).left = (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left :=
    hl₀.trans (Category.id_comp _)
  refine corr_down (Y := (jOG (𝟙 (Sp S)) d m 2).left) t.PP.isLB t'.PP.isLB w (adj_comm mp a (H.bar a)) hp hc hm hl
    _ _ (unitΓ u) (fun V _ h => ?_) hu2
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_act' hact, zpow_neg, Finset.prod_inv_distrib]
  simp only [inv_mul_cancel_right]

end GlobalTheory.FrameAdjDown
