import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameAdjUp

section Pts

variable {S : Type} [CommRing S] (d : ℕ)

theorem subst_copy (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) =
      jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2) := by
  apply GermD.jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetSubstP, jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X]

theorem substX (m : ℕ) {n : ℕ} (k : Fin n) :
    jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S)) =
      jetCopy d m k := by
  apply GermD.jet_hom_ext
  intro p
  simp [jetSubstP, jetCopy, GermD.jetMap_mk]

def jetRen (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m :=
  jetMap (fun q : Fin n × Fin d => MvPolynomial.X (r q.1, q.2)) fun _ => X_mem_orig _

theorem ren_one (m : ℕ) {n' : ℕ} (r : Fin 1 → Fin n') : jetRen (S := S) d m r = jetCopy d m (r 0) := by
  apply GermD.jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [jetRen, jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X]

theorem subst_psIn (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (g : Fin d → MvPowerSeries (Fin n × Fin d) S) :
    jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (g p.2)) =
      (jetRen d m r).comp (jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (g p.2))) := by
  have hr : (MvPolynomial.aeval fun q : Fin n × Fin d => (MvPolynomial.X (r q.1, q.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.rename fun p : Fin n × Fin d => (r p.1, p.2) := MvPolynomial.algHom_ext fun q => by simp
  apply GermD.jet_hom_ext
  intro p
  simp only [jetSubstP, jetRen, AlgHom.comp_apply, GermD.jetMap_mk, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, psIn, MvPolynomial.constantCoeff_rename, hr, MvPolynomial.rename_C]

end Pts

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}

theorem pt_sub (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)) ≫ jptG t x0 d x m i =
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2)) ≫ x m := by
  rw [jptG, ← Category.assoc, GermD.homAt_comp, subst_copy]

theorem pt_X (m : ℕ) {n : ℕ} (k : Fin n) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S))) ≫ x m =
      jptG t x0 d x m k := by
  rw [substX]
  try rfl

theorem pe_pt (m : ℕ) {n : ℕ} (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (I : ULift.{0} (Finset (Fin 2))) :
    (Formalism.L2.Pj.homAt x0 σ).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I =
      (psum t.G ![Formalism.L2.Pj.homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2), Formalism.L2.Pj.homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2)] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i <;> rfl

theorem wl_pt {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act c] I =
      (psum t.G ![a, b ≫ t.act.act c] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ fst t.G t.G = a
    exact lift_fst _ _
  · show lift a b ≫ (snd t.G t.G ≫ t.act.act c) = b ≫ t.act.act c
    exact lift_snd_assoc _ _ _

theorem wl_pt' {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G ≫ t.act.act c, snd t.G t.G] I =
      (psum t.G ![a ≫ t.act.act c, b] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ (fst t.G t.G ≫ t.act.act c) = a ≫ t.act.act c
    exact lift_fst_assoc _ _ _
  · show lift a b ≫ snd t.G t.G = b
    exact lift_snd _ _

end Chart

section Val

variable {X X' Y P P' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K₁ W : Type} [Fintype K] [Fintype K₁]
  [Fintype W]

theorem corr_up (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    (φ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (e : LB.Gen (LB.LinComb L φ ε₁)) (hc : LB.Gen.Corr L _ _ _ _ c e)
    (ψ' : W → (P' ⟶ X')) (ψ : W → (P ⟶ X)) (δ : W → ℤ) (v' : LB.Gen (LB.LinComb L' ψ' δ))
    (v : LB.Gen (LB.LinComb L ψ δ)) (l' : Y ⟶ P') (l : Y ⟶ P)
    (hv : ∀ (y : Y) J J', Good L y J → Good L' y J' → val v l y J =
      (∏ k, gw w (l' ≫ ψ' k) y (J ((l' ≫ ψ' k) ≫ F)) (J' (l' ≫ ψ' k)) ^ δ k) * val v' l' y J')
    (s₁ s₂ : Y ⟶ Y)
    (hs : FormEq (Sum.elim (fun k => l' ≫ ψ' k) (fun k => s₁ ≫ φ' k)) (Sum.elim δ ε) (fun k => s₂ ≫ φ' k) ε)
    (u : Γ(Y, ⊤)ˣ)
    (h : LB.Gen.Corr L' _ _ _ _ (LB.mulGen L' _ _ _ _ (LB.pullGen L' ψ' δ v' l') (LB.pullGen L' φ' ε a s₁))
      (FrameSym.scale _ _ u (LB.pullGen L' φ' ε a s₂))) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L ψ δ v l) (LB.pullGen L φ ε₁ e s₁))
      (FrameSym.scale _ _ u (LB.pullGen L φ ε₁ e s₂)) := by
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := FrameSym.good_exists hL' y
  have h' := val_corr hJ' h (𝟙 Y)
  rw [val_mul hJ', FrameSym.val_scale _ _ _ _ hJ', val_pull hJ', val_pull hJ', val_pull hJ'] at h'
  rw [val_mul hJ, FrameSym.val_scale _ _ _ _ hJ, val_pull hJ, val_pull hJ, val_pull hJ, ← val_corr hJ hc,
    ← val_corr hJ hc, FrameSym.val_tie w φ' ε a c hm _ y hJ hJ', FrameSym.val_tie w φ' ε a c hm _ y hJ hJ']
  simp only [Category.id_comp] at h' ⊢
  have p := hs _ (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [Fintype.prod_sum_type] at p
  simp only [Sum.elim_inl, Sum.elim_inr] at p
  rw [hv y J J' hJ hJ', _root_.mul_mul_mul_comm, p, h', _root_.mul_left_comm]

end Val

section Adj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev adφ {B : Scheme.{0}} (t : SAB H B) (a : 𝓞 E) :
    ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ((t.G ⊗ t.G).left ⟶ t.G.left) :=
  Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])

abbrev adε : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim (cε 2) fun I => -cε 2 I

variable {B B' : Scheme.{0}} {t : SAB H B} {t' : SAB H B'} {f : B' ⟶ B} (mp : SABMap t' t f)

def sqMap : Over.mk ((t'.G ⊗ t'.G).hom ≫ f) ⟶ t.G ⊗ t.G :=
  lift (pushPt mp.cart.1.w (fst t'.G t'.G)) (pushPt mp.cart.1.w (snd t'.G t'.G))

theorem push_act {T : Over B'} (x : T ⟶ t'.G) (a : 𝓞 E) :
    pushPt mp.cart.1.w (x ≫ t'.act.act a) = pushPt mp.cart.1.w x ≫ t.act.act a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, mp.act, Category.assoc])

theorem adφ_comm (a : 𝓞 E) (k) : adφ t' a k ≫ mp.φ = (sqMap mp).left ≫ adφ t a k := by
  rcases k with I | I
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · simp [sqMap]
    · exact (push_act mp _ _).trans (by simp [sqMap])
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · exact (push_act mp _ _).trans (by simp [sqMap])
    · simp [sqMap]

theorem lift_sqMap {T' : Over B'} {T : Over B} (g : T'.left ⟶ T.left) (p' q' : T' ⟶ t'.G) (p q : T ⟶ t.G)
    (hp : p'.left ≫ mp.φ = g ≫ p.left) (hq : q'.left ≫ mp.φ = g ≫ q.left) :
    (lift p' q').left ≫ (sqMap mp).left = g ≫ (lift p q).left := by
  apply pullback.hom_ext
  · show (_ ≫ (sqMap mp).left) ≫ (fst t.G t.G).left = (_ ≫ _) ≫ (fst t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, sqMap, lift_fst, ← hp]
    show (lift p' q').left ≫ (fst t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · show (_ ≫ (sqMap mp).left) ≫ (snd t.G t.G).left = (_ ≫ _) ≫ (snd t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, sqMap, lift_snd, ← hq]
    show (lift p' q').left ≫ (snd t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

theorem prod_adjointnessBundle_zeroSection_eq_one (a : 𝓞 E) {U : Type} [CommGroup U] (h : ((𝟙_ (Over B)).left ⟶ t.G.left) → U) :
    ∏ k, h ((GermB.zz t).left ≫ adφ t a k) ^ adε k = 1 := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', zpow_neg, Finset.prod_inv_distrib,
    GermB.eta_one]
  rw [GermB.cube_one_left t (fun p => h p.left), GermB.cube_one_right t (fun p => h p.left), inv_one, _root_.mul_one]

theorem val_ad (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)) (hw : w.IsGen)
    (a : 𝓞 E) (v' : LB.Gen (LB.LinComb t'.PP.L (adφ t' a) adε)) (hv' : v'.IsGen)
    (h' : ∀ y J', Good t'.PP.L y J' → val v' (GermB.zz t').left y J' = 1)
    (v : LB.Gen (LB.LinComb t.PP.L (adφ t a) adε)) (hv : v.IsGen)
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over B)).left) (z : Z) J, Good t.PP.L z J →
      val v (r ≫ (GermB.zz t).left) z J = 1)
    {Z : Scheme.{0}} (r : Z ⟶ (t'.G ⊗ t'.G).left) (z : Z) J J' (hJ : Good t.PP.L z J) (hJ' : Good t'.PP.L z J') :
    val v (r ≫ (sqMap mp).left) z J =
      (∏ k, gw w (r ≫ adφ t' a k) z (J ((r ≫ adφ t' a k) ≫ mp.φ)) (J' (r ≫ adφ t' a k)) ^ adε k) * val v' r z J' := by
  obtain ⟨c, hc, R⟩ := exists_up ((isGen_iff w).1 hw) t.PP.isLB t'.PP.isLB v' hv'
  have R' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (t'.G ⊗ t'.G).left) (z : Z) J J', Good t.PP.L z J → Good t'.PP.L z J' →
      val c r z J = (∏ k, gw w (r ≫ adφ t' a k) z (J ((r ≫ adφ t' a k) ≫ mp.φ)) (J' (r ≫ adφ t' a k)) ^ adε k) *
        val v' r z J' := fun Z r z J J' hJ hJ' => by
    refine (R Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  have sj : Function.Surjective ((snd t'.G t'.G).left ≫ t'.G.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : (GermB.zz t').left ≫ (snd t'.G t'.G).left ≫ t'.G.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (GermB.zz t')
  have key := gen_unique' t.PP.isLB (φ := fun k => (sqMap mp).left ≫ adφ t a k) (ε := adε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ adε I) (adφ_comm mp a I))
    _ (GermB.zz t').left he sj (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hv (sqMap mp).left) hc (fun y I hI => by
      obtain ⟨I', hI'⟩ := FrameSym.good_exists t'.PP.isLB y
      refine Eq.trans ?_ ((R' _ _ y I I' hI hI').trans (congrArg₂ (· * ·)
        (prod_adjointnessBundle_zeroSection_eq_one a (fun q => gw w q y (I (q ≫ mp.φ)) (I' q))) (h' y I' hI'))).symm
      rw [_root_.mul_one]
      refine (val_pull hI _ _ _).trans ?_
      rw [lift_sqMap mp mp.cm.e _ _ _ _ mp.cm.e_comm mp.cm.e_comm]
      exact h _ _ y I hI) _ r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (R' _ _ z J J' hJ hJ'))

end Adj

theorem psJet_zero_of {S κ : Type} [CommRing S] [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 1) : psJet 0 f = 1 := by
  have hc : MvPolynomial.constantCoeff (psTrunc 0 f) = 1 := by
    rw [MvPolynomial.constantCoeff_eq, GermFun.coeff_psTrunc _ _ _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  unfold psJet
  rw [← map_one (Ideal.Quotient.mk (orig S κ ^ (0 + 1)))]
  refine Ideal.Quotient.eq.2 ?_
  have := sub_const_mem_orig (psTrunc 0 f)
  rw [hc, map_one] at this
  rwa [zero_add, pow_one]

theorem aug_subst {S κ κ' : Type} [CommRing S] (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetAug : Jet S κ' m →ₐ[S] S).comp (jetSubstP m φ) = jetAug := by
  apply GermD.jet_hom_ext
  intro p
  have h0 : ∀ q : MvPolynomial κ' S, MvPolynomial.aeval (fun _ => (0 : S)) q = MvPolynomial.constantCoeff q := by
    intro q
    induction q using MvPolynomial.induction_on <;> simp_all
  rw [GermB.jetAug_X, AlgHom.comp_apply, jetSubstP, GermD.jetMap_mk, MvPolynomial.aeval_X]
  show MvPolynomial.aeval (fun _ => (0 : S)) _ = 0
  rw [h0]; simp

theorem pt_act' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
    {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
    {act : 𝓞 E → Fin d → PS S 1 d}
    (hact : ∀ m (b : 𝓞 E), x m ≫ t.act.act b =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m)
    (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← GermD.homAt_comp, Category.assoc, ← hact m a, ← Category.assoc, ren_one]
  try rfl

set_option maxHeartbeats 1000000 in
theorem frame_adj_up : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → IsAbelianScheme t'.G → (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → MvPowerSeries.constantCoeff (ad a) = 1 → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  intro hLaws E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx hA h0 e e' _ _ ht act ad a hact _ had ⟨v', hv', hr⟩
  obtain ⟨v, hv, hv0⟩ := GermB.exists_wL t a
  have hz : ∀ y J', Good t'.PP.L y J' → val v' (GermB.zz t').left y J' = 1 := by
    intro y J' hJ'
    obtain ⟨u, hu, hc⟩ := hr 0
    obtain rfl : u = 1 := Units.ext (hu.trans (psJet_zero_of _ had))
    let ρ : overAt (𝟙 (Sp S)) S ⟶ jOG (𝟙 (Sp S)) d 0 2 :=
      Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 2 × Fin d) 0 →ₐ[S] S)
    have hρ : ∀ φ : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
        ρ.left ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetSubstP 0 φ)).left = ρ.left := fun φ => by
      rw [← Over.comp_left, GermD.homAt_comp, aug_subst]
    have hj : ∀ i : Fin 2, ρ ≫ jptG t' (𝟙 (Sp S)) d x' 0 i = 1 := fun i => by
      rw [jptG, ← Category.assoc, GermD.homAt_comp, GermB.aug_copy, h0]
    have hl : ρ.left ≫ (lift (jptG t' (𝟙 (Sp S)) d x' 0 (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' 0 (1 : Fin 2))).left =
        (GermB.zz t').left := by
      rw [← Over.comp_left, comp_lift, hj, hj]
      refine (congrArg Over.Hom.left (comp_lift (toUnit (overAt (𝟙 (Sp S)) S)) η[t'.G] η[t'.G]).symm).trans ?_
      show (toUnit (overAt (𝟙 (Sp S)) S)).left ≫ (GermB.zz t').left = _
      have : (toUnit (overAt (𝟙 (Sp S)) S)).left = 𝟙 (Sp S) := by
        show spMap (algebraMap S S) ≫ 𝟙 _ = _
        simp [spMap]
      rw [this]; exact Category.id_comp _
    have hJ'' : Good (Z := Sp S) t'.PP.L y J' := hJ'
    have e1 := (val_mul hJ'' _ _ _).symm.trans ((val_corr hJ'' hc ρ.left).trans (GermB.val_scale t' _ _ _ _ _ y J' hJ''))
    have e2 := (congrArg₂ (· * ·) (val_pull hJ'' _ _ _) (val_pull hJ'' _ _ _)).symm.trans
      (e1.trans (congrArg₂ (· * ·) rfl (val_pull hJ'' _ _ _)))
    rw [hρ, hρ, hl, unitΓ, map_one, map_one] at e2
    exact mul_right_cancel e2
  refine ⟨v, hv, fun m => ?_⟩
  obtain ⟨u, hu, hc⟩ := hr m
  obtain ⟨c₁, hc₁, hm⟩ := ht m
  have hjx : ∀ i : Fin 2, (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = 𝟙 _ ≫ (jptG t x0 d x m i).left := fun i => by
    rw [Category.id_comp]
    show (_ ≫ (x' m).left) ≫ _ = _ ≫ (x m).left
    rw [Category.assoc, hx]; rfl
  have hl := (lift_sqMap mp (T' := jOG (𝟙 (Sp S)) d m 2) (T := jOG x0 d m 2) (𝟙 _) _ _ _ _ (hjx 0) (hjx 1)).trans
    (Category.id_comp _)
  have hF : FormEq (Sum.elim
      (fun k => (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left ≫ adφ t' a k)
      (fun k => (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2)).left ≫
        cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] k)) (Sum.elim adε (cε 2))
      (fun k => (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2)).left ≫
        cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] k) (cε 2) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub,
      Matrix.cons_val_zero, Matrix.cons_val_one, pt_X, pt_act' hact, zpow_neg, Finset.prod_inv_distrib]
    simp only [inv_mul_cancel_right]
  refine ⟨u, hu, corr_up t.PP.isLB t'.PP.isLB w _ (cε 2) (e' m) c₁ hm
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) hc₁ (adφ t' a) (adφ t a) adε v' v
    _ _ (fun y J J' hJ hJ' => ?_) _ _ hF (unitΓ u) hc⟩
  exact (congrArg (fun r => val v r y J) hl).symm.trans
      (val_ad mp hLaws.globalFns hA w hw.1 a v' hv' hz v hv hv0 _ y J J' hJ hJ')

end GlobalTheory.FrameAdjUp
