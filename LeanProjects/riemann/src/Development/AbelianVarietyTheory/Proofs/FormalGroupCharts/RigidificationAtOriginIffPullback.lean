import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.RigOriginPull

theorem val_tie {X₁ X₂ Y Z : Scheme.{0}} {K : Type} [Fintype K] {L : LB X₁} {L' : LB X₂} {F : X₂ ⟶ X₁}
    (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X₂)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X₁) → L.ι} {J' : (Z ⟶ X₂) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val c r z J = (∏ k, Geo.Tor.gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  have H := (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h Z r z (fun k => J ((r ≫ φ' k) ≫ F))
    (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))
  · rw [Category.comp_id] at H
    exact (val_of c r z J _ (fun k => by rw [Category.assoc])).trans H
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem prod_prim (t : SAB H X0) {T : Over X0} {M : Type} [CommGroup M] (h : (T.left ⟶ t.G.left) → M) :
    ∏ k, h ((1 : T ⟶ t.G).left ≫ primφ t k) ^ primε k = h (1 : T ⟶ t.G).left := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), (1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, (1 : T ⟶ t.G) ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact Category.comp_id (1 : T ⟶ t.G)
    · rfl
  have hc : ∏ I, h ((1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I) ^ cε 2 I = 1 :=
    (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
      (GermB.cube_one_left t (fun p => h p.left) _)
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  exact (congrArg (fun q => h (1 : T ⟶ t.G).left * q⁻¹) hc).trans (by rw [inv_one, _root_.mul_one])

theorem prod_cube_left (t : SAB H X0) {T T' : Over X0} {M : Type} [CommGroup M] (h : (T'.left ⟶ t.G.left) → M)
    (u : T' ⟶ T) (a b : T ⟶ t.G) (ha : u ≫ a = 1) :
    ∏ I, h (u.left ≫ cφG t ![a, b] I) ^ cε 2 I = 1 := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), u.left ≫ cφG t ![a, b] I = (psum t.G ![1, u ≫ b] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact ha
    · rfl
  exact (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) _)

end GlobalTheory.RigOriginPull

open GlobalTheory.RigOriginPull in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.rigOrigin_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (wP : PrimTyG t) (wP' : PrimTyG t'), wP.IsGen → wP'.IsGen → (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d), (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (Rig0G t x0 d x act e wP ↔ Rig0G t' (𝟙 (Sp S)) d x' act e' wP') := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hrig d x x' hx e e' _ _ htie wP wP' _ _ hP act h0 _
  obtain ⟨c, hc₁, hc₂⟩ := htie 0
  obtain ⟨cP, hP₁, hP₂⟩ := hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hrig.2
  let o : Sp S ⟶ t'.G.left := (1 : overAt (𝟙 (Sp S)) S ⟶ t'.G).left
  have key : ∀ (y : Sp S) (J : (Sp S ⟶ t.G.left) → t.PP.L.ι) (J' : (Sp S ⟶ t'.G.left) → t'.PP.L.ι),
      Good t.PP.L y J → Good t'.PP.L y J' →
      val (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0)
          (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (LB.pullGen t'.PP.L _ _ (eLG t' (𝟙 (Sp S)) d x' act e' wP' 0)
            (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J' ∧
      val (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (rigT t'.G t'.PP.L t'.PP.rig (overAt (𝟙 (Sp S)) S) 1) (𝟙 (Sp S)) y J' := by
    intro y J J' hJ hJ'
    constructor
    · let A := Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let A' := Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let σ : Jet S (Fin 2 × Fin d) 0 →ₐ[S] Jet S (Fin 1 × Fin d) 0 := jetSubstP 0 fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 1), j), fun j => psIn d 0 ![0] (act H.w0 j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2
      have ho : (𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left = o :=
        (congrArg (· ≫ (x' 0).left) (Category.id_comp _)).trans (congrArg (fun q => q.left) h0)
      have ho' : (𝟙 (Sp S) ≫ A.left) ≫ (x 0).left = o ≫ mp.φ := by
        rw [← ho, ← hx 0]
        exact (Category.assoc _ _ _).symm
      have p₁ : val wP ((𝟙 (Sp S) ≫ A.left) ≫ (x 0).left) y J =
          Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) * val wP' ((𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left) y J' := by
        rw [ho, ho']
        refine (val_pull hJ wP mp.φ o).symm.trans ((val_corr hJ hP₁ o).symm.trans
          ((val_tie w _ _ wP' cP hP₂ o y hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)))
        exact prod_prim t' (T := overAt (𝟙 (Sp S)) S) (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q))
      have hu : (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ) ≫ jptG t' (𝟙 (Sp S)) d x' 0 (0 : Fin 2) = 1 := by
        have hid : σ.comp (jetCopy d 0 (0 : Fin 2)) = AlgHom.id S _ := by
          apply GermD.jet_hom_ext
          rintro ⟨i, j⟩
          obtain rfl : i = 0 := Subsingleton.elim _ _
          simp [σ, jetSubstP, jetCopy, GermD.jetMap_mk]
        rw [jptG, Category.assoc, ← Category.assoc (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ), GermD.homAt_comp, hid,
          GermD.homAt_id, Category.id_comp]
        exact h0
      have p₂ : val (e 0) ((𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left) y J =
          val (e' 0) ((𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left) y J' := by
        have q : (𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := congrArg (· ≫ _) (Category.id_comp _)
        have q' : (𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := q
        rw [q, q']
        refine (val_corr hJ hc₁ _).symm.trans ((val_tie w _ _ (e' 0) c hc₂ _ y hJ hJ').trans ?_)
        exact (congrArg₂ (· * ·) (prod_cube_left t' (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q)) _ _ _ hu)
          rfl).trans (_root_.one_mul _)
      refine (val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·)
        ((val_pull hJ _ _ _).trans p₁) ((val_pull hJ _ _ _).trans p₂)).trans ((_root_.mul_assoc _ _ _).trans
          (congrArg₂ (· * ·) rfl (Eq.symm ?_)))))
      exact (val_pull hJ' _ _ _).trans ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _)
        (val_pull hJ' _ _ _)))
    · refine (GermB.val_rigT _ _ _ _ _ y J hJ).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl
        (GermB.val_rigT _ _ _ _ _ y J' hJ').symm))
      have b : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ mp.cm.e = 𝟙 (Sp S) ≫ (overAt x0 S).hom := by
        rw [mp.base]
        simp
      have a₁ : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ eSec t'.G = o :=
        congrArg (· ≫ eSec t'.G) (Category.id_comp _)
      have a₂ : (𝟙 (Sp S) ≫ (overAt x0 S).hom) ≫ eSec t.G = o ≫ mp.φ := by
        rw [← b, ← a₁, Category.assoc, ← mp.cm.e_comm]
        exact (Category.assoc _ _ _).symm
      have q := pm _ (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) y (fun _ => J (o ≫ mp.φ)) (fun _ => J' o)
        (fun _ => (congrArg (fun r => (r ≫ mp.φ) y ∈ t.PP.L.U (J (o ≫ mp.φ))) a₁).mpr (hJ _))
        (fun _ => (congrArg (fun r => r y ∈ t'.PP.L.U (J' o)) a₁).mpr (hJ' _))
      rw [Fintype.prod_unique, zpow_one, b, a₁] at q
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans (q.trans (congrArg₂ (· * ·) rfl
        (val_of _ _ y J' _ (fun _ => congrArg J' a₁)).symm))
  constructor
  · intro h
    refine corr_of_val hL' fun y J' hJ' => ?_
    choose J hJ using fun χ : Sp S ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact mul_left_cancel (k₁.symm.trans ((val_corr hJ h _).trans k₂))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    choose J' hJ' using fun χ : Sp S ⟶ t'.G.left => exists_chart hL' (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact k₁.trans ((congrArg₂ (· * ·) rfl (val_corr hJ' h _)).trans k₂.symm)
