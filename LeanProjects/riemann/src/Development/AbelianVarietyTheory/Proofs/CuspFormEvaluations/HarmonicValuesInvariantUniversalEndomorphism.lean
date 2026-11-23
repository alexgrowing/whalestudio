import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFrames
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBCNab
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartPush

section General

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def om (w : LB.Iso L' (L.pull Φ)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (x : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := Geo.Tor.gw w x z (J (x ≫ Φ)) (J' x)

theorem exists_up_om {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (φ' : K → (Y ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (hc : ∀ k, φ' k ≫ Φ = φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      val t r z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  obtain rfl : (fun k => φ' k ≫ Φ) = φ := funext hc
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' a ha
  refine ⟨t, ht, fun Z r z J J' hJ hJ' => (hv _ r z _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)⟩
  simp only [pw, om, Category.assoc]

theorem exists_down_om {Y' : Scheme.{0}} {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J →
      Good L' z J' → val t (r ≫ h) z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) hL hL' h hψ t ht
  exact ⟨a, ha, fun Z r z J J' hJ hJ' => DegPull.pmaps_val hψ H r z hJ hJ'⟩

end General

def lam {A U : Type} [CommGroup A] [CommGroup U] (h : A → U) (a b : A) : U := h (a * b) * (h a)⁻¹ * (h b)⁻¹ * h 1

theorem lam_one_left {A U : Type} [CommGroup A] [CommGroup U] (h : A → U) (b : A) : lam h 1 b = 1 := by
  simp [lam]

theorem lam_one_right {A U : Type} [CommGroup A] [CommGroup U] (h : A → U) (b : A) : lam h b 1 = 1 := by
  simp [lam]

theorem lam_comm {A U : Type} [CommGroup A] [CommGroup U] (h : A → U) (a b : A) : lam h a b = lam h b a := by
  rw [lam, lam, mul_comm a b, mul_right_comm (h (b * a))]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X}
  {t' : SAB H X'} {ρ : X' ⟶ X} (ν : SABMap t' t ρ)

theorem prod_lam {T T' : Over X} (σ : T' ⟶ T) (a b : T ⟶ t.G) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ t.G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (σ.left ≫ cφG t ![a, b] I) ^ cε 2 I = lam (fun p : T' ⟶ t.G => h p.left) (σ ≫ a) (σ ≫ b) := by
  refine Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) ?_) (prod_cube₂ (σ ≫ a) (σ ≫ b) h)
  refine congrArg (fun q => q.left) ((psum_hom (preHom σ) ![a, b] I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_)))
  fin_cases i <;> rfl

theorem cφ_push {T : Over X} {T' : Over X'} (h : T'.left ⟶ T.left) {a' b' : T' ⟶ t'.G} {a b : T ⟶ t.G}
    (ha : a'.left ≫ ν.φ = h ≫ a.left) (hb : b'.left ≫ ν.φ = h ≫ b.left) (I : ULift.{0} (Finset (Fin 2))) :
    cφG t' ![a', b'] I ≫ ν.φ = h ≫ cφG t ![a, b] I := by
  have hh : h ≫ T.hom = T'.hom ≫ ρ := by
    rw [← Over.w a, ← Category.assoc, ← ha, Category.assoc, ν.cart.1.w, ← Category.assoc, Over.w]
  refine psum_push ν.cart _ _ (Over.homMk h hh : Over.mk (T'.hom ≫ ρ) ⟶ T) (fun i => ?_) I.down
  fin_cases i
  · exact Over.OverMorphism.ext ha
  · exact Over.OverMorphism.ext hb

theorem act_push {T : Over X} {T' : Over X'} (h : T'.left ⟶ T.left) {a' : T' ⟶ t'.G} {a : T ⟶ t.G}
    (ha : a'.left ≫ ν.φ = h ≫ a.left) (c : 𝓞 E) :
    (a' ≫ t'.act.act c).left ≫ ν.φ = h ≫ (a ≫ t.act.act c).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, ha, Category.assoc]

variable {ν} {w : LB.Iso t'.PP.L (t.PP.L.pull ν.cm.F)}

section Val

variable {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} {J' : (Z ⟶ t'.G.left) → t'.PP.L.ι}
  (hJ : Good t.PP.L z J) (hJ' : Good t'.PP.L z J')
include hJ hJ'

theorem rig_val (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig)) (r : Z ⟶ X') :
    val (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1) t.PP.rig (r ≫ ρ) z J =
      om w z J J' (r ≫ eSec t'.G) * val (φ := fun _ : PUnit => eSec t'.G) (ε := fun _ => 1) t'.PP.rig r z J' := by
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig ν.cm.e _
      (rigPull_le ν.cm.F ν.cm.e ν.cm.e_comm t.PP.L) (fun _ => rfl)).1 hr
  have e := DegPull.pmaps_val (fun _ => ν.cm.e_comm) pm r z hJ hJ'
  rw [Fintype.prod_unique, zpow_one, ν.base] at e
  exact e

theorem cub_val (hc : LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (ν.cm.thetaPull t.PP.L t.cub.t))
    {Y : Scheme.{0}} {g : Y ⟶ X} {g' : Y ⟶ X'} {a' b' c' : Over.mk g' ⟶ t'.G} {a b c : Over.mk g ⟶ t.G}
    (ha : a'.left ≫ ν.φ = a.left) (hb : b'.left ≫ ν.φ = b.left) (hc' : c'.left ≫ ν.φ = c.left) (r : Z ⟶ Y) :
    val (L := t.PP.L) (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t (r ≫ (lift a (lift b c)).left) z J =
      lam (fun p : Over.mk g' ⟶ t'.G => om w z J J' (r ≫ p.left)) (a' * b') c' *
        (lam (fun p : Over.mk g' ⟶ t'.G => om w z J J' (r ≫ p.left)) a' c')⁻¹ *
        (lam (fun p : Over.mk g' ⟶ t'.G => om w z J J' (r ≫ p.left)) b' c')⁻¹ *
        val (L := t'.PP.L) (φ := thφ t'.G (x3 t'.G)) (ε := thε) t'.cub.t (r ≫ (lift a' (lift b' c')).left) z J' := by
  have pm := (maps_iff w (thφ t'.G (x3 t'.G)) (thφ t.G (x3 t.G)) thε t'.cub.t t.cub.t ν.cm.F3
    (ν.cm.thetaPull t.PP.L t.cub.t) (ν.cm.theta_le t.PP.L) (fun _ => rfl)).1 hc
  have e := DegPull.pmaps_val (φ' := thφ t'.G (x3 t'.G)) (φ := thφ t.G (x3 t.G)) (ε := thε)
    (fun I => ν.cm.psum_comm I.down) pm (r ≫ (lift a' (lift b' c')).left) z hJ hJ'
  have q : (lift a' (lift b' c')).left ≫ ν.cm.F3 = (lift a (lift b c)).left := hom_ext_triple _ fun i => by
    have := ν.cm.psum_comm {i}
    rw [psum_single, psum_single] at this
    rw [Category.assoc, ← this, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i
    · simpa [x3] using ha
    · simpa [x3] using hb
    · simpa [x3] using hc'
  rw [Category.assoc r, q] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  have p := prod_cub a' b' c' (fun q => om w z J J' (r ≫ q))
  refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (p.trans ?_)
  · exact congrArg (fun q => om w z J J' q ^ thε I) (Category.assoc _ _ _)
  · apply Additive.ofMul.injective
    simp only [lam, ofMul_mul, ofMul_inv]
    abel

theorem prim_val (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (hw : w.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig)) {wP : PrimTyG t} {wP' : PrimTyG t'} (hP : IsPrimG t wP) (hP' : IsPrimG t' wP')
    {T : Over X'} (x : T ⟶ t'.G) (r : Z ⟶ T.left) :
    val wP ((r ≫ x.left) ≫ ν.φ) z J = om w z J J' (r ≫ x.left) *
      (lam (fun p : T ⟶ t'.G => om w z J J' (r ≫ p.left)) x (x ≫ t'.act.act H.w0))⁻¹ * val wP' (r ≫ x.left) z J' := by
  have i₀ : (𝟙 t'.G : t'.G ⟶ t'.G).left ≫ ν.φ = ν.φ ≫ (𝟙 t.G : t.G ⟶ t.G).left := by simp
  obtain ⟨u, hu, vu⟩ := exists_down_om hw t.PP.isLB t'.PP.isLB
    (φ' := Sum.elim (fun _ : Fin 1 => 𝟙 t'.G.left) (cφG t' ![𝟙 t'.G, t'.act.act H.w0])) ν.φ (by
      rintro (k | I)
      · simp
      · exact cφ_push ν ν.φ i₀ (ν.act _) I) wP hP.1
  have wt : ∀ {T : Over X'} (x : T ⟶ t'.G) {U : Type} [CommGroup U] (h : (T.left ⟶ t'.G.left) → U),
      ∏ k, h (x.left ≫ Sum.elim (fun _ : Fin 1 => 𝟙 t'.G.left) (cφG t' ![𝟙 t'.G, t'.act.act H.w0]) k) ^
        (Sum.elim (fun _ => 1) (fun I => -cε 2 I) k : ℤ) =
        h x.left * (lam (fun p : T ⟶ t'.G => h p.left) x (x ≫ t'.act.act H.w0))⁻¹ := fun x U _ h =>
    DVR.prod_sum₂ _ (by simp) (DVR.prod_neg _ _ ((prod_lam x _ _ h).trans (by rw [Category.comp_id])))
  have key := gen_unique t'.PP.isLB t'.G.hom (eSec t'.G) (Over.w η[t'.G]) (hG _ _ hA).2 hu hP'.1 (fun y I' hI' => by
    obtain ⟨I, hI⟩ := DegPull.exists_good' t.PP.isLB y
    have a := vu _ (eSec t'.G) y I I' hI hI'
    have b := wt η[t'.G] (om w y I I')
    rw [GermB.eta_one, lam_one_left, inv_one, _root_.mul_one, ← GermB.eta_one] at b
    have c := rig_val hI hI' hr (𝟙 X')
    have d := (val_pull hI _ _ _).symm.trans (val_corr hI hP.2 (𝟙 X' ≫ ρ))
    have d' := (val_pull hI' _ _ _).symm.trans (val_corr hI' hP'.2 (𝟙 X'))
    have e : eSec t'.G ≫ ν.φ = (𝟙 X' ≫ ρ) ≫ eSec t.G := by
      rw [Category.id_comp]; exact ν.cm.e_comm.trans (congrArg (· ≫ eSec t.G) ν.base)
    rw [e] at a
    rw [Category.id_comp] at d'
    have f := a.symm.trans (d.trans c)
    rw [Category.id_comp] at f
    exact (mul_left_cancel ((congrArg₂ (· * ·) b.symm rfl).trans f)).trans d'.symm) _ (r ≫ x.left) z J' hJ'
  refine (vu _ _ z J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ key)
  refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (wt x (fun q => om w z J J' (r ≫ q)))
  rw [Category.assoc r]

abbrev AdT (t : SAB H X) (c : 𝓞 E) : Type := LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar c)])
        (cφG t ![fst t.G t.G ≫ t.act.act c, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I))

theorem ad_val (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (hw : w.IsGen) {c : 𝓞 E} {wL : AdT t c} {wL' : AdT t' c}
    (hL : wL.IsGen) (hL' : wL'.IsGen)
    (hn : ∀ (r : Z ⟶ (𝟙_ (Over X)).left), val wL (r ≫ (GermB.zz t).left) z J = 1)
    {Y : Scheme.{0}} {g : Y ⟶ X} {g' : Y ⟶ X'} {a' b' : Over.mk g' ⟶ t'.G} {a b : Over.mk g ⟶ t.G}
    (ha : a'.left ≫ ν.φ = a.left) (hb : b'.left ≫ ν.φ = b.left) (r : Z ⟶ Y)
    (hn' : val wL' (r ≫ (lift (1 : Over.mk g' ⟶ t'.G) (1 : Over.mk g' ⟶ t'.G)).left) z J' = 1) :
    val wL (r ≫ (lift a b).left) z J =
      lam (fun p : Over.mk g' ⟶ t'.G => om w z J J' (r ≫ p.left)) a' (b' ≫ t'.act.act (H.bar c)) *
      (lam (fun p : Over.mk g' ⟶ t'.G => om w z J J' (r ≫ p.left)) (a' ≫ t'.act.act c) b')⁻¹ *
      val wL' (r ≫ (lift a' b').left) z J' := by
  have gp := ν.cart
  let Φ₂ : (t'.G ⊗ t'.G).left ⟶ (t.G ⊗ t.G).left :=
    (lift (pushPt gp.1.w (fst t'.G t'.G)) (pushPt gp.1.w (snd t'.G t'.G))).left
  have f₁ : (fst t'.G t'.G).left ≫ ν.φ = Φ₂ ≫ (fst t.G t.G).left :=
    (congrArg (fun q => q.left) (lift_fst (pushPt gp.1.w (fst t'.G t'.G)) (pushPt gp.1.w (snd t'.G t'.G)))).symm
  have f₂ : (snd t'.G t'.G).left ≫ ν.φ = Φ₂ ≫ (snd t.G t.G).left :=
    (congrArg (fun q => q.left) (lift_snd (pushPt gp.1.w (fst t'.G t'.G)) (pushPt gp.1.w (snd t'.G t'.G)))).symm
  have cmp : ∀ {a' b' : Over.mk g' ⟶ t'.G} {a b : Over.mk g ⟶ t.G}, a'.left ≫ ν.φ = a.left → b'.left ≫ ν.φ = b.left →
      (lift a' b').left ≫ Φ₂ = (lift a b).left := fun {a' b' a b} hx hy => by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₁.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst, hx]
      exact (congrArg (fun q => q.left) (lift_fst a b)).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₂.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd, hy]
      exact (congrArg (fun q => q.left) (lift_snd a b)).symm
  obtain ⟨u, hu, vu⟩ := exists_down_om hw t.PP.isLB t'.PP.isLB
    (φ' := Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar c)])
        (cφG t' ![fst t'.G t'.G ≫ t'.act.act c, snd t'.G t'.G])) Φ₂ (by
      rintro (I | I)
      · exact cφ_push ν Φ₂ f₁ (act_push ν Φ₂ f₂ _) I
      · exact cφ_push ν Φ₂ (act_push ν Φ₂ f₁ _) f₂ I) wL hL
  have vu' : ∀ {a' b' : Over.mk g' ⟶ t'.G} {a b : Over.mk g ⟶ t.G}, a'.left ≫ ν.φ = a.left → b'.left ≫ ν.φ = b.left →
      val wL (r ≫ (lift a b).left) z J =
      lam (fun p : Over.mk g' ⟶ t'.G => om w z J J' (r ≫ p.left)) a' (b' ≫ t'.act.act (H.bar c)) *
      (lam (fun p : Over.mk g' ⟶ t'.G => om w z J J' (r ≫ p.left)) (a' ≫ t'.act.act c) b')⁻¹ *
      val u (r ≫ (lift a' b').left) z J' := fun {a' b' a b} hx hy => by
    have e := vu _ (r ≫ (lift a' b').left) z J J' hJ hJ'
    rw [Category.assoc r, cmp hx hy] at e
    refine e.trans (congrArg₂ (· * ·) ?_ rfl)
    have p₁ := prod_lam (lift a' b') (fst t'.G t'.G) (snd t'.G t'.G ≫ t'.act.act (H.bar c)) (fun q => om w z J J' (r ≫ q))
    have p₂ := prod_lam (lift a' b') (fst t'.G t'.G ≫ t'.act.act c) (snd t'.G t'.G) (fun q => om w z J J' (r ≫ q))
    rw [lift_fst, lift_snd_assoc] at p₁
    rw [lift_fst_assoc, lift_snd] at p₂
    refine DVR.prod_sum₂ _ (Eq.trans (Finset.prod_congr rfl fun I _ => ?_) p₁)
      (Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (DVR.prod_neg _ _ p₂))
    · rw [Category.assoc r]; rfl
    · rw [Category.assoc r]; rfl
  have gg : g' ≫ ρ = g := by
    have h₁ : a'.left ≫ t'.G.hom = g' := Over.w a'
    have h₂ : a.left ≫ t.G.hom = g := Over.w a
    rw [← h₁, ← h₂, ← ha, Category.assoc, Category.assoc, gp.1.w]
  have o : (1 : Over.mk g' ⟶ t'.G).left ≫ ν.φ = (1 : Over.mk g ⟶ t.G).left := by
    subst gg
    exact congrArg (fun q => q.left) (map_one (pushHom gp (Over.mk g')))
  have u₀ := vu' o o
  have z₀ : (lift (1 : Over.mk g ⟶ t.G) (1 : Over.mk g ⟶ t.G)).left = g ≫ (GermB.zz t).left := by
    have : lift (1 : Over.mk g ⟶ t.G) (1 : Over.mk g ⟶ t.G) = toUnit _ ≫ GermB.zz t := by
      rw [GermB.zz, comp_lift]; rfl
    rw [this]; rfl
  rw [lam_one_left, lam_one_right, inv_one, _root_.mul_one, _root_.one_mul, z₀, ← Category.assoc] at u₀
  have u₁ := u₀.symm.trans (hn _)
  let n : t'.G ⊗ t'.G ⟶ t'.G ⊗ t'.G := lift 1 1
  have sj : Function.Surjective ((snd t'.G t'.G).left ≫ t'.G.hom).appTop.hom := surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have nn : (GermB.zz t').left ≫ n.left = (GermB.zz t').left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one, GermB.zz, GermB.eta_one]
  have key := gen_unique' t'.PP.isLB (fun _ _ _ => rfl)
    ((snd t'.G t'.G).left ≫ t'.G.hom) (GermB.zz t').left (by rw [Over.w]; exact Over.w (GermB.zz t')) sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ hL' n.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hL' (DVR.pullGen_isGen _ _ _ _ hu n.left)) (fun y I hI => by
      rw [val_mul hI, val_mul hI, val_pull hI, val_pull hI, nn, mul_comm]) _ (r ≫ (lift a' b').left) z J' hJ'
  have n₁ : (r ≫ (lift a' b').left) ≫ n.left = r ≫ (lift (1 : Over.mk g' ⟶ t'.G) (1 : Over.mk g' ⟶ t'.G)).left := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [val_mul hJ', val_mul hJ', val_pull hJ', val_pull hJ', n₁, hn', u₁, _root_.mul_one, _root_.mul_one] at key
  rw [vu' ha hb, key]

end Val

section Chart

open GlobalTheory.FrameAdjSeries

variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {x0' : Sp S ⟶ X'}

variable (ν) in

def pu (h0 : x0' ≫ ρ = x0) (A : Type) [CommRing A] [Algebra S A] : (overAt x0' A ⟶ t'.G) →* (overAt x0 A ⟶ t.G) :=
  have e : (overAt x0' A).hom ≫ ρ = (overAt x0 A).hom := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h0)
  MonoidHom.mk' (fun a => Over.homMk (a.left ≫ ν.φ) ((Over.w (pushPt ν.cart.1.w a)).trans e)) fun a b =>
    Over.OverMorphism.ext ((ν.cart.2 _ a b (pushPt ν.cart.1.w a) (pushPt ν.cart.1.w b) rfl rfl).symm.trans
      (mul_left_congr e _ _ _ _ rfl rfl))

theorem pu_left (h0 : x0' ≫ ρ = x0) {A : Type} [CommRing A] [Algebra S A] (a : overAt x0' A ⟶ t'.G) :
    (pu ν h0 A a).left = a.left ≫ ν.φ := rfl

theorem hom_pu (h0 : x0' ≫ ρ = x0) {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (a : overAt x0' A ⟶ t'.G) : homAt x0 f ≫ pu ν h0 A a = pu ν h0 B (homAt x0' f ≫ a) :=
  Over.OverMorphism.ext (Category.assoc _ _ _).symm

theorem pu_act (h0 : x0' ≫ ρ = x0) {A : Type} [CommRing A] [Algebra S A] (a : overAt x0' A ⟶ t'.G) (c : 𝓞 E) :
    pu ν h0 A a ≫ t.act.act c = pu ν h0 A (a ≫ t'.act.act c) :=
  Over.OverMorphism.ext (by
    show (a.left ≫ ν.cm.F) ≫ (t.act.act c).left = (a.left ≫ (t'.act.act c).left) ≫ ν.cm.F
    rw [Category.assoc, Category.assoc, ν.act])

variable {d : ℕ} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t'.G.left)} {uvec : κ → Fin d → S}
  {x' : ∀ m, jOG x0' d m 1 ⟶ t'.G} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}

theorem isChart_push (h0 : x0' ≫ ρ = x0) (hc : IsChartG t' x0' d F act tg uvec x') :
    IsChartG t x0 d F act (fun ℓ => tg ℓ ≫ ν.φ) uvec (fun m => pu ν h0 _ (x' m)) := by
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun ℓ => ?_, hc.basis⟩
  · rw [hom_pu, hc.zero, map_one]
  · rw [hom_pu, hc.trunc]
  · rw [hom_pu, hc.law, map_mul, jptG, jptG, jptG, jptG, hom_pu, hom_pu]
  · rw [hom_pu, pu_act, hc.act]
  · obtain ⟨u, hu, hp⟩ := hc.tan ℓ
    refine ⟨fun i => pu ν h0 (DualNumber S) (u i), fun i => ?_, ?_⟩
    · exact (congrArg (· ≫ ν.φ) (hu i)).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
    · have e : List.ofFn (fun i => pu ν h0 (DualNumber S) (u i)) = (List.ofFn u).map (pu ν h0 (DualNumber S)) := by
        rw [List.map_ofFn]; rfl
      rw [e, ← map_list_prod, pu_left, hp]

theorem jpt_push (hx : ∀ m, (x' m).left ≫ ν.φ = (x m).left) {n : ℕ} (m : ℕ) (i : Fin n) :
    (jptG t' x0' d x' m i).left ≫ ν.φ = (jptG t x0 d x m i).left :=
  (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (hx m))

variable (w) in

def FrRel (e' : ∀ m, FrTyG t' x0' d x' m) (e : ∀ m, FrTyG t x0 d x m) : Prop :=
  ∀ (m : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet S (Fin 2 × Fin d) m)) (z : Z) J J', Good t.PP.L z J → Good t'.PP.L z J' →
    val (L := t.PP.L) (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε := cε 2) (e m) r z J =
      (∏ I : ULift.{0} (Finset (Fin 2)), om w z J J'
        (r ≫ cφG t' ![jptG t' x0' d x' m (0 : Fin 2), jptG t' x0' d x' m (1 : Fin 2)] I) ^ cε 2 I) *
      val (L := t'.PP.L) (φ := cφG t' ![jptG t' x0' d x' m (0 : Fin 2), jptG t' x0' d x' m (1 : Fin 2)]) (ε := cε 2)
        (e' m) r z J'

theorem exists_frRel (hw : w.IsGen) (hx : ∀ m, (x' m).left ≫ ν.φ = (x m).left) (e' : ∀ m, FrTyG t' x0' d x' m)
    (he' : ∀ m, (e' m).IsGen) : ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ FrRel w e' e := by
  choose e he hv using fun m => exists_up_om (Y := Sp (Jet S (Fin 2 × Fin d) m)) hw t.PP.isLB t'.PP.isLB
    (cφG t' ![jptG t' x0' d x' m (0 : Fin 2), jptG t' x0' d x' m (1 : Fin 2)])
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2)
    (fun I => (cφ_push ν (T := jOG x0 d m 2) (T' := jOG x0' d m 2) (𝟙 _)
      ((jpt_push hx m 0).trans (Category.id_comp _).symm) ((jpt_push hx m 1).trans (Category.id_comp _).symm) I).trans
      (Category.id_comp _)) (e' m) (he' m)
  exact ⟨e, he, hv⟩

variable {e' : ∀ m, FrTyG t' x0' d x' m} {e : ∀ m, FrTyG t x0 d x m}

theorem val_pe (he : FrRel w e' e) {Z : Scheme.{0}} {z : Z} {J J'} (hJ : Good t.PP.L z J) (hJ' : Good t'.PP.L z J')
    {m n : ℕ} (f g : Fin d → MvPolynomial (Fin n × Fin d) S) (r : Z ⟶ Sp (Jet S (Fin n × Fin d) m))
    {a b : jOG x0' d m n ⟶ t'.G}
    (ha : homAt x0' (jetSubstP m (fun p : Fin 1 × Fin d => f p.2)) ≫ x' m = a)
    (hb : homAt x0' (jetSubstP m (fun p : Fin 1 × Fin d => g p.2)) ≫ x' m = b) :
    val (peG t x0 d x e m ![f, g]) r z J = lam (fun p : jOG x0' d m n ⟶ t'.G => om w z J J' (r ≫ p.left)) a b *
      val (peG t' x0' d x' e' m ![f, g]) r z J' := by
  refine (val_pull hJ _ _ _).trans ((he m Z _ z J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ (val_pull hJ' _ _ _).symm))
  have p := prod_lam (homAt x0' (jetSubstP m fun p : Fin 2 × Fin d => (![f, g] : Fin 2 → _) p.1 p.2))
    (jptG t' x0' d x' m (0 : Fin 2)) (jptG t' x0' d x' m (1 : Fin 2)) (fun q => om w z J J' (r ≫ q))
  rw [pt_sub, pt_sub] at p
  subst ha hb
  refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) p
  exact congrArg (fun q => om w z J J' q ^ cε 2 I) (Category.assoc _ _ _)

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {z : Z} {J}
    (hJ : Good t.PP.L z J) (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem val_three {Y Z : Scheme.{0}} {K₁ K₂ K₃ : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃]
    {φ₁ : K₁ → (Y ⟶ t.G.left)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ t.G.left)} {ε₂ : K₂ → ℤ} {φ₃ : K₃ → (Y ⟶ t.G.left)}
    {ε₃ : K₃ → ℤ} {z : Z} {J} (hJ : Good t.PP.L z J) (u : Γ(Y, ⊤)ˣ) (g₁ : LB.Gen (LB.LinComb t.PP.L φ₁ ε₁))
    (g₂ : LB.Gen (LB.LinComb t.PP.L φ₂ ε₂)) (g₃ : LB.Gen (LB.LinComb t.PP.L φ₃ ε₃)) (r : Z ⟶ Y) :
    val (scaleGenG t _ _ u (LB.mulGen t.PP.L _ _ _ _ g₁ (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ g₂)
      (LB.invGen t.PP.L _ _ g₃)))) r z J = gm r z ⊤ u * (val g₁ r z J * ((val g₂ r z J)⁻¹ * (val g₃ r z J)⁻¹)) := by
  rw [val_scale hJ, val_mul hJ, val_mul hJ, val_inv, val_inv]

theorem psJet_zero_of {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 1) : psJet 0 f = 1 := by
  unfold psJet
  rw [← map_one (Ideal.Quotient.mk (orig S κ ^ (0 + 1)))]
  refine Ideal.Quotient.eq.2 ?_
  rw [zero_add, pow_one]
  have := sub_const_mem_orig (psTrunc 0 f)
  rwa [MvPolynomial.constantCoeff_eq, GermFun.coeff_psTrunc _ _ _ (by simp),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_one] at this

theorem ad_zero (hc : IsChartG t' x0' d F act tg uvec x') {c : 𝓞 E} {wL : AdT t' c} {u : (Jet S (Fin 2 × Fin d) 0)ˣ}
    (hu : u = 1) (hr : LB.Gen.Corr t'.PP.L _ _ _ _
        (LB.mulGen t'.PP.L _ _ _ _
          (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' x0' d x' 0 (0 : Fin 2)) (jptG t' x0' d x' 0 (1 : Fin 2))).left)
          (peG t' x0' d x' e' 0 ![fun j => psIn d 0 ![0] (act c j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
        (scaleGenG t' _ _ (unitΓ u)
          (peG t' x0' d x' e' 0 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 0 ![1] (act (H.bar c) j)])))
    {Z : Scheme.{0}} {z : Z} {J'} (hJ' : Good t'.PP.L z J') {m : ℕ} (r : Z ⟶ Sp (Jet S (Fin 2 × Fin d) m)) :
    val wL (r ≫ (lift (1 : jOG x0' d m 2 ⟶ t'.G) (1 : jOG x0' d m 2 ⟶ t'.G)).left) z J' = 1 := by
  let σ : jOG x0' d m 2 ⟶ jOG x0' d 0 2 := homAt x0' ((Algebra.ofId S _).comp jetAug)
  have j₀ : ∀ i : Fin 2, jptG t' x0' d x' 0 i = 1 := fun i => by rw [jptG, frame_origin_jet_one hc, MonObj.comp_one]
  have hι : σ ≫ lift (jptG t' x0' d x' 0 (0 : Fin 2)) (jptG t' x0' d x' 0 (1 : Fin 2)) =
      lift (1 : jOG x0' d m 2 ⟶ t'.G) (1 : jOG x0' d m 2 ⟶ t'.G) := by
    rw [j₀, j₀, comp_lift, MonObj.comp_one]
  have h1 := val_corr hJ' hr (r ≫ σ.left)
  rw [val_mul hJ', val_pull hJ', val_scale hJ', hu, show unitΓ (1 : (Jet S (Fin 2 × Fin d) 0)ˣ) = 1 from map_one _,
    map_one, _root_.one_mul] at h1
  have hpe : val (peG t' x0' d x' e' 0 ![fun j => psIn d 0 ![0] (act c j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (r ≫ σ.left) z J' =
      val (peG t' x0' d x' e' 0 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 0 ![1] (act (H.bar c) j)])
        (r ≫ σ.left) z J' := by
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_pull hJ' _ _ _).symm)
    rw [jetSubstP_zero_eq]
  rw [hpe, mul_eq_right, Category.assoc, ← Over.comp_left, hι] at h1
  exact h1

theorem alg_three {U : Type} [CommGroup U] {A A' l₁ l₂ l₃ u p₁ p₂ p₃ q₁ q₂ q₃ : U} (k₀ : A = l₁ * l₂⁻¹ * l₃⁻¹ * A')
    (k : A' = u * (q₁ * (q₂⁻¹ * q₃⁻¹))) (k₁ : p₁ = l₁ * q₁) (k₂ : p₂ = l₂ * q₂) (k₃ : p₃ = l₃ * q₃) :
    A = u * (p₁ * (p₂⁻¹ * p₃⁻¹)) := by
  subst k₀ k k₁ k₂ k₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alg_one {U : Type} [CommGroup U] {A A' l l' u p q : U} (k₀ : A = l' * A') (e : l' = l) (k : A' = u * q)
    (k₁ : p = l * q) : A = u * p := by
  subst k₀ k k₁ e
  exact mul_left_comm _ _ _

theorem alg_two {U : Type} [CommGroup U] {A A' l₁ l₂ u p₁ p₂ q₁ q₂ : U} (k₀ : A = l₂ * l₁⁻¹ * A')
    (k : A' * q₁ = u * q₂) (k₁ : p₁ = l₁ * q₁) (k₂ : p₂ = l₂ * q₂) : A * p₁ = u * p₂ := by
  subst k₀ k₁ k₂
  apply Additive.ofMul.injective
  have := congrArg Additive.ofMul k
  simp only [ofMul_mul, ofMul_inv] at this ⊢
  linear_combination (norm := abel) this

theorem corr_of_val₂ {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ} {a : LB.Gen (LB.LinComb t.PP.L φ ε)} {b : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (t' : SAB H X') (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good t.PP.L z J → Good t'.PP.L z J' →
      val a r z J = val b r z J) : LB.Gen.Corr t.PP.L φ ε φ' ε' a b :=
  corr_of_val t.PP.isLB fun y J hJ => by
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' t'.PP.isLB y
    exact h _ _ y J J' hJ hJ'

set_option maxHeartbeats 800000 in
theorem isFrame_push (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (hw : w.IsGen)
    (hcub : LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (ν.cm.thetaPull t.PP.L t.cub.t))
    (hc : IsChartG t' x0' d F act tg uvec x') (hx : ∀ m, (x' m).left ≫ ν.φ = (x m).left) (he : FrRel w e' e)
    (hg : ∀ m, (e m).IsGen) {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (had : ∀ c, MvPowerSeries.constantCoeff (ad c) = 1)
    (hf : IsFrameG t' x0' d x' F act ph1 ph2 sy ad e') : IsFrameG t x0 d x F act ph1 ph2 sy ad e := by
  refine ⟨hg, fun m => ?_, fun m => ?_, fun m => ?_, fun c => ?_⟩
  · obtain ⟨u, hu, hr⟩ := hf.ph1 m
    refine ⟨u, hu, corr_of_val₂ t' fun Z r z J J' hJ hJ' => ?_⟩
    have k := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' hr r).trans (val_three hJ' _ _ _ _ _))
    have k₀ := cub_val hJ hJ' hcub (jpt_push hx m (0 : Fin 3)) (jpt_push hx m (1 : Fin 3)) (jpt_push hx m (2 : Fin 3)) r
    have k₁ := val_pe he hJ hJ' (fun j => psIn d m ![0, 1] (F j)) (fun j => MvPolynomial.X ((2 : Fin 3), j)) r
      (a := jptG t' x0' d x' m (0 : Fin 3) * jptG t' x0' d x' m (1 : Fin 3)) (pt_law hc m ![0, 1]) (pt_X m _)
    have k₂ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((0 : Fin 3), j)) (fun j => MvPolynomial.X ((2 : Fin 3), j)) r (pt_X m _) (pt_X m _)
    have k₃ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((1 : Fin 3), j)) (fun j => MvPolynomial.X ((2 : Fin 3), j)) r (pt_X m _) (pt_X m _)
    exact (val_pull hJ _ _ _).trans ((alg_three k₀ k k₁ k₂ k₃).trans (val_three hJ _ _ _ _ _).symm)
  · obtain ⟨u, hu, hr⟩ := hf.ph2 m
    refine ⟨u, hu, corr_of_val₂ t' fun Z r z J J' hJ hJ' => ?_⟩
    have k := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' hr r).trans (val_three hJ' _ _ _ _ _))
    have k₀ := cub_val hJ hJ' hcub (jpt_push hx m (1 : Fin 3)) (jpt_push hx m (2 : Fin 3)) (jpt_push hx m (0 : Fin 3)) r
    have k₁ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((0 : Fin 3), j)) (fun j => psIn d m ![1, 2] (F j)) r
      (b := jptG t' x0' d x' m (1 : Fin 3) * jptG t' x0' d x' m (2 : Fin 3)) (pt_X m _) (pt_law hc m ![1, 2])
    have k₂ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((0 : Fin 3), j)) (fun j => MvPolynomial.X ((1 : Fin 3), j)) r (pt_X m _) (pt_X m _)
    have k₃ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((0 : Fin 3), j)) (fun j => MvPolynomial.X ((2 : Fin 3), j)) r (pt_X m _) (pt_X m _)
    rw [lam_comm] at k₁ k₂ k₃
    exact (val_pull hJ _ _ _).trans ((alg_three k₀ k k₁ k₂ k₃).trans (val_three hJ _ _ _ _ _).symm)
  · obtain ⟨u, hu, hr⟩ := hf.sy m
    refine ⟨u, hu, corr_of_val₂ t' fun Z r z J J' hJ hJ' => ?_⟩
    have k := (val_corr hJ' hr r).trans (val_scale hJ' _ _ _)
    have k₀ := he m _ r z J J' hJ hJ'
    have p := prod_lam (𝟙 (jOG x0' d m 2)) (jptG t' x0' d x' m (0 : Fin 2)) (jptG t' x0' d x' m (1 : Fin 2))
      (fun q => om w z J J' (r ≫ q))
    have k₁ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((1 : Fin 2), j)) (fun j => MvPolynomial.X ((0 : Fin 2), j)) r (pt_X m _) (pt_X m _)
    rw [lam_comm] at k₁
    simp only [Over.id_left, Category.id_comp] at p
    exact (alg_one k₀ p k k₁).trans (val_scale hJ _ _ _).symm
  · obtain ⟨wL', hw', hall⟩ := hf.ad c
    obtain ⟨wL, hwL, hn⟩ := GermB.exists_wL t c
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hr⟩ := hall m
    obtain ⟨u₀, hu₀, hr₀⟩ := hall 0
    have hu₁ : u₀ = 1 := Units.ext (hu₀.trans (psJet_zero_of _ (had c)))
    refine ⟨u, hu, corr_of_val₂ t' fun Z r z J J' hJ hJ' => ?_⟩
    have k' := (val_mul hJ' _ _ _).symm.trans ((val_corr hJ' hr r).trans (val_scale hJ' _ _ _))
    rw [val_pull hJ'] at k'
    have z₀ := ad_zero hc hu₁ hr₀ hJ' (m := m) r
    have k₀ := ad_val hJ hJ' hG hA hw hwL hw' (fun r => hn _ r z J hJ) (jpt_push hx m (0 : Fin 2))
      (jpt_push hx m (1 : Fin 2)) r z₀
    have k₁ := val_pe he hJ hJ' (fun j => psIn d m ![0] (act c j)) (fun j => MvPolynomial.X ((1 : Fin 2), j)) r
      (a := jptG t' x0' d x' m (0 : Fin 2) ≫ t'.act.act c) (pt_act hc m ![0] c) (pt_X m _)
    have k₂ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((0 : Fin 2), j)) (fun j => psIn d m ![1] (act (H.bar c) j)) r
      (b := jptG t' x0' d x' m (1 : Fin 2) ≫ t'.act.act (H.bar c)) (pt_X m _) (pt_act hc m ![1] (H.bar c))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
    rw [val_pull hJ]
    exact alg_two k₀ k' k₁ k₂

variable {wP : PrimTyG t} {wP' : PrimTyG t'}

theorem alg_prim {U : Type} [CommGroup U] {A A' l o p q : U} (k₀ : A = o * l⁻¹ * A') (k₁ : p = l * q) :
    A * p = o * (A' * q) := by
  subst k₀ k₁
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_eL (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (hw : w.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig)) (hP : IsPrimG t wP) (hP' : IsPrimG t' wP')
    (hc : IsChartG t' x0' d F act tg uvec x') (hx : ∀ m, (x' m).left ≫ ν.φ = (x m).left) (he : FrRel w e' e)
    {Z : Scheme.{0}} {z : Z} {J J'} (hJ : Good t.PP.L z J) (hJ' : Good t'.PP.L z J') (m : ℕ)
    (r : Z ⟶ Sp (Jet S (Fin 1 × Fin d) m)) :
    val (eLG t x0 d x act e wP m) r z J = om w z J J' (r ≫ (x' m).left) * val (eLG t' x0' d x' act e' wP' m) r z J' := by
  have j₀ : jptG t' x0' d x' m (0 : Fin 1) = x' m := by
    have : (jetCopy d m (0 : Fin 1) : Jet S (Fin 1 × Fin d) m →ₐ[S] _) = AlgHom.id S _ := GermD.jet_hom_ext fun p => by
      obtain ⟨i, j⟩ := p
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp [jetCopy, GermD.jetMap_mk]
    rw [jptG, this, GermD.homAt_id, Category.id_comp]
  have k₀ := prim_val hJ hJ' hG hA hw hr hP hP' (x' m) r
  have k₁ := val_pe he hJ hJ' (fun j => MvPolynomial.X ((0 : Fin 1), j)) (fun j => psIn d m ![0] (act H.w0 j)) r
    (a := x' m) (b := x' m ≫ t'.act.act H.w0) ((pt_X m 0).trans j₀)
    ((pt_act hc m ![0] H.w0).trans (congrArg (· ≫ t'.act.act H.w0) j₀))
  rw [Category.assoc, hx] at k₀
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (congrArg (om w z J J' (r ≫ (x' m).left) * ·) (val_mul hJ' _ _ _).symm))
  rw [val_pull hJ, val_pull hJ']
  exact alg_prim k₀ k₁

theorem rig_push (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (hw : w.IsGen) (h0 : x0' ≫ ρ = x0)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig)) (hP : IsPrimG t wP) (hP' : IsPrimG t' wP')
    (hc : IsChartG t' x0' d F act tg uvec x') (hx : ∀ m, (x' m).left ≫ ν.φ = (x m).left) (he : FrRel w e' e)
    (h : LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ (eLG t' x0' d x' act e' wP' 0)
      (homAt x0' (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT t'.G t'.PP.L t'.PP.rig (overAt x0' S) 1)) :
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0)
      (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1) := by
  refine corr_of_val₂ t' fun Z r z J J' hJ hJ' => ?_
  have k := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' h r).trans (GermB.val_rigT _ _ _ _ _ _ _ hJ'))
  have k₀ := val_eL hG hA hw hr hP hP' hc hx he hJ hJ' 0
    (r ≫ (homAt x0' (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
  have k₁ := rig_val hJ hJ' hr (r ≫ (overAt x0' S).hom)
  have a : (r ≫ (homAt x0' (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) ≫ (x' 0).left =
      (r ≫ (overAt x0' S).hom) ≫ eSec t'.G := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, hc.zero]; rfl
  have b : (r ≫ (overAt x0' S).hom) ≫ ρ = r ≫ (overAt x0 S).hom :=
    (Category.assoc _ _ _).trans (congrArg (r ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h0)))
  rw [a, k] at k₀
  rw [b] at k₁
  exact (val_pull hJ _ _ _).trans (k₀.trans (k₁.symm.trans (GermB.val_rigT _ _ _ _ _ _ _ hJ).symm))

abbrev sv (t : SAB H X) {k : ℤ} {T : Over X} (s : LB.Sec (LPow t.G t.PP.L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ t.G).left)
    (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) : Z.presheaf.stalk z :=
  sval (L := t.PP.L) (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => k) s r z J

theorem ptSecT_snd {T : Over X} (a : T ⟶ t.G) : (ptSecT t.G a).left ≫ (snd T t.G).left = a.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

theorem sv_of_isValueAt {n : ℤ} {T : Over X} {s : LB.Sec (LPow t.G t.PP.L n T)} {a : T ⟶ t.G}
    {τ : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => a.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
    (h : IsValueAt t.G t.PP.L n s a τ c) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J}
    (hJ : Good t.PP.L z J) : sv t s (r ≫ (ptSecT t.G a).left) z J = gs r z ⊤ c * (val τ r z J).val := by
  have hz := hJ.mem (fun _ : Fin 1 => a.left) r
  refine (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J (fun _ => J (r ≫ a.left))
    (fun _ => by rw [Category.assoc, ptSecT_snd])).trans ?_
  exact ((gs_res r z _ hz _).trans (gs_pull r (ptSecT t.G a).left z _ (val_le t.G t.PP.L a _ hz) _)).symm.trans
    ((congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_res r z le_top hz c) (gs_unit r z _ hz _))))

theorem isValueAt_of_sv {n : ℤ} {T : Over X} {s : LB.Sec (LPow t.G t.PP.L n T)} {a : T ⟶ t.G}
    {τ : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => a.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
    (t' : SAB H X') (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good t.PP.L z J → Good t'.PP.L z J' →
      sv t s (r ≫ (ptSecT t.G a).left) z J = gs r z ⊤ c * (val τ r z J).val) :
    IsValueAt t.G t.PP.L n s a τ c := fun j => fn_ext fun y hy => by
  obtain ⟨J, hJ, e⟩ := exists_good t.PP.L t.PP.isLB y (fun _ : Fin 1 => a.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' t'.PP.isLB y
  have q := h _ (𝟙 _) y J J' hJ hJ'
  rw [val_of τ _ y J j (fun k => by rw [Category.id_comp]; exact e k)] at q
  have q' := (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s (𝟙 _ ≫ (ptSecT t.G a).left) y J j
    (fun k => by rw [Category.id_comp, ptSecT_snd]; exact e k)).symm.trans q
  exact ((gs_res _ y _ hy _).trans (gs_pull _ (ptSecT t.G a).left y _ (val_le t.G t.PP.L a _ hy) _)).trans
    (q'.trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy c) (gs_unit _ y _ hy _))).symm)

theorem sv_pullSec {n : ℤ} {T T' : Over X} {h : T' ⊗ t.G ⟶ T ⊗ t.G} {hh : h ≫ snd T t.G = snd T' t.G}
    {s : LB.Sec (LPow t.G t.PP.L n T)} {s' : LB.Sec (LPow t.G t.PP.L n T')} (hs : IsPullSec t.G t.PP.L n h hh s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ t.G).left) (z : Z) {J} (hJ : Good t.PP.L z J) :
    sv t s' r z J = sv t s (r ≫ h.left) z J :=
  (GermD.pullSec_stalk t.G t.PP.L n hs r z _ (hJ.mem (fun _ : Fin 1 => (snd T' t.G).left) r)).trans
    (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J _
      (fun _ => by rw [Category.assoc, ← Over.comp_left, hh])).symm

theorem isGerm_push (hG : GlobalFnsSt) (hA : IsAbelianScheme t'.G) (hw : w.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (ν.cm.rigPull t.PP.L t.PP.rig)) (hP : IsPrimG t wP) (hP' : IsPrimG t' wP')
    (hc : IsChartG t' x0' d F act tg uvec x') {tg₁ : κ → (Sp (DualNumber S) ⟶ t.G.left)}
    (hc₁ : IsChartG t x0 d F act tg₁ uvec x) (hx : ∀ m, (x' m).left ≫ ν.φ = (x m).left) (he : FrRel w e' e)
    (hg : ∀ m, (e m).IsGen) {pm : (Over.mk x0' ⊗ t'.G).left ⟶ (Over.mk x0 ⊗ t.G).left}
    (p₁ : pm ≫ (fst (Over.mk x0) t.G).left = (fst (Over.mk x0') t'.G).left)
    (p₂ : pm ≫ (snd (Over.mk x0) t.G).left = (snd (Over.mk x0') t'.G).left ≫ ν.φ) {k : ℕ}
    {s' : LB.Sec (LPow t'.G t'.PP.L k (Over.mk x0'))} {s : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x0' ⊗ t'.G).left) (z : Z) J J', Good t.PP.L z J → Good t'.PP.L z J' →
      sv t s (r ≫ pm) z J = (om w z J J' (r ≫ (snd (Over.mk x0') t'.G).left) ^ k).val * sv t' s' r z J')
    {f : MvPowerSeries (Fin 1 × Fin d) S} (h : IsGermG t' x0' d x' act e' wP' k s' f) :
    IsGermG t x0 d x act e wP k s f := by
  intro m
  obtain ⟨s₁', τ', hp', hτ', hv'⟩ := h m
  have heL : (eLG t x0 d x act e wP m).IsGen :=
    DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (DVR.pullGen_isGen t.PP.L _ _ _ hP.1 _) (DVR.pullGen_isGen t.PP.L _ _ _ (hg m) _)
  obtain ⟨τ, -, hτ⟩ : ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by
    refine exists_gen t.PP.isLB ?_ _ (GermD.genPowG_isGen t _ _ _ heL k)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one,
      GermD.formEq_eL hc₁ m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  obtain ⟨s₁, hp⟩ := GermD.exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) s
  refine ⟨s₁, τ, hp, corr_of_val t.PP.isLB fun y J hJ => hτ _ _ y J hJ,
    isValueAt_of_sv t' fun Z r z J J' hJ hJ' => ?_⟩
  have q₁ := sv_of_isValueAt hv' r z hJ'
  have q₂ := (val_corr hJ' hτ' r).trans (GermD.val_genPowG t' _ _ _ k r z J')
  have q₃ := (hτ _ r z J hJ).trans (GermD.val_genPowG t _ _ _ k r z J)
  have q₄ := val_eL hG hA hw hr hP hP' hc hx he hJ hJ' m r
  have q₅ := hs _ ((r ≫ (ptSecT t'.G (x' m)).left) ≫ (jBaseG x0' d m 1 ▷ t'.G).left) z J J' hJ hJ'
  have a₁ : ∀ {X : Scheme.{0}} {t : SAB H X} {x0 : Sp S ⟶ X} (a : jOG x0 d m 1 ⟶ t.G),
      ((ptSecT t.G a).left ≫ (jBaseG x0 d m 1 ▷ t.G).left) ≫ (snd (Over.mk x0) t.G).left = a.left ∧
      ((ptSecT t.G a).left ≫ (jBaseG x0 d m 1 ▷ t.G).left) ≫ (fst (Over.mk x0) t.G).left =
        spMap (algebraMap S (Jet S (Fin 1 × Fin d) m)) := fun a => by
    constructor
    · rw [← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_snd]
    · rw [← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_fst, Category.id_comp]; rfl
  have a₂ : ((ptSecT t'.G (x' m)).left ≫ (jBaseG x0' d m 1 ▷ t'.G).left) ≫ pm =
      (ptSecT t.G (x m)).left ≫ (jBaseG x0 d m 1 ▷ t.G).left := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) p₁).trans ((a₁ (x' m)).2.trans (a₁ (x m)).2.symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) p₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ν.φ) (a₁ (x' m)).1).trans ((hx m).trans (a₁ (x m)).1.symm))))
  have q₆ := sv_pullSec hp' (r ≫ (ptSecT t'.G (x' m)).left) z hJ'
  rw [← q₆, q₁, q₂, Category.assoc r, Category.assoc r, Category.assoc r, a₂, (a₁ (x' m)).1] at q₅
  refine (sv_pullSec hp _ z hJ).trans ?_
  rw [Category.assoc r]
  refine q₅.trans ?_
  rw [q₃, q₄, mul_pow, Units.val_mul]
  exact mul_left_comm _ _ _

theorem gs_appLE {A B Z : Scheme.{0}} (g : B ⟶ A) (r : Z ⟶ B) (z : Z) {U : A.Opens} {W : B.Opens} (h : W ≤ g ⁻¹ᵁ U)
    (hz : r z ∈ W) (a : Γ(A, U)) : gs r z W ((g.appLE U W h).hom a) = gs (r ≫ g) z U a :=
  (gs_res r z h hz ((g.app U).hom a)).trans (gs_pull r g z U (h hz) a)

theorem gs_pow {A Z : Scheme.{0}} (r : Z ⟶ A) (z : Z) (U : A.Opens) (h : r z ∈ U) (a : Γ(A, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem sv_of_charts {T : Over X} {T' : Over X'} {pm : (T' ⊗ t'.G).left ⟶ (T ⊗ t.G).left}
    (p₂ : pm ≫ (snd T t.G).left = (snd T' t'.G).left ≫ ν.φ) {a : ℤ} {k : ℕ}
    {s' : LB.Sec (LPow t'.G t'.PP.L a T')} {s : LB.Sec (LPow t.G t.PP.L a T)}
    (h : ∀ (i : t.PP.L.ι) (j : t'.PP.L.ι) (W : (T' ⊗ t'.G).left.Opens)
      (h₀ : W ≤ (snd T' t'.G).left ⁻¹ᵁ ((LB.div (t.PP.L.pull ν.cm.F) t'.PP.L).U ((fun _ => i), j)))
      (h₁ : W ≤ pm ⁻¹ᵁ (LPow t.G t.PP.L a T).U (fun _ => i)) (h₂ : W ≤ (LPow t'.G t'.PP.L a T').U (fun _ => j)),
      (pm.appLE ((LPow t.G t.PP.L a T).U (fun _ => i)) W h₁).hom (s.f (fun _ => i)) =
        ((snd T' t'.G).left.appLE ((LB.div (t.PP.L.pull ν.cm.F) t'.PP.L).U ((fun _ => i), j)) W h₀).hom
          (Units.val (w.s ((fun _ => i), j))) ^ k *
        ((T' ⊗ t'.G).left.presheaf.map (homOfLE h₂).op).hom (s'.f (fun _ => j)))
    (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ t'.G).left) (z : Z) (J J') (hJ : Good t.PP.L z J) (hJ' : Good t'.PP.L z J') :
    sv t s (r ≫ pm) z J = (om w z J J' (r ≫ (snd T' t'.G).left) ^ k).val * sv t' s' r z J' := by
  let i := J ((r ≫ (snd T' t'.G).left) ≫ ν.cm.F)
  let j := J' (r ≫ (snd T' t'.G).left)
  let W := (snd T' t'.G).left ⁻¹ᵁ ((LB.div (t.PP.L.pull ν.cm.F) t'.PP.L).U ((fun _ => i), j))
  have h₁ : W ≤ pm ⁻¹ᵁ (LPow t.G t.PP.L a T).U (fun _ => i) := fun y hy => Set.mem_iInter.2 fun _ => by
    show (pm ≫ (snd T t.G).left) y ∈ t.PP.L.U i
    rw [p₂]
    exact mem_pull.1 hy.1
  have h₂ : W ≤ (LPow t'.G t'.PP.L a T').U (fun _ => j) := fun y hy => Set.mem_iInter.2 fun _ => hy.2
  have hz : r z ∈ W := ⟨mem_pull.2 (hJ ((r ≫ (snd T' t'.G).left) ≫ ν.cm.F)), hJ' (r ≫ (snd T' t'.G).left)⟩
  have e := congrArg (gs r z W) (h i j W le_rfl h₁ h₂)
  rw [gs_appLE _ r z _ hz, gs_mul r z W hz, gs_pow r z W hz, gs_appLE _ r z _ hz, gs_res r z h₂ hz] at e
  refine (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => a) s _ z J (fun _ => i)
    (fun _ => by rw [Category.assoc, p₂, ← Category.assoc])).trans (e.trans (congrArg₂ (· * ·) ?_ rfl))
  rw [Units.val_pow_eq_pow_val]
  exact congrArg (· ^ k) (gs_unit (r ≫ (snd T' t'.G).left) z _ hz _)

end Chart

section Main

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
  {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]

theorem const_ad {d : ℕ} (B : Germ.FB S d (𝓞 E)) (a : 𝓞 E) : MvPowerSeries.constantCoeff (B.ad a) = 1 := by
  have e := CIndBCNab.const_ev (n := 1) ![0, Germ.pt S (n := 1) d 0]
    (by intro p q; fin_cases p <;> simp [Germ.pt]) (B.ad a)
  rw [B.adjoint_zero_fst a, map_one] at e
  exact e.symm

set_option maxHeartbeats 400000 in

theorem exists_chart_push (hG : GlobalFnsSt) {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) {y y' : FrPt Xo c S}
    {pm : Gx y.x ⟶ Gx y'.x} {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (h0 : y'.x = y.x ≫ ρ)
    (p₁ : pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left)
    (p₂ : pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ)
    (hw : CubIso ν w) (hu : ∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) (C : ChartAt Xo c y) :
    ∃ (x : ∀ m, jO y' C.d m 1 ⟶ Xo.univ.t.G) (e : ∀ m, FrTy y' C.d x m),
      IsChart y' C.d C.B.G.F C.B.A.act C.uvec x ∧
      IsFrame y' C.d x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y' C.d x C.B.A.act e C.wP 0)
          (homAt y'.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y'.x S) 1) ∧
      ∀ (k : ℕ) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y'.x))),
        (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx y.x) (z : Z) J J', Good Xo.univ.t.PP.L z J → Good Xo.univ.t.PP.L z J' →
          sv Xo.univ.t s' (r ≫ pm) z J =
            (om w z J J' (r ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) ^ k).val * sv Xo.univ.t s r z J') →
        ∀ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k s f → IsGerm y' C.d x C.B.A.act e C.wP k s' f := by
  have hA := isAbelianScheme_univ Xo
  have hc := (isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  have hf := (isFrame_iff y C.d C.x _ _ _ _ _ _ C.e).1 C.frame
  have hP := (isPrim_iff C.wP).1 C.prim
  have hc₁ := isChart_push (ν := ν) h0.symm hc
  have hx : ∀ m, (C.x m).left ≫ ν.φ = (pu ν h0.symm _ (C.x m)).left := fun _ => rfl
  obtain ⟨e, hg, he⟩ := exists_frRel (x := fun m => pu ν h0.symm _ (C.x m)) hw.1 hx C.e hf.gen
  have g₁ := isFrame_push hG hA hw.1 hw.2.2 hc hx he hg (const_ad C.B) hf
  have r₀ : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _
      (eLG Xo.univ.t y.x C.d C.x C.B.A.act C.e C.wP 0) (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) := C.rig0
  have g₂ := rig_push hG hA hw.1 h0.symm hw.2.1 hP hP hc hx he r₀
  have e₁ : (fun ℓ : Lt1 Dw => y'.u ℓ.1 ℓ.2) = fun ℓ => y.u ℓ.1 ℓ.2 ≫ ν.φ := funext fun ℓ => hu _ _
  refine ⟨fun m => pu ν h0.symm _ (C.x m), e, ?_, ?_, ?_, fun k s s' hs f hf => ?_⟩
  · refine (isChart_iff y' C.d _ _ _ _).2 ?_
    rw [e₁]
    exact hc₁
  · exact (isFrame_iff y' C.d _ _ _ _ _ _ _ e).2 g₁
  · exact g₂
  · have hf' := (isGerm_iff y C.d _ _ _ _ k s f).1 hf
    have g₃ := isGerm_push hG hA hw.1 hw.2.1 hP hP hc hc₁ hx he hg p₁ p₂ hs hf'
    exact (isGerm_iff y' C.d _ _ e _ k s' f).2 g₃

theorem chartVal_smul {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ}
    (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (P : MvPolynomial (LtN Dw n) c.F) (a : c.F)
    (h : (a • P).support = P.support) : chartVal C k f (a • P) = algebraMap c.F S a * chartVal C k f P := by
  rw [chartVal, chartVal, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc]

theorem nab_push (hG : GlobalFnsSt) (hC : ChartIndepSt2) {nab : NabV Xo c} (hn : IsNab Xo c nab) {ρ : Xo.X ⟶ Xo.X}
    (ν : SABMap Xo.univ.t Xo.univ.t ρ) {y y' : FrPt Xo c S}
    {pm : Gx y.x ⟶ Gx y'.x} {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (h0 : y'.x = y.x ≫ ρ)
    (p₁ : pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left)
    (p₂ : pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ)
    (hw : CubIso ν w) (hu : ∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (k : ℕ) (b : ℤ)
    (hb : b = k) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L b (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L b (ptO Xo y'.x)))
    (hF : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Gx y.x) (z : Z) J J', Good Xo.univ.t.PP.L z J → Good Xo.univ.t.PP.L z J' →
      sv Xo.univ.t (F' i) (r ≫ pm) z J =
        (om w z J J' (r ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) ^ k).val * sv Xo.univ.t (F i) r z J') :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ i, nab y' b (F' i) (colOf m i) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ i, nab y b (F i) (colOf m i) := by
  subst hb
  obtain ⟨C, hex, hpin⟩ := hn.2 S y
  obtain ⟨C', hex', hpin'⟩ := hn.2 S y'
  choose f hf using fun i => hex k (F i)
  choose f' hf' using fun i => hex' k (F' i)
  obtain ⟨x, e, h₁, h₂, h₃, h₄⟩ := exists_chart_push hG ν h0 p₁ p₂ hw hu C
  let C₁ : ChartAt Xo c y' := ⟨C.d, C.B, C.uvec, x, e, C.wP, C.h, h₁, h₂, C.prim, C.gauge, h₃⟩
  obtain ⟨N, hN, hNP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have key := hC E H Dw l Xo c hn.1 S y' C' C₁ k n F' f' f hf' (fun i => h₄ k (F i) (F' i) (hF i) _ (hf i)) a _ hNP
  rw [chartVal_smul _ _ _ _ _ hsupp, chartVal_smul _ _ _ _ _ hsupp] at key
  have hunit : IsUnit (algebraMap c.F S (N : c.F)) := (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hN.ne')).map _
  have key' := hunit.mul_left_cancel key
  have e₁ : ∀ m, ∏ i, nab y k (F i) (colOf m i) =
      ∏ i, C.B.nabVal S C.h H.w0 k (f i) C.uvec (MvPolynomial.monomial (colOf m i) 1) := fun m =>
    Finset.prod_congr rfl fun i _ => hpin k (F i) (f i) (hf i) (colOf m i)
  have e₂ : ∀ m, ∏ i, nab y' k (F' i) (colOf m i) =
      ∏ i, C'.B.nabVal S C'.h H.w0 k (f' i) C'.uvec (MvPolynomial.monomial (colOf m i) 1) := fun m =>
    Finset.prod_congr rfl fun i _ => hpin' k (F' i) (f' i) (hf' i) (colOf m i)
  simp only [e₁, e₂]
  exact key'

end Main

theorem nab_harmonic_invariant : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c S) (pm : Gx y.x ⟶ Gx y'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)), y'.x = y.x ≫ ρ → pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left → pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ → CubIso ν w → (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, (∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx y.x).Opens) (h₀ : W ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))) (h₁ : W ≤ pm ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)).U (fun _ => i)) (h₂ : W ≤ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)).U (fun _ => j)), (pm.appLE ((LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)).U (fun _ => i)) W h₁).hom ((F' b).f (fun _ => i)) = ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) W h₀).hom (Units.val (w.s ((fun _ => i), j))) ^ (N ^ 2) * ((Gx y.x).presheaf.map (homOfLE h₂).op).hom ((F b).f (fun _ => j)))) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hn S _ _ ρ ν y y' pm w h0 p₁ p₂ hw hu n a P hP N F F' hF
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  exact nab_push hL.globalFns hC hn ν h0 p₁ p₂ hw hu hP (N ^ 2) _ (Nat.cast_pow N 2).symm F F'
    fun i => sv_of_charts p₂ (hF i)

end GlobalTheory.ChartPush
