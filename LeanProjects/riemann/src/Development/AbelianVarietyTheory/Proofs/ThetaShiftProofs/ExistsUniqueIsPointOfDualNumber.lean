import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPushoutQuotientMap

noncomputable section

namespace GlobalTheory.FormalPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Ratio

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem exists_ratio (hL : L.IsLB) (h : FormEq φ' ε' φ ε) (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ ρ : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t r z J = gm r z ⊤ ρ * val t' r z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL h t' ht'
  obtain ⟨ρ, hρ⟩ := TLinPf.ratio_glue _ (TLinPf.linComb_cover L hL φ ε) t u ht hu
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ]
  exact (congrArg (gm r z _) (hρ _)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) ρ) rfl))

theorem appTop_eq_of_gm {Y' Z : Scheme.{0}} (r : Z ⟶ Y) (r' : Z ⟶ Y') (a : Γ(Y, ⊤)ˣ) (b : Γ(Y', ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ a = gm r' z ⊤ b) : r.appTop.hom a.val = r'.appTop.hom b.val := by
  have : pullU r ⊤ a = pullU r' ⊤ b := unit_ext (V := ⊤) fun z _ => by
    have e₁ := gm_pull (𝟙 Z) r z ⊤ trivial a
    have e₂ := gm_pull (𝟙 Z) r' z ⊤ trivial b
    rw [Category.id_comp] at e₁ e₂
    exact e₁.trans ((h z).trans e₂.symm)
  exact congrArg Units.val this

theorem appTop_eq_one_of_gm {Z : Scheme.{0}} (r : Z ⟶ Y) (a : Γ(Y, ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ a = 1) : r.appTop.hom a.val = 1 :=
  (appTop_eq_of_gm r r a 1 fun z => (h z).trans (map_one _).symm).trans (map_one _)

theorem val_eq_of_epi (hL : L.IsLB) (h : FormEq φ' ε' φ ε) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) {W : Scheme.{0}} (p : W ⟶ Y) [Epi p]
    (hp : ∀ w J, Good L w J → val t p w J = val t' p w J)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) : val t r z J = val t' r z J := by
  obtain ⟨ρ, hρ⟩ := exists_ratio hL h t t' ht ht'
  have h1 : p.appTop.hom ρ.val = 1 := appTop_eq_one_of_gm p ρ fun w => by
    obtain ⟨J, hJ⟩ := TLinPf.idx_exists L hL w
    exact mul_eq_right.1 ((hρ W p w J hJ).symm.trans (hp w J hJ))
  have h2 : ρ = 1 := Units.ext (FunDescent.appTop_injective p (h1.trans (map_one _).symm))
  rw [hρ Z r z J hJ, h2, map_one, _root_.one_mul]

end Ratio

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

omit [IsDomain R] [IsCommMonObj G] in

theorem map_mul_fstG {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a b : Z ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).map (a * b) ≫ fstG I e G =
      ((Over.map (thick R I e)).map a ≫ fstG I e G) * ((Over.map (thick R I e)).map b ≫ fstG I e G) :=
  Over.OverMorphism.ext (TorusToProper.mul_left_fst (thick R I e) G (a := Z.hom) (c := Z.hom ≫ thick R I e) a b
    ((Over.map (thick R I e)).map a ≫ fstG I e G) ((Over.map (thick R I e)).map b ≫ fstG I e G) rfl rfl)

theorem prod_Oφ {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (p : T ⟶ D.P.A) (χ : D.X)
    {U : Type} [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ D.Oφ p χ k) ^ Oinvε k =
      (h (cP D T' χ * (ρ ≫ p)).left)⁻¹ * h (cP D T' χ).left * h (ρ ≫ p).left * (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  simp only [WeightPf.Oφ_comp]
  rw [Fin.prod_univ_four, mul_comm (cP D T' χ)]
  show h ((ρ ≫ p) * cP D T' χ).left ^ (-1 : ℤ) * h (cP D T' χ).left ^ (1 : ℤ) * h (ρ ≫ p).left ^ (1 : ℤ) *
    h (1 : T' ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_gtφT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (p : T ⟶ D.P.A) (χ : D.X)
    {U : Type} [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ DegPre.gtφT D T p χ k) ^ DegPre.gtε k =
      (h (cP D T' χ * (ρ ≫ p)).left)⁻¹ * h (cP D T' χ).left * h (ρ ≫ p).left * (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, ← comp_cP D ρ, ← MonObj.comp_mul, ← MonObj.comp_one ρ]
  show h (ρ ≫ (cP D T χ * p)).left ^ (-1 : ℤ) * h (ρ ≫ cP D T χ).left ^ (1 : ℤ) * h (ρ ≫ p).left ^ (1 : ℤ) *
    h (ρ ≫ (1 : T ⟶ D.P.A)).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem val_s_add {T T' : Over (Spec (CommRingCat.of R))} (g : GtPt D T) (ρ : T' ⟶ T) {z : T'.left} {J}
    (hJ : Good D.P.L z J) (χ χ' : D.X) :
    val (g.s (χ + χ')) ρ.left z J * th D z J (cP D T' χ) (cP D T' χ') (ρ ≫ g.b) =
      val (g.s χ) ρ.left z J * val (g.s χ') ρ.left z J := by
  rw [← comp_cP D ρ, ← comp_cP D ρ]
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub ρ hJ _ _ _))).symm.trans
    ((val_corr hJ (g.mult χ χ') ρ.left).trans (val_mul hJ _ _ _))

variable (c : GtCoord I D e G)

theorem val_t_add {T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ (Over.map (thick R I e)).obj (thickObj R I e G)) {z : T'.left} {J}
    (hJ : Good D.P.L z J) (χ χ' : D.X) :
    val (c.t (χ + χ')) ρ.left z J * th D z J (cP D T' χ) (cP D T' χ') (ρ ≫ c.pG) =
      val (c.t χ) ρ.left z J * val (c.t χ') ρ.left z J := by
  rw [← comp_cP D ρ, ← comp_cP D ρ]
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub ρ hJ _ _ _))).symm.trans
    ((val_corr hJ (c.t_mul χ χ') ρ.left).trans (val_mul hJ _ _ _))

section
variable {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}

theorem im_eq (y : Z ⟶ thickObj R I e G) :
    TorusCoord.im c y = (Over.map (thick R I e)).map (y ≫ c.q) ≫ fstG I e D.P.A := by
  rw [Functor.map_comp, Category.assoc]; rfl

theorem val_t_weight (χ : D.X) (τ : Z ⟶ WeightPf.Te D I e) (y : Z ⟶ thickObj R I e G)
    {W : Scheme.{0}} (r : W ⟶ Z.left) {z : W} {J} (hJ : Good D.P.L z J) :
    val (c.t χ) (r ≫ ((τ ≫ c.i) * y).left) z J =
      gm (r ≫ τ.left) z ⊤ (charUnit _ D.X χ) * val (c.t χ) (r ≫ y.left) z J := by
  have h := val_corr hJ (c.t_weight χ) (r ≫ (lift τ y).left)
  have e₁ : lift τ y ≫ WeightPf.act c = (τ ≫ c.i) * y := by
    have h1 : WeightPf.act c = (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ c.i) * snd _ _ := rfl
    rw [h1, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e₂ : (r ≫ (lift τ y).left) ≫ (WeightPf.act c).left = r ≫ ((τ ≫ c.i) * y).left := by
    rw [Category.assoc, ← Over.comp_left, e₁]
  have e₃ : (r ≫ (lift τ y).left) ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left = r ≫ y.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd]
  have e₄ : (r ≫ (lift τ y).left) ≫ (fst (WeightPf.Te D I e) (thickObj R I e G)).left = r ≫ τ.left := by
    rw [Category.assoc, ← Over.comp_left, lift_fst]
  rw [← e₂, ← e₃, ← e₄]
  refine (val_pull hJ _ _ _).symm.trans (h.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ?_ (val_pull hJ _ _ _))))
  exact (gm_res _ z _ (hJ.mem (PEmpty.elim : PEmpty → (_ ⟶ D.P.A.left)) _) _).trans
    (gm_pull _ _ z ⊤ trivial _)

end

theorem formEq_of_comp {T T' : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (r : T' ⟶ T)
    (x : T' ⟶ (Over.map (thick R I e)).obj (thickObj R I e G)) (h : x ≫ c.pG = r ≫ b) (χ : D.X) :
    FormEq (fun k => x.left ≫ D.Oφ c.pG χ k) Oinvε (fun k => r.left ≫ DegPre.gtφT D T b χ k) DegPre.gtε :=
  fun U _ f => (prod_Oφ x c.pG χ f).trans (by rw [h]; exact (prod_gtφT r b χ f).symm)

theorem exists_point {T : Over (Spec (CommRingCat.of R))} (g : GtPt D T)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : (Over.map (thick R I e)).obj Z ⟶ T) :
    ∃ x : Z.left ⟶ (thickObj R I e G).left, x ≫ c.pG.left = r.left ≫ g.b.left ∧
      ∀ χ (W : Scheme.{0}) (k : W ⟶ Z.left) (z : W) (J), Good D.P.L z J →
        val (c.t χ) (k ≫ x) z J = val (g.s χ) (k ≫ r.left) z J := by
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have := c.q_hom
  let β : Z.left ⟶ (thickObj R I e D.P.A).left := pullback.lift (r ≫ g.b).left Z.hom (Over.w (r ≫ g.b))
  have β₁ : β ≫ pullback.fst D.P.A.hom (thick R I e) = (r ≫ g.b).left := pullback.lift_fst _ _ _
  have β₂ : β ≫ (thickObj R I e D.P.A).hom = Z.hom := pullback.lift_snd _ _ _
  let W : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (pullback.fst c.q.left β ≫ (thickObj R I e G).hom)
  let y : W ⟶ thickObj R I e G := Over.homMk (pullback.fst c.q.left β) rfl
  let p : W ⟶ Z := Over.homMk (pullback.snd c.q.left β) (by
    change pullback.snd c.q.left β ≫ Z.hom = pullback.fst c.q.left β ≫ (thickObj R I e G).hom
    rw [← β₂, ← Over.w c.q, pullback.condition_assoc])
  have hE : EffectiveEpi p.left := inferInstanceAs (EffectiveEpi (pullback.snd c.q.left β))
  let s : (Over.map (thick R I e)).obj W ⟶ T := (Over.map (thick R I e)).map p ≫ r
  have hy : TorusCoord.im c y = s ≫ g.b := Over.OverMorphism.ext (by
    change pullback.fst c.q.left β ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R I e) =
      (pullback.snd c.q.left β ≫ r.left) ≫ g.b.left
    rw [pullback.condition_assoc, β₁, Category.assoc]; rfl)
  have H : ∀ χ, ∃ ρ : Γ(W.left, ⊤)ˣ, ∀ (V : Scheme.{0}) (k : V ⟶ W.left) (z : V) (J), Good D.P.L z J →
      val (g.s χ) (k ≫ s.left) z J = gm k z ⊤ ρ * val (c.t χ) (k ≫ y.left) z J := fun χ => by
    obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB (formEq_of_comp c g.b s ((Over.map (thick R I e)).map y) hy χ)
      (LB.pullGen D.P.L _ _ (g.s χ) s.left) (LB.pullGen D.P.L _ _ (c.t χ) y.left)
      (pullGen_isGen _ _ _ _ (g.isGen χ) _) (pullGen_isGen _ _ _ _ (c.t_gen χ) _)
    exact ⟨ρ, fun V k z J hJ => (val_pull hJ _ _ _).symm.trans ((hρ V k z J hJ).trans
      (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))⟩
  choose ρ hρ using H
  have hm : ∀ χ χ', ρ (χ + χ') = ρ χ * ρ χ' := fun χ χ' => unit_ext (V := ⊤) fun z _ => by
    obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB z
    have a₀ := hρ (χ + χ') _ (𝟙 _) z J hJ
    have a₁ := hρ χ _ (𝟙 _) z J hJ
    have a₂ := hρ χ' _ (𝟙 _) z J hJ
    rw [Category.id_comp, Category.id_comp] at a₀ a₁ a₂
    have b₁ := val_s_add g s (z := z) hJ χ χ'
    have b₂ := val_t_add c ((Over.map (thick R I e)).map y) (z := z) hJ χ χ'
    rw [← hy] at b₁
    have key : ∀ {U : Type} [CommGroup U] (s₀ s₁ s₂ t₀ t₁ t₂ r₀ r₁ r₂ θ : U), s₀ = r₀ * t₀ → s₁ = r₁ * t₁ →
        s₂ = r₂ * t₂ → s₀ * θ = s₁ * s₂ → t₀ * θ = t₁ * t₂ → r₀ = r₁ * r₂ := by
      intro U _ s₀ s₁ s₂ t₀ t₁ t₂ r₀ r₁ r₂ θ h₀ h₁ h₂ h₃ h₄
      rw [h₀, h₁, h₂, _root_.mul_assoc, h₄, _root_.mul_mul_mul_comm] at h₃
      exact mul_right_cancel h₃
    exact (key _ _ _ _ _ _ _ _ _ _ a₀ a₁ a₂ b₁ b₂).trans (map_mul _ _ _).symm
  obtain ⟨E, hE'⟩ := exists_splitTorus_points_mulEquiv _ D.X W
  obtain ⟨τ, hτ⟩ := E.surjective (MonoidHom.mk' (fun χ => ρ χ.toAdd) fun χ χ' => hm _ _)
  have hτ' : ∀ χ, pullU τ.left ⊤ (charUnit _ D.X χ) = ρ χ := fun χ =>
    Units.ext ((hE' τ χ).symm.trans (by rw [hτ]; rfl))
  let y' : W ⟶ thickObj R I e G := (τ ≫ c.i) * y
  have hv : ∀ χ (V : Scheme.{0}) (k : V ⟶ W.left) (z : V) (J), Good D.P.L z J →
      val (c.t χ) (k ≫ y'.left) z J = val (g.s χ) (k ≫ s.left) z J := fun χ V k z J hJ =>
    (val_t_weight c χ τ y k hJ).trans ((congrArg₂ (· * ·)
      ((gm_pull k τ.left z ⊤ trivial _).symm.trans (congrArg (gm k z ⊤) (hτ' χ))) rfl).trans (hρ χ V k z J hJ).symm)
  have hq : y' ≫ c.q = y ≫ c.q := by
    rw [MonObj.mul_comp, Category.assoc, WeightPf.i_q, ← Category.assoc, comp_toUnit, ← Hom.one_def,
      _root_.one_mul]
  have hb : y'.left ≫ c.pG.left = p.left ≫ r.left ≫ g.b.left := by
    have h₁ : TorusCoord.im c y' = s ≫ g.b := by rw [im_eq, hq, ← im_eq, hy]
    exact (congrArg (fun q => q.left) h₁).trans (Category.assoc _ _ _)
  have hd : ∀ {V : Scheme.{0}} (g₁ g₂ : V ⟶ W.left), g₁ ≫ p.left = g₂ ≫ p.left → g₁ ≫ y'.left = g₂ ≫ y'.left := by
    intro V g₁ g₂ h
    refine TorusCoord.ext_of_val c _ _ (by rw [Category.assoc, Category.assoc, hb, reassoc_of% h]) fun χ z J hJ => ?_
    have h' : g₁ ≫ s.left = g₂ ≫ s.left := by
      change g₁ ≫ p.left ≫ r.left = g₂ ≫ p.left ≫ r.left
      rw [reassoc_of% h]
    rw [hv χ V g₁ z J hJ, hv χ V g₂ z J hJ, h']
  have hx := EffectiveEpi.fac p.left y'.left hd
  generalize EffectiveEpi.desc p.left y'.left hd = x at hx
  have hxb : x ≫ c.pG.left = r.left ≫ g.b.left := by
    rw [← cancel_epi p.left, reassoc_of% hx, hb]
  let x' : (Over.map (thick R I e)).obj Z ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) :=
    Over.homMk x ((congrArg (x ≫ ·) (Over.w c.pG).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.P.A.hom) hxb).trans (Over.w (r ≫ g.b)))))
  refine ⟨x, hxb, fun χ V k z J hJ => ?_⟩
  refine (val_pull hJ _ _ _).symm.trans (Eq.trans ?_ (val_pull hJ _ _ _))
  refine (val_eq_of_epi D.P.isLB (formEq_of_comp c g.b r x' (Over.OverMorphism.ext hxb) χ)
    (pullGen_isGen _ _ _ _ (g.isGen χ) r.left) (pullGen_isGen _ _ _ _ (c.t_gen χ) x) p.left
    (fun w J hJ => ?_) V k z J hJ).symm
  have h := hv χ _ (𝟙 _) w J hJ
  rw [Category.id_comp, Category.id_comp, ← hx] at h
  exact (val_pull hJ _ _ _).trans (h.symm.trans (val_pull hJ _ _ _).symm)

end Level

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {T : Over (Spec (CommRingCat.of R))}

def HasCoords (e : ℕ) (g : GtPt D.toPre T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (y : Z ⟶ (thickObj R I e G).left) : Prop :=
  y ≫ (U.gt e).pG.left = r ≫ g.b.left ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _
    (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) y) (LB.pullGen D.toPre.P.L _ _ (g.s χ) r)

def IsPointOf (g : GtPt D.toPre T) (x : T ⟶ G) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (y : Z ⟶ (thickObj R I e G).left),
    y ≫ (fstG I e G).left = r ≫ x.left → HasCoords U e g r y

def IsSmulPt {D : DegPre R} {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O)
    (g g' : GtPt D T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.b).left)) (g'.s χ)

theorem hasCoords_iff (e : ℕ) (g : GtPt D.toPre T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (y : Z ⟶ (thickObj R I e G).left) :
    HasCoords U e g r y ↔ y ≫ (U.gt e).pG.left = r ≫ g.b.left ∧
      ∀ χ z J, Good D.toPre.P.L z J → val ((U.gt e).t χ) y z J = val (g.s χ) r z J := by
  refine and_congr Iff.rfl (forall_congr' fun χ => ⟨fun h z J hJ => ?_, fun h => ?_⟩)
  · have := val_corr hJ h (𝟙 _)
    rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at this
  · refine corr_of_val D.toPre.P.isLB fun z J hJ => ?_
    rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
    exact h z J hJ

variable {U} in
theorem HasCoords.comp {e : ℕ} {g : GtPt D.toPre T} {Z W : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : HasCoords U e g r y) (k : W ⟶ Z) :
    HasCoords U e g (k ≫ r) (k ≫ y) :=
  (hasCoords_iff U e g _ _).2 ⟨by rw [Category.assoc, h.1, Category.assoc], fun χ _ _ hJ =>
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) k).trans (val_pull hJ _ _ _))⟩

variable {U} in

theorem HasCoords.unique {e : ℕ} {g : GtPt D.toPre T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y y' : Z ⟶ (thickObj R I e G).left} (h : HasCoords U e g r y) (h' : HasCoords U e g r y') : y = y' := by
  rw [hasCoords_iff] at h h'
  exact TorusCoord.ext_of_val (U.gt e) _ _ (h.1.trans h'.1.symm) fun χ z J hJ => (h.2 χ z J hJ).trans (h'.2 χ z J hJ).symm

theorem exists_hasCoords (e : ℕ) (g : GtPt D.toPre T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (σ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (h : σ ≫ thick R I e = r ≫ T.hom) :
    ∃ y, HasCoords U e g r y := by
  obtain ⟨y, h₁, h₂⟩ := exists_point (U.gt e) g (Z := Over.mk σ) (Over.homMk r h.symm)
  refine ⟨y, (hasCoords_iff U e g _ _).2 ⟨h₁, fun χ z J hJ => ?_⟩⟩
  have := h₂ χ _ (𝟙 _) z J hJ
  rwa [Category.id_comp, Category.id_comp] at this

variable {U} in

theorem HasCoords.succ {e : ℕ} {g : GtPt D.toPre T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : HasCoords U e g r y) :
    HasCoords U (e + 1) g r (y ≫ thickMap R I e G) := by
  rw [hasCoords_iff] at h ⊢
  exact ⟨by rw [Category.assoc, U.gt_q, h.1], fun χ z J hJ =>
    (val_pull hJ _ _ _).symm.trans ((val_corr hJ (U.gt_t e χ) y).trans (h.2 χ z J hJ))⟩

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
instance mono_fstG (e : ℕ) : Mono (fstG I e G).left :=
  inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem exists_lift_fstG {e : ℕ} {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (w : (Over.map (thick R I e)).obj Z ⟶ G) :
    ∃ a : Z ⟶ thickObj R I e G, (Over.map (thick R I e)).map a ≫ fstG I e G = w :=
  ⟨Over.homMk (pullback.lift w.left Z.hom (Over.w w)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem eq_of_map_fstG {e : ℕ} {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {a b : Z ⟶ thickObj R I e G}
    (h : (Over.map (thick R I e)).map a ≫ fstG I e G = (Over.map (thick R I e)).map b ≫ fstG I e G) : a = b :=
  Over.OverMorphism.ext ((cancel_mono (fstG I e G).left).1 (congrArg (fun q => q.left) h))

theorem isPointOf_iff (g : GtPt D.toPre T) (x : T ⟶ G) :
    IsPointOf U g x ↔ ∀ (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (r : (Over.map (thick R I e)).obj Z ⟶ T) (a : Z ⟶ thickObj R I e G),
      (Over.map (thick R I e)).map a ≫ fstG I e G = r ≫ x → TorusCoord.im (U.gt e) a = r ≫ g.b ∧
        ∀ χ z J, Good D.toPre.P.L z J →
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J = val (g.s χ) r.left z J := by
  constructor
  · intro h e Z r a ha
    obtain ⟨h₁, h₂⟩ := (hasCoords_iff U e g _ _).1
      (h e _ r.left ((Over.map (thick R I e)).map a).left (congrArg (fun q => q.left) ha))
    exact ⟨Over.OverMorphism.ext h₁, h₂⟩
  · intro h e Z r y hy
    have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
    obtain ⟨h₁, h₂⟩ := h e (Over.mk (y ≫ (thickObj R I e G).hom)) (Over.homMk r w) (Over.homMk y rfl)
      (Over.OverMorphism.ext hy)
    exact (hasCoords_iff U e g _ _).2 ⟨congrArg (fun q => q.left) h₁, h₂⟩

variable {U}

theorem IsPointOf.comp_fstG_eq {g : GtPt D.toPre T} {x : T ⟶ G} (hx : IsPointOf U g x) {e : ℕ} {Z : Scheme.{0}}
    {r : Z ⟶ T.left} {y : Z ⟶ (thickObj R I e G).left} (h : HasCoords U e g r y) :
    y ≫ (fstG I e G).left = r ≫ x.left := by
  have w : (r ≫ x.left) ≫ G.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [Category.assoc, Over.w x, ← Over.w g.b, ← Category.assoc, ← h.1, Category.assoc, Over.w (U.gt e).pG,
      Category.assoc]; rfl
  have h' : pullback.lift _ _ w ≫ (fstG I e G).left = r ≫ x.left := pullback.lift_fst _ _ _
  rw [h.unique (hx e Z r _ h'), h']

theorem IsPointOf.pull {T' : Over (Spec (CommRingCat.of R))} (k : T' ⟶ T) {g : GtPt D.toPre T}
    {g' : GtPt D.toPre T'} {x : T ⟶ G} (hx : IsPointOf U g x) (h : GtPt.IsPull k.left g g') :
    IsPointOf U g' (k ≫ x) := by
  intro e Z r y hy
  obtain ⟨h₁, h₂⟩ := (hasCoords_iff U e g _ _).1 (hx e Z (r ≫ k.left) y (hy.trans (Category.assoc _ _ _).symm))
  exact (hasCoords_iff U e g' _ _).2 ⟨by rw [h₁, h.1, Category.assoc], fun χ z J hJ =>
    (h₂ χ z J hJ).trans ((val_pull hJ _ _ _).symm.trans (val_corr hJ (h.2 χ) r).symm)⟩

variable (U) in

theorem isPointOf_one {g : GtPt D.toPre T} (h : g.IsZero) : IsPointOf U g 1 := by
  rw [isPointOf_iff]
  intro e Z r a ha
  have h1 : (Over.map (thick R I e)).map (1 : Z ⟶ thickObj R I e G) ≫ fstG I e G = 1 := by
    have := map_mul_fstG (1 : Z ⟶ thickObj R I e G) 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  obtain rfl : a = 1 := eq_of_map_fstG (by rw [ha, h1, MonObj.comp_one])
  refine ⟨by rw [TorusCoord.im_one, h.1]; exact (MonObj.comp_one r).symm, fun χ z J hJ => ?_⟩
  have t₁ := TorusCoord.val_unit (U.gt e) χ (Z := Z) (z := z) hJ
  exact t₁.trans ((val_corr hJ (h.2 χ) r.left).trans (val_one _)).symm

theorem IsPointOf.mul (hG : GlobalFnsSt) {g g' g'' : GtPt D.toPre T} {x x' : T ⟶ G} (hx : IsPointOf U g x)
    (hx' : IsPointOf U g' x') (h : g.IsAdd g' g'') : IsPointOf U g'' (x * x') := by
  rw [isPointOf_iff] at hx hx' ⊢
  intro e Z r y hy
  obtain ⟨a, ha⟩ := exists_lift_fstG (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift_fstG (r ≫ x')
  obtain rfl : y = a * b := eq_of_map_fstG (by rw [hy, map_mul_fstG, ha, hb, MonObj.comp_mul])
  obtain ⟨a₁, a₂⟩ := hx e Z r a ha
  obtain ⟨b₁, b₂⟩ := hx' e Z r b hb
  refine ⟨by rw [TorusCoord.im_mul, a₁, b₁, h.1]; exact (MonObj.comp_mul _ _ _).symm, fun χ z J hJ => ?_⟩
  have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a * b)).left z J *
      th D.toPre z J (cP D.toPre _ χ) (TorusCoord.im (U.gt e) a) (TorusCoord.im (U.gt e) b) =
      val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J *
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map b).left z J :=
    TorusCoord.val_t_mul_points (U.gt e) hG χ a b z J hJ
  have e₂ : val (g''.s χ) r.left z J * th D.toPre z J (r ≫ cP D.toPre T χ) (r ≫ g.b) (r ≫ g'.b) =
      val (g.s χ) r.left z J * val (g'.s χ) r.left z J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.toPre.cub r hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) r.left).trans (val_mul hJ _ _ _))
  rw [a₁, b₁, a₂ χ z J hJ, b₂ χ z J hJ] at e₁
  rw [comp_cP] at e₂
  exact mul_right_cancel (e₁.trans e₂.symm)

theorem IsPointOf.smul (hG : GlobalFnsSt) {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]
    {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hO : U.OLinear O ιD ιA ιG) (a : O)
    {g g' : GtPt D.toPre T} {x : T ⟶ G} (hx : IsPointOf U g x) (h : IsSmulPt ιD a g g') :
    IsPointOf U g' (x ≫ ιG.act a) := by
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  have hr := ιD.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  rw [isPointOf_iff] at hx ⊢
  intro e Z r y hy
  obtain ⟨b, hb⟩ := exists_lift_fstG (r ≫ x)
  have hf : TLinPf.hOv ιG e a ≫ fstG I e G = fstG I e G ≫ ιG.act a :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  obtain rfl : y = b ≫ (Over.pullback (thick R I e)).map (ιG.act a) :=
    eq_of_map_fstG (by rw [hy, Functor.map_comp, Category.assoc, hf, reassoc_of% hb])
  obtain ⟨b₁, b₂⟩ := hx e Z r b hb
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · rw [TorusCoord.im, Functor.map_comp, Category.assoc, TLinPf.hOv_pG U ιD ιG e a (hO.q_lin e), h.1,
      ← Category.assoc, ← Category.assoc r, ← b₁]
  · have e₁ := val_corr hJ (TLinPf.tLin_of hG R I O D A G U ιD ιA ιG hO e a u hu u₀ χ)
      ((Over.map (thick R I e)).map b).left
    have e₂ := val_corr hJ (h.2 u hu u₀ χ) r.left
    have e₃ : ((Over.map (thick R I e)).map b).left ≫ (lift (cP D.toPre _ χ) (U.gt e).pG).left =
        r.left ≫ (lift (cP D.toPre T χ) g.b).left := by
      rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, comp_cP, comp_cP, ← b₁]
    refine ((val_pull hJ _ _ _).symm.trans e₁.symm).trans (Eq.trans ?_ e₂)
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) (b₂ _ z J hJ) ?_) (val_mul hJ _ _ _).symm)
    exact (val_pull hJ _ _ _).trans ((congrArg (fun q => val u q z J) e₃).trans (val_pull hJ _ _ _).symm)

end Main

section Complete

variable {R : Type} [CommRing R] (I : Ideal R) {S : Type} [CommRing S] (φ : R →+* S)

def levelMap (e : ℕ) :
    Spec (CommRingCat.of (S ⧸ I.map φ ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ ^ (e + 1)) φ
    (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))

theorem levelMap_thick (e : ℕ) :
    levelMap I φ e ≫ thick R I e = adicLevelι (I.map φ) (e + 1) ≫ spMap φ := by
  rw [levelMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_factor_level {e : ℕ} {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of S))
    (σ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (h : r ≫ spMap φ = σ ≫ thick R I e) :
    ∃ l, l ≫ adicLevelι (I.map φ) (e + 1) = r := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (NilpotentLift.isPushout_quotient_map (I ^ (e + 1)) (CommRingCat.ofHom φ))
  have hle : I.map φ ^ (e + 1) ≤ (I ^ (e + 1)).map φ := (Ideal.map_pow φ I (e + 1)).ge
  refine ⟨H.lift r σ h ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  exact H.lift_fst r σ h

variable {φ} {G : Over (Spec (CommRingCat.of R))}

def reduction (x : Over.mk (spMap φ) ⟶ G) (e : ℕ) :
    Spec (CommRingCat.of (S ⧸ I.map φ ^ (e + 1))) ⟶ (thickObj R I e G).left :=
  pullback.lift (adicLevelι (I.map φ) (e + 1) ≫ x.left) (levelMap I φ e)
    ((Category.assoc _ _ _).trans ((congrArg _ (Over.w x)).trans (levelMap_thick I φ e).symm))

theorem reduction_fstG (x : Over.mk (spMap φ) ⟶ G) (e : ℕ) :
    reduction I x e ≫ (fstG I e G).left = adicLevelι (I.map φ) (e + 1) ≫ x.left :=
  pullback.lift_fst _ _ _

theorem reduction_hom (x : Over.mk (spMap φ) ⟶ G) (e : ℕ) :
    reduction I x e ≫ (thickObj R I e G).hom = levelMap I φ e :=
  pullback.lift_snd _ _ _

variable {I} [IsDomain R] {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem isPointOf_iff_reduction (g : GtPt D.toPre (Over.mk (spMap φ))) (x : Over.mk (spMap φ) ⟶ G) :
    IsPointOf U g x ↔ ∀ e, HasCoords U e g (adicLevelι (I.map φ) (e + 1)) (reduction I x e) := by
  refine ⟨fun h e => h e _ _ _ (reduction_fstG I x e), fun h e Z r y hy => ?_⟩
  have w : r ≫ (Over.mk (spMap φ)).hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, rfl⟩ := exists_factor_level I φ r _ w
  obtain rfl : y = l ≫ reduction I x e := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, reduction_fstG]
    exact hy.trans (Category.assoc _ _ _)
  exact (h e).comp l

variable [IsLocalRing S]

variable {U} in
theorem IsPointOf.unique [IsHausdorff (I.map φ) S] {g : GtPt D.toPre (Over.mk (spMap φ))}
    {x x' : Over.mk (spMap φ) ⟶ G} (h : IsPointOf U g x) (h' : IsPointOf U g x') : x = x' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map φ) fun e =>
    (reduction_fstG I x e).symm.trans (h'.comp_fstG_eq ((isPointOf_iff_reduction U g x).1 h e)))

theorem existsUnique_isPointOf [IsAdicComplete (I.map φ) S] (g : GtPt D.toPre (Over.mk (spMap φ))) :
    ∃! x : Over.mk (spMap φ) ⟶ G, IsPointOf U g x := by
  refine existsUnique_of_exists_of_unique ?_ fun _ _ h h' => h.unique h'
  choose y hy using fun e =>
    exists_hasCoords U e g (adicLevelι (I.map φ) (e + 1)) (levelMap I φ e) (levelMap_thick I φ e)
  have hf : IsAdicFamily (I.map φ) fun e => y e ≫ (fstG I e G).left := fun e => by
    have h₁ := (hy (e + 1)).comp (adicLevelMap (I.map φ) (Nat.le_succ (e + 1)))
    have h₂ : adicLevelMap (I.map φ) (Nat.le_succ (e + 1)) ≫ adicLevelι (I.map φ) (e + 1 + 1) =
      adicLevelι (I.map φ) (e + 1) := adicLevelMap_ι _ _
    have h₃ : HasCoords U (e + 1) g (adicLevelι (I.map φ) (e + 1))
      (adicLevelMap (I.map φ) (Nat.le_succ (e + 1)) ≫ y (e + 1)) := h₂ ▸ h₁
    have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) G).left) (h₃.unique (hy e).succ)).trans
      ((Category.assoc _ _ _).trans (congrArg _ h₄)))
  obtain ⟨x, ⟨hx₁, hx₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (spMap φ) G.hom hf fun e => by
    have h₁ : (fstG I e G).left ≫ G.hom = (U.gt e).pG.left ≫ D.toPre.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    exact (Category.assoc _ _ _).trans ((congrArg _ h₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.toPre.P.A.hom) (hy e).1).trans ((Category.assoc _ _ _).trans (congrArg _ (Over.w g.b))))))
  refine ⟨Over.homMk x hx₁, (isPointOf_iff_reduction U g _).2 fun e => ?_⟩
  have : reduction I (Over.homMk x hx₁ : Over.mk (spMap φ) ⟶ G) e = y e := by
    rw [← cancel_mono (fstG I e G).left, reduction_fstG]
    exact hx₂ e
  rw [this]
  exact hy e

theorem existsUnique_isPointOf' [IsAdicComplete (I.map φ) S] {s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)}
    (hs : s = spMap φ) (g : GtPt D.toPre (Over.mk s)) : ∃! x : Over.mk s ⟶ G, IsPointOf U g x := by
  subst hs
  exact existsUnique_isPointOf U g

omit [IsLocalRing S] in

theorem existsUnique_isPointOf_unit [IsLocalRing R] [IsAdicComplete I R]
    (g : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))) :
    ∃! x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G, IsPointOf U g x :=
  have : IsAdicComplete (I.map (RingHom.id R)) R := by rwa [Ideal.map_id]
  existsUnique_isPointOf' U (φ := RingHom.id R) (s := 𝟙 _) (Spec.map_id _).symm g

end Complete

end GlobalTheory.FormalPoint
