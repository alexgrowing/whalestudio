import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyGtCoordOfIsGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotCoord

open WeightGen

theorem exists_flat {X B Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (B ⟶ X)} {ε : K → ℤ}
    (f : Y ⟶ B) (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => f ≫ φ k) j →
        r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ => j) ∧
        gm r z (LB.wchart L (fun k => f ≫ φ k) j) (t.s j) =
          gm r z (((LB.LinComb L φ ε).pull f).U (fun _ => j)) (u.s fun _ => j) := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull f).U (fun _ => j) :=
    fun _ _ hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (u.s fun _ => j)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => ⟨le j hj, gm_res r z (le j) hj _⟩⟩
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j) hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (gm_res (𝟙 Y) y (le j') hy.2 _)))).symm)
  refine (gm_gen hu (𝟙 Y) y (le j hy.1) (le j' hy.2)).trans (congrArg (· * _) ?_)
  refine (gm_pull_g _ f (𝟙 Y) y _ _ (le j hy.1) (le j' hy.2)).trans
    ((gm_linComb L φ ε (𝟙 Y ≫ f) y j j' (mem_pull.1 (le j hy.1)) (mem_pull.1 (le j' hy.2))).trans ?_)
  simp only [Category.assoc]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

noncomputable abbrev tact (i : splitTorus S X ⟶ G) : splitTorus S X ⊗ G ⟶ G :=
  lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]

theorem comp_tact (i : splitTorus S X ⟶ G) {Z : Over S} (ρ : Z ⟶ splitTorus S X ⊗ G) :
    ρ ≫ tact i = ((ρ ≫ fst _ _) ≫ i) * (ρ ≫ snd _ _) := by
  rw [Hom.mul_def, comp_lift_assoc, Category.assoc]

theorem exists_wt_gen (i : splitTorus S X ⟶ G) {Y B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K]
    {φ : K → (B ⟶ Y)} {ε : K → ℤ} (f : G.left ⟶ B)
    (hf : (tact i).left ≫ f = (snd (splitTorus S X) G).left ≫ f) (χ : X)
    (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen) (hw : ∀ j, IsWt i _ (u.s j).val χ) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X ⊗ G).left) (z : Z) (J), Good L z J →
        val t (r ≫ (tact i).left) z J = wt X G χ Z r z * val t (r ≫ (snd (splitTorus S X) G).left) z J := by
  obtain ⟨t, ht, hv⟩ := exists_flat f u hu
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have m := hJ.mem (fun k => f ≫ φ k) (r ≫ (snd (splitTorus S X) G).left)
  have m' := hJ.mem (fun k => f ≫ φ k) (r ≫ (tact i).left)
  have e : ∀ k, J ((r ≫ (tact i).left) ≫ f ≫ φ k) = J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k) :=
    fun k => by rw [Category.assoc, Category.assoc, reassoc_of% hf]
  rw [funext e] at m'
  rw [val_of _ (r ≫ (tact i).left) z J _ e]
  obtain ⟨n, v⟩ := hv Z _ z _ m
  obtain ⟨n', v'⟩ := hv Z _ z _ m'
  refine v'.trans (Eq.trans ?_ (congrArg _ v).symm)
  let Z' : Over S := Over.mk (r ≫ (splitTorus S X ⊗ G).hom)
  let ρ : Z' ⟶ splitTorus S X ⊗ G := Over.homMk r rfl
  have k := WtBundle.gm_of_isWt (hw fun _ => fun k => J ((r ≫ (snd (splitTorus S X) G).left) ≫ f ≫ φ k))
    (ρ ≫ fst _ _) (ρ ≫ snd _ _) z (by rw [← comp_tact]; exact n') n
  rw [← comp_tact, ← gm_charUnit] at k
  exact k

variable (Q : TQ G X)

theorem tact_q : tact Q.i ≫ Q.q = snd _ _ ≫ Q.q := WtBundle.act_comp Q (fst _ _) (snd _ _)

theorem exists_const (hG : GlobalFnsSt) (f : Γ(G.left, ⊤))
    (hf : (tact Q.i).left.appTop.hom f = (snd (splitTorus S X) G).left.appTop.hom f) :
    ∃ c, G.hom.appTop.hom c = f := by
  have := Q.q_affine
  obtain ⟨b, hb⟩ := (invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat
    Q.q_surj inferInstance Q.isKernel ⊤).2.2 f (fun Z t g h₁ h₂ => by
      have e₁ : (t ≫ Q.i) * g = lift t g ≫ tact Q.i := by
        rw [comp_tact, lift_fst, lift_snd]
      have key : ((t ≫ Q.i) * g).left.appTop.hom f = g.left.appTop.hom f := by
        rw [e₁, Over.comp_left, FunDescent.comp_appTop_apply, hf, ← FunDescent.comp_appTop_apply,
          ← Over.comp_left, lift_snd]
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.app_eq_appLE] at key
      exact key)
  obtain ⟨c, hc⟩ := (hG S Q.B Q.isAb).2 b
  refine ⟨c, ?_⟩
  rw [← Over.w Q.q, FunDescent.comp_appTop_apply, hc]
  exact hb

end

theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  let e : G' ≅ (Over.pullback f).obj G := Over.isoMk h.1.isoPullback h.1.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom f = F := h.1.isoPullback_hom_fst
  refine ⟨e, isMonHom_of_mul _ fun T x y => ?_, he⟩
  have h₁ := h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have h₂ := (isGrpPullback_pullback G f).2 T (x ≫ e.hom) (y ≫ e.hom) (pushPt h.1.w x) (pushPt h.1.w y)
    (by rw [Over.comp_left, Category.assoc, he]; rfl) (by rw [Over.comp_left, Category.assoc, he]; rfl)
  refine Over.OverMorphism.ext ((isGrpPullback_pullback G f).1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  rw [← h₂, h₁, Over.comp_left, Category.assoc, he]

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_transl {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 2, h (p.left ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ^
      (![-1, 1] : Fin 2 → ℤ) k = (h ((toUnit T ≫ D.c χ) * p).left)⁻¹ * h p.left := by
  have e : p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A) = (toUnit T ≫ D.c χ) * p := by
    rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  rw [Fin.prod_univ_two, ← e]
  show h (p ≫ ((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A)).left ^ (-1 : ℤ) * h (p.left ≫ 𝟙 _) ^ (1 : ℤ) = _
  rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]

theorem exists_four {T : Over (Spec (CommRingCat.of R))} (q : T ⟶ D.P.A) (σ : T ⟶ T) (hσ : σ ≫ q = 1) (χ : D.X)
    (f : T.left ⟶ D.P.A.left) (hf : q.left = f)
    (t₀ : LB.Gen (LB.LinComb D.P.L (K := Fin 2)
      (fun k => f ≫ ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] k) ![-1, 1])) (g₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (D.Oφ q χ) Oinvε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val t₀ r z J * (val t₀ (r ≫ σ.left) z J)⁻¹ := by
  subst hf
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := D.Oφ q χ) (ε' := Oinvε) (fun U _ h => by
      have a := prod_transl D (σ ≫ q) χ h
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_transl D q χ h) (DVR.prod_neg _ _
          ((Finset.prod_congr rfl fun k _ =>
            congrArg (fun g => h g ^ (![-1, 1] : Fin 2 → ℤ) k) (Category.assoc _ _ _).symm).trans a))) ?_
      rw [prod_Oφ, hσ, _root_.mul_one, mul_comm q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t₀ (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t₀ σ.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ g₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ g₀ _)))
  exact ⟨t, ht, fun Z r z J hJ => by rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ]⟩

end

end GlobalTheory.QuotCoord

namespace GlobalTheory

open WeightGen QuotCoord

theorem exists_gtCoord_of_torusQuotient : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (Q : TQ (thickObj R I e G) D.X) (b : Q.B.left ⟶ D.P.A.left), IsGrpPullback Q.B D.P.A (thick R I e) b → (∀ χ, ∃ u : LB.Gen ((LB.LinComb D.P.L (K := Fin 2) ![((toUnit D.P.A ≫ D.c χ) * 𝟙 D.P.A).left, 𝟙 D.P.A.left] ![-1, 1]).pull (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) → ∃ g : GtCoord I D e G, g.i = Q.i ∧ g.pG.left = Q.q.left ≫ b := by
  intro hG R _ _ _ I D e G _ _ Q b hb hu
  obtain ⟨β, hβ, hβb⟩ : ∃ β : Q.B ≅ thickObj R I e D.P.A, IsMonHom β.hom ∧
    β.hom.left ≫ pullback.fst D.P.A.hom (thick R I e) = b := exists_iso_pullback hb
  have hL := D.P.isLB
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  let F := Over.map (thick R I e)
  have hp : (F.map (Q.q ≫ β.hom) ≫ D.prBe I e).left = Q.q.left ≫ b := by
    rw [← hβb, ← Category.assoc]
    rfl
  have unit_q : F.map η[thickObj R I e G] ≫ F.map (Q.q ≫ β.hom) ≫ D.prBe I e = 1 := by
    rw [← F.map_comp_assoc, IsMonHom.one_hom]
    exact Over.OverMorphism.ext (unit_fst (thick R I e) D.P.A)
  have hπ : F.map (tact Q.i) ≫ F.map (toUnit _) = F.map (snd _ _) ≫ F.map (toUnit _) := by
    rw [← F.map_comp, ← F.map_comp, comp_toUnit, comp_toUnit]
  obtain ⟨t, g, m, u, w⟩ := exists_normalised D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
    (F.map (toUnit _)) (F.map η[thickObj R I e G])
    (by rw [← F.map_comp, comp_toUnit, toUnit_unit, F.map_id]) unit_q
    (F.map (tact Q.i)) (F.map (snd _ _))
    (by rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Category.assoc (tact Q.i), tact_q Q,
      Category.assoc])
    hπ (QuotCoord.exists_const Q hG) (fun χ => wt D.X (thickObj R I e G) χ)
    (fun χ χ' Z r z => wt_add _ _ _ _ Z r z)
    (fun χ => by
      obtain ⟨u, gu, wu⟩ := hu χ
      obtain ⟨t₀, g₀, w₀⟩ := exists_wt_gen Q.i (Q.q.left ≫ b) (by
        rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, tact_q]) χ u gu wu
      obtain ⟨t, g, v⟩ := exists_four D (F.map (Q.q ≫ β.hom) ≫ D.prBe I e)
        (F.map (toUnit _) ≫ F.map η[thickObj R I e G])
        (by rw [Category.assoc, unit_q, MonObj.comp_one]) χ _ hp t₀ g₀
      refine ⟨t, g, fun Z r z J hJ => ?_⟩
      have k : (F.map (tact Q.i)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left =
          (F.map (snd _ _)).left ≫ (F.map (toUnit _) ≫ F.map η[thickObj R I e G]).left :=
        congrArg (fun g => g.left) (show F.map (tact Q.i) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] =
          F.map (snd _ _) ≫ F.map (toUnit _) ≫ F.map η[thickObj R I e G] by rw [reassoc_of% hπ])
      rw [v _ _ z J hJ, v _ _ z J hJ, Category.assoc, Category.assoc, k, ← _root_.mul_assoc]
      exact congrArg (· * _) (w₀ Z r z J hJ))
  refine ⟨{ q := Q.q ≫ β.hom
            q_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surj := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            i := Q.i
            i_hom := inferInstance
            isKernel := Q.isKernel.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) β (by simp)
              (toUnit_unique _ _) (by simp) (by simp)
            t := t
            t_gen := g
            t_mul := m
            t_unit := fun χ => corr_of_val hL fun y J hJ => ?_
            t_weight := fun χ => corr_of_val hL fun y J hJ => ?_ }, rfl, hp⟩
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact u χ y J hJ
  · exact (val_pull hJ _ _ _).trans ((w χ _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)

end GlobalTheory
