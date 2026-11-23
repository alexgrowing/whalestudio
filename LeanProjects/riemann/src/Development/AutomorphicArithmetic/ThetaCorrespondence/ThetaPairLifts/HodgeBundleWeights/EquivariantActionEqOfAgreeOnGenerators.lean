import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismIntegralMap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.InteriorEquivariantActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismIntegralMapStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvAct
theorem equivariant_action_ext : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA1 Γ _ ι ρ hact X' _ φ ℓ ρ' hN hproj hℓ hℓφ hρ
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨n, hn, hη⟩ := _root_.GlobalTheory.T.interior_equivariant_action_invariant hP E H Dw l Xo c TF Z hpq hA Γ ι ρ (GlobalTheory.T.interiorLevelAction_eq_restriction_levelMove_inv E H Dw l Xo c TF Z hpq hA Γ ι ρ hact)
  haveI := hℓ
  haveI : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isProjOver hproj
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' := (isNormalScheme_iff_pred X').mp hN
  have hne : Nonempty (V₀ TF.Y Z) :=
    ⟨⟨genPt Z, (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)⟩⟩
  haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG' : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian (pullG TF Z φ) :=
    IsSemiAbelian.pullback _ _ TF.Y.t.semi
  have hcomp : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
    rw [← Category.assoc, hℓφ]
  have hκ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (φ ≫ (barComp TF.Y Z).ι) ℓ
    ((isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr hcomp rfl)
  obtain ⟨κ, hκ, hκψ⟩ : ∃ κ : (pullG TF Z (j₀ TF.Y Z)).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z (j₀ TF.Y Z)) (pullG TF Z φ) ℓ κ ∧ κ ≫ pullψ TF Z φ = pullψ TF Z (j₀ TF.Y Z) :=
    ⟨_, hκ, pullback.lift_fst _ _ _⟩
  have hκw : κ ≫ (pullG TF Z φ).hom = (pullG TF Z (j₀ TF.Y Z)).hom ≫ ℓ := hκ.1.w
  have hM : ∀ γ, ∃ M : (pullG TF Z φ).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z φ) (pullG TF Z φ) (ρ' γ).hom M ∧ κ ≫ M = n γ ≫ κ := fun γ =>
    exists_isGrpPullback_extend hP.p22 X' (V₀ TF.Y Z) hS ℓ (ρ γ).hom (ρ' γ).hom (hρ γ) (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
      (n γ) (hn.1 γ)
  choose m hm hmκ using hM
  have huniq := eq_of_comp_eq_of_isGrpPullback hS ℓ (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
  have hact' : ∀ a : 𝓞 E, κ ≫ ((pullAct TF Z φ).act a).left = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
    intro a
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ) = _ ≫ (κ ≫ pullψ TF Z φ)
      rw [pullAct_pullψ, ← Category.assoc, hκψ, pullAct_pullψ]
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ (pullG TF Z φ).hom) = _ ≫ (κ ≫ (pullG TF Z φ).hom)
      rw [Over.w, hκw, ← Category.assoc, Over.w]
  refine ⟨m, ⟨hm, fun γ a => ?_, fun γ₁ γ₂ => ?_⟩, ?_⟩
  · refine huniq _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, (hm γ).1.w, ← Category.assoc, Over.w]
    · calc κ ≫ ((pullAct TF Z φ).act a).left ≫ m γ
          = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ ≫ m γ := by rw [← Category.assoc, hact', Category.assoc]
        _ = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ n γ ≫ κ := by rw [hmκ]
        _ = n γ ≫ ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
          rw [← Category.assoc, hn.2.1 γ a, Category.assoc]
        _ = n γ ≫ κ ≫ ((pullAct TF Z φ).act a).left := by rw [hact']
        _ = κ ≫ m γ ≫ ((pullAct TF Z φ).act a).left := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · refine huniq _ _ ?_ ?_
    · rw [(hm _).1.w, Category.assoc, (hm γ₁).1.w, ← Category.assoc, (hm γ₂).1.w, Category.assoc, map_mul,
        Aut.Aut_mul_def]
      rfl
    · calc κ ≫ m (γ₁ * γ₂) = n (γ₁ * γ₂) ≫ κ := hmκ _
        _ = n γ₂ ≫ n γ₁ ≫ κ := by rw [hn.2.2, Category.assoc]
        _ = n γ₂ ≫ κ ≫ m γ₁ := by rw [hmκ]
        _ = κ ≫ m γ₂ ≫ m γ₁ := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · intro γ a b hab w w' hw hw' hwb hwa
    have lift : ∀ v : V₀ TF.Y Z ⟶ (pullG TF Z φ).left, v ≫ (pullG TF Z φ).hom = ℓ →
        ∃ u : V₀ TF.Y Z ⟶ (pullG TF Z (j₀ TF.Y Z)).left, u ≫ (pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _ ∧
          u ≫ pullψ TF Z (j₀ TF.Y Z) = v ≫ pullψ TF Z φ ∧ u ≫ κ = v := by
      intro v hv
      have e : (v ≫ pullψ TF Z φ) ≫ TF.Y.t.G.hom = 𝟙 _ ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (v ≫ (pullG TF Z φ).hom) ≫ _ = _
        rw [hv, Category.id_comp, hcomp]
      refine ⟨pullback.lift _ _ e, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc]
        change _ ≫ (κ ≫ pullψ TF Z φ) = v ≫ pullψ TF Z φ
        rw [hκψ]; exact pullback.lift_fst _ _ _
      · rw [Category.assoc]
        change _ ≫ (κ ≫ (pullG TF Z φ).hom) = v ≫ (pullG TF Z φ).hom
        rw [hκw, ← Category.assoc]
        change (pullback.lift _ _ e ≫ pullback.snd _ _) ≫ ℓ = _
        rw [pullback.lift_snd, Category.id_comp, hv]
    obtain ⟨u, hu1, hu2, hu3⟩ := lift w hw
    obtain ⟨u', hu1', hu2', hu3'⟩ := lift w' hw'
    have := hη γ a b hab u u' hu1 hu1' (by rw [hu2, hwb]) (by rw [hu2', hwa])
    rw [← hu3, ← hu3', Category.assoc, hmκ, ← Category.assoc, this, Category.assoc]
end GlobalTheory.EqvAct
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_action_eq_of_agree_on_generators : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  first | exact @_root_.GlobalTheory.EqvAct.equivariant_action_ext | exact _root_.GlobalTheory.EqvAct.equivariant_action_ext | (intros; apply _root_.GlobalTheory.EqvAct.equivariant_action_ext <;> assumption)
end
