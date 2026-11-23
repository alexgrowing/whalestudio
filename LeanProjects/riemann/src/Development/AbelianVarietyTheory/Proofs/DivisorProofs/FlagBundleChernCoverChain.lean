import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingEverywhereOfRegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniqueUpToIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackPieceIsoFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTensorPreimmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldOfUniquePrimeStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointPullbackResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeFstEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTensorResidueDegree
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.FlagSwitch

open Limits GlobalTheory.TwoLat.Gen

theorem exists_isPullback {B X : Scheme.{0}} {L : B.Modules} {g : ℕ} (F : FlagSp L g) (ρ : X ⟶ B)
    (W : FlagSp ((Scheme.Modules.pullback ρ).obj L) g) : ∃ t : W.Y ⟶ F.Y, IsPullback t W.π F.π ρ ∧
      ∀ {k : Type} [CommRing k] {q : B ⟶ Sp k} {p : X ⟶ Sp k} (w : ρ ≫ q = p) {h : VMetric q L g} (H : h.IsCInf)
        (v : t ≫ F.π ≫ q = W.π ≫ p) (i : Fin g),
        ((VMetric.grLB F.fl i (H.pull F.π rfl)).pull t v).Isometric
          (VMetric.grLB W.fl i ((H.pull ρ w).pull W.π rfl)) := by
  have hπ' := FlagBaseChange.isFlagBundle_pullFlag B F.Y X F.π ρ Unit _ _ _ F.univ
  have hπ := W.univ
  obtain ⟨u, ⟨wu, cu⟩, -⟩ := hπ' W.Y W.π fun _ => W.fl
  obtain ⟨s, ⟨ws, cs⟩, -⟩ := hπ _ (pullback.snd F.π ρ) fun _ => FlagBaseChange.pullFlag F.π ρ F.fl
  have hus : u ≫ s = 𝟙 _ := by
    obtain ⟨z, -, hz⟩ := hπ W.Y W.π fun _ => W.fl
    have w₃ : (u ≫ s) ≫ W.π = W.π := by rw [Category.assoc, ws, wu]
    exact (hz _ ⟨w₃, flagCompat_comp _ _ _ _ s ws cs _ _ u wu cu w₃⟩).trans
      (hz _ ⟨Category.id_comp _, flagCompat_id _ _ _⟩).symm
  have hsu : s ≫ u = 𝟙 _ := by
    obtain ⟨z, -, hz⟩ := hπ' _ (pullback.snd F.π ρ) fun _ => FlagBaseChange.pullFlag F.π ρ F.fl
    have w₃ : (s ≫ u) ≫ pullback.snd F.π ρ = pullback.snd F.π ρ := by rw [Category.assoc, wu, ws]
    exact (hz _ ⟨w₃, flagCompat_comp _ _ _ _ u wu cu _ _ s ws cs w₃⟩).trans
      (hz _ ⟨Category.id_comp _, flagCompat_id _ _ _⟩).symm
  have : IsIso u := ⟨s, hus, hsu⟩
  refine ⟨u ≫ pullback.fst F.π ρ, ?_, ?_⟩
  · exact IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, reassoc_of% wu]⟩ (asIso u) rfl wu
  · intro k _ q p w h H v i
    have w₁ : pullback.fst F.π ρ ≫ F.π ≫ q = pullback.snd F.π ρ ≫ p := by rw [pullback.condition_assoc, w]
    have w₂ : u ≫ pullback.snd F.π ρ ≫ p = W.π ≫ p := by rw [reassoc_of% wu]
    have e₁ := VMetric.isometric_grLB_of_steps_pull p _ W.π _ g _ (H.pull ρ w) _ W.fl u wu (cu ()) w₂ i
    have e₂ := isometric_grLB_pull_ofIso (H.pull F.π rfl) ((H.pull ρ w).pull (pullback.snd F.π ρ) rfl) w₁
      (isIsometry_sqIso pullback.condition h rfl w w₁ rfl) F.fl i
    exact ((HermLB.isometric_of_refines (HermLB.refines_pull_pull _ _ w₁ u w₂ v)).symm.trans
      (e₂.pull u w₂)).trans e₁.symm

theorem generic_of_isPullback {P Z X Y : Scheme.{0}} [IsIntegral P] [IsIntegral Z] [IsIntegral X] [IsIntegral Y]
    {γ : P ⟶ Z} {b : P ⟶ X} {a : Z ⟶ Y} {ρ : X ⟶ Y} (sq : IsPullback γ b a ρ)
    (ha : a (genericPoint Z) = genericPoint Y) (hρ : ρ (genericPoint X) = genericPoint Y)
    (hd : ρ.residueDegree (genericPoint X) ≠ 0) :
    γ (genericPoint P) = genericPoint Z ∧ γ.residueDegree (genericPoint P) = ρ.residueDegree (genericPoint X) := by
  have : IsIntegral (pullback a ρ) := IsIntegral.of_isIso sq.isoPullback.hom
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := ρ) _ _ (ha.trans hρ.symm)
  have h₁ := LineBundleBaseChange.map_genericPoint_of_mem _ z hz₁
  have h₂ := LineBundleBaseChange.map_genericPoint_of_mem _ z hz₂
  have h₃ : sq.isoPullback.hom (genericPoint P) = genericPoint (pullback a ρ : Scheme.{0}) := by
    refine LineBundleBaseChange.map_genericPoint_of_mem _ (sq.isoPullback.inv (genericPoint _)) ?_
    simp
  have hF := GlobalTheory.PullbackGenericTensor.isField_tensor GlobalTheory.isField_of_spec_singleton_stalk_isField a ρ
    (GlobalTheory.isPreimmersion_SpecTensorTo _ _ _) (h₂ ▸ hd)
  rw [← sq.isoPullback_hom_fst]
  refine ⟨by rw [Scheme.Hom.comp_apply, h₃, h₁], ?_⟩
  rw [CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion sq.isoPullback.hom, mul_one, h₃,
    GlobalTheory.FieldTensorDegree.residueDegree_fst_eq_finrank a ρ _ hF, GlobalTheory.ResidueTensorRank.finrank_tensorInl]
  change ρ.residueDegree (pullback.snd a ρ (genericPoint _)) = _
  rw [h₂]

theorem isArithVar_of_isIso {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D)
    (e : Y ⟶ X) [IsIso e] : IsArithVar (e ≫ p) D := by
  have := h.isIntegral
  have := h.flat
  refine ⟨h.isDomain, h.finite, IsIntegral.of_isIso (inv e), ProjSpace.isProjOver_comp_of_isClosedImmersion e h.isProjOver,
    by rw [Category.assoc]; infer_instance, ?_⟩
  rw [← h.dim_eq]
  exact (Scheme.homeoOfIso (asIso e)).isHomeomorph.topologicalKrullDim_eq

theorem main : ∀ (k : Type) [CommRing k] (B Y X : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsIntegral X] (q : B ⟶ Sp k) (π : Y ⟶ B) (ρ : X ⟶ Y) (p : X ⟶ Sp k) (w : ρ ≫ π ≫ q = p) (d D : ℕ), IsArithVar q d → IsArithVar (π ≫ q) D → FlagChain.IsCov (π ≫ q) D ρ → ∀ (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (L : B.Modules) (g : ℕ) (hL : VMetric q L g) (HL : hL.IsCInf) (F : FlagSp L g) (W : FlagSp ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj L)) g) [IsIntegral W.Y], ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (π₂ : Z ⟶ F.Y) (fz : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₂).obj ((Scheme.Modules.pullback F.π).obj (E a))) (r a)) (γ : W.Y ⟶ Z) (v : γ ≫ π₂ ≫ F.π ≫ q = W.π ≫ p), (∀ N : HermLB q, (((N.pull F.π rfl).pull π₂ rfl).pull γ v).Isometric (((N.pull π rfl).pull ρ w).pull W.π rfl)) ∧ IsFlagBundle π₂ (fun a => (Scheme.Modules.pullback F.π).obj (E a)) r fz ∧ IsArithVar (π₂ ≫ F.π ≫ q) (D + g.choose 2) ∧ FlagChain.IsCov (π₂ ≫ F.π ≫ q) (D + g.choose 2) γ ∧ γ.residueDegree (genericPoint W.Y) = ρ.residueDegree (genericPoint X) ∧ (∀ a i, ((VMetric.grLB (fz a) i (((H a).pull F.π rfl).pull π₂ rfl)).pull γ v).Isometric (((VMetric.grLB (fl a) i ((H a).pull π rfl)).pull ρ w).pull W.π rfl)) ∧ (∀ i, (((VMetric.grLB F.fl i (HL.pull F.π rfl)).pull π₂ rfl).pull γ v).Isometric (VMetric.grLB W.fl i (((HL.pull π rfl).pull ρ w).pull W.π rfl))) ∧ ∀ a (N : HermLB (W.π ≫ p)) (n : ℕ), bcPair ((((h a).pull F.π rfl).pull π₂ rfl).pull γ v) ((fz a).pull γ) N n = bcPair ((((h a).pull π rfl).pull ρ w).pull W.π rfl) (((fl a).pull ρ).pull W.π) N n := by
  intro k _ B Y X _ _ _ q π ρ p w d D hq hπ hρ ι _ E r h H fl hfl L g hL HL F W _
  have := hπ.isLocallyNoetherian
  have := hρ.1.isLocallyNoetherian
  let F₁ : FlagSp ((Scheme.Modules.pullback π).obj L) g :=
    ⟨pullback F.π π, pullback.snd F.π π, FlagBaseChange.pullFlag F.π π F.fl,
      FlagBaseChange.isFlagBundle_pullFlag B F.Y Y F.π π Unit _ _ _ F.univ⟩
  obtain ⟨t, sq, ht⟩ := exists_isPullback F₁ ρ W
  let σ := pullbackSymmetry F.π π
  let γ : W.Y ⟶ pullback π F.π := t ≫ σ.hom
  have sq' : IsPullback γ W.π (pullback.fst π F.π) ρ :=
    sq.of_iso (Iso.refl _) σ (Iso.refl _) (Iso.refl _) (by simp [γ]) (by simp) (by simp [σ, F₁]) (by simp)
  have w₁ : pullback.fst π F.π ≫ π ≫ q = pullback.snd π F.π ≫ F.π ≫ q := pullback.condition_assoc q
  have v : γ ≫ pullback.snd π F.π ≫ F.π ≫ q = W.π ≫ p := by rw [← w₁, reassoc_of% sq'.w, w]
  have hZ : IsArithVar (pullback.snd π F.π ≫ F.π ≫ q) (D + g.choose 2) := by
    have := isArithVar_of_isIso ((FlagTop.main k Y _ D hπ _ g (hL.isVB.pullback π)).2 F₁).1 σ.inv
    rwa [← Category.assoc, show σ.inv ≫ F₁.π = pullback.fst π F.π by simp [σ, F₁], w₁] at this
  have hW := ((FlagTop.main k X _ D hρ.1 _ g ((hL.isVB.pullback π).pullback ρ)).2 W).1
  have := hZ.isIntegral
  have ha : pullback.fst π F.π (genericPoint (pullback π F.π : Scheme.{0})) = genericPoint Y := by
    obtain ⟨y, hy⟩ := FlagSurj.isFlagBundle_surjective Y F₁.Y F₁.π Unit _ _ _ (fun _ => hL.isVB.pullback π) F₁.univ
      (genericPoint Y)
    refine LineBundleBaseChange.map_genericPoint_of_mem _ (σ.hom y) ?_
    rw [← Scheme.Hom.comp_apply, ← hy]
    simp [σ, F₁]
  obtain ⟨g₁, g₂⟩ := generic_of_isPullback sq' ha hρ.2.1 hρ.2.2
  refine ⟨pullback π F.π, inferInstance, pullback.snd π F.π, fun a => FlagBaseChange.pullFlag π F.π (fl a), γ, v,
    fun N => ?_, FlagBaseChange.isFlagBundle_pullFlag B Y F.Y π F.π ι E r fl hfl, hZ,
    ⟨by rwa [v, ← w], g₁, g₂ ▸ hρ.2.2⟩, g₂, fun a i => ?_, fun i => ?_, fun a N n => ?_⟩
  · exact ((isometric_sq pullback.condition N rfl rfl w₁ rfl).pull γ v).symm.trans
      (isometric_sq sq'.w _ w₁ w v rfl)
  · exact ((isometric_grLB_pull_ofIso _ _ w₁ (isIsometry_sqIso pullback.condition (h a) rfl rfl w₁ rfl)
      (fl a) i).pull γ v).symm.trans (isometric_sq sq'.w _ w₁ w v rfl)
  · have w₂ : pullback.fst F.π π ≫ F.π ≫ q = pullback.snd F.π π ≫ π ≫ q := pullback.condition_assoc q
    have v₂ : t ≫ F₁.π ≫ π ≫ q = W.π ≫ p := by rw [reassoc_of% sq.w, w]
    have e : γ ≫ pullback.snd π F.π = t ≫ pullback.fst F.π π := by simp [γ, σ]
    exact (isometric_sq e _ rfl w₂ v v₂).trans (((isometric_grLB_pull_ofIso _ _ w₂
      (isIsometry_sqIso pullback.condition hL rfl rfl w₂ rfl) F.fl i).pull t v₂).trans (ht w (HL.pull π rfl) v₂ i))
  · have I := IsometryPullback.isIsometry_trans (IsometryPullback.isIsometry_symm (isIsometry_sqIso sq'.w ((h a).pull π rfl) w₁ w v rfl))
      (IsometryPullback.isIsometry_pull (isIsometry_sqIso pullback.condition (h a) rfl rfl w₁ rfl) γ v)
    refine (bcPair_eq_of_compat ((((H a).pull F.π rfl).pull _ rfl).pull γ v) I (fun i => ?_) N n).symm
    refine ⟨(sqIso sq'.w).inv.app ((fl a).F i), ?_⟩
    change _ ≫ (Scheme.Modules.pullback γ).map ((Scheme.Modules.pullback (pullback.fst π F.π)).map ((fl a).ι i) ≫
        (sqIso pullback.condition).hom.app (E a)) =
      (Scheme.Modules.pullback ρ ⋙ Scheme.Modules.pullback W.π).map ((fl a).ι i) ≫ (sqIso sq'.w).inv.app _ ≫
        (Scheme.Modules.pullback γ).map ((sqIso pullback.condition).hom.app (E a))
    rw [NatTrans.naturality_assoc, Functor.map_comp]
    rfl

end GlobalTheory.FlagSwitch
