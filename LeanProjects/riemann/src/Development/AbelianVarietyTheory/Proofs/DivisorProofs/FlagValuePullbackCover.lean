import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingEverywhereOfRegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCoverGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricGrLBPullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackPieceIsoFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniqueUpToIso

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

namespace GlobalTheory.FlagCoverVal

theorem exists_isIso_compat {B Y Y' : Scheme.{0}} {π : Y ⟶ B} {π' : Y' ⟶ B} {ι : Type} {E : ι → B.Modules} {r : ι → ℕ}
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)}
    {fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)} (hπ : IsFlagBundle π E r fl)
    (hπ' : IsFlagBundle π' E r fl') : ∃ (u : Y ⟶ Y') (w : u ≫ π' = π), IsIso u ∧
      ∀ a i, ∃ e : (Scheme.Modules.pullback u).obj ((fl' a).F i) ≅ (fl a).F i,
        e.hom ≫ (fl a).ι i = (Scheme.Modules.pullback u).map ((fl' a).ι i) ≫
          (Scheme.Modules.pullbackComp u π').hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a) := by
  obtain ⟨u, ⟨wu, cu⟩, -⟩ := hπ' Y π fl
  obtain ⟨v, ⟨wv, cv⟩, -⟩ := hπ Y' π' fl'
  have huv : u ≫ v = 𝟙 Y := by
    obtain ⟨z, -, hz⟩ := hπ Y π fl
    have w₃ : (u ≫ v) ≫ π = π := by rw [Category.assoc, wv, wu]
    exact (hz _ ⟨w₃, flagCompat_comp π fl π' fl' v wv cv π fl u wu cu w₃⟩).trans
      (hz _ ⟨Category.id_comp π, flagCompat_id π fl _⟩).symm
  have hvu : v ≫ u = 𝟙 Y' := by
    obtain ⟨z, -, hz⟩ := hπ' Y' π' fl'
    have w₃ : (v ≫ u) ≫ π' = π' := by rw [Category.assoc, wu, wv]
    exact (hz _ ⟨w₃, flagCompat_comp π' fl' π fl u wu cu π' fl' v wv cv w₃⟩).trans
      (hz _ ⟨Category.id_comp π', flagCompat_id π' fl' _⟩).symm
  exact ⟨u, wu, ⟨v, huv, hvu⟩, cu⟩

theorem eq_genericPoint_of_isTop {X : Scheme.{0}} [IsIntegral X] {E : X.Modules} {r : ℕ} (F : FlagSp E r)
    [IsIntegral F.Y] {y : F.Y} (hy : F.IsTop (genericPoint X) y) : y = genericPoint F.Y :=
  GenericBaseChange.eq_genericPoint_of_specializes
    (hy.2 _ (LineBundleBaseChange.map_genericPoint_of_mem F.π y hy.1))

theorem residueDegree_fst {X Y S : Scheme.{0}} [IsIntegral Y] (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral (Limits.pullback f g)]
    (h : Limits.pullback.snd f g (genericPoint (Limits.pullback f g : Scheme.{0})) = genericPoint Y)
    (hg : g.residueDegree (genericPoint Y) ≠ 0) :
    (Limits.pullback.fst f g).residueDegree (genericPoint (Limits.pullback f g : Scheme.{0})) =
      g.residueDegree (genericPoint Y) := by
  have hF := GlobalTheory.T.generic_point_pullback_residue_field GlobalTheory.T.isField_of_unique_prime_stalk f g (GlobalTheory.T.spec_tensor_preimmersion _ _ _) (h ▸ hg)
  rw [GlobalTheory.T.residue_degree_fst_eq_finrank f g _ hF, GlobalTheory.T.finrank_tensor_residue_degree]
  change g.residueDegree (Limits.pullback.snd f g (genericPoint _)) = _
  rw [h]

theorem isVal_pull : ArCalc → ∀ (k : Type) [CommRing k] (B₀ B : Scheme.{0}) [IsIntegral B₀] [IsIntegral B] (q₀ : B₀ ⟶ Sp k) (q : B ⟶ Sp k) (e : ℕ), IsArithVar q₀ (e + 1) → ∀ (β : B ⟶ B₀) (w : β ≫ q₀ = q), FlagChain.IsCov q₀ (e + 1) β → ∀ (L : B₀.Modules) (g : ℕ) (h : VMetric q₀ L g) (H : h.IsCInf) (F₀ : FlagSp L g) (F₁ : FlagSp ((Scheme.Modules.pullback β).obj L) g) (N : HermLB q₀) (a : ℝ), F₀.IsVal H N (genericPoint B₀) e a → F₁.IsVal (H.pull β w) (N.pull β w) (genericPoint B) e ((β.residueDegree (genericPoint B) : ℝ) * a) := by
  intro hA k _ B₀ B _ _ q₀ q e hq₀ β w hβ L g h H F₀ F₁ N a ⟨y₀, Φ, hy₀, hΦ, ha⟩
  subst w
  have := hq₀.isLocallyNoetherian
  have := hβ.1.isLocallyNoetherian
  have A₀ := ((FlagTop.main k B₀ q₀ _ hq₀ L g h.isVB).2 F₀).1
  obtain ⟨A₁, -, T₁⟩ := (FlagTop.main k B _ _ hβ.1 _ g (h.isVB.pullback β)).2 F₁
  obtain ⟨y₁, hy₁, -⟩ := T₁ (genericPoint B)
  have := A₀.isIntegral
  have := A₁.isIntegral
  obtain rfl := eq_genericPoint_of_isTop F₀ hy₀
  obtain rfl := eq_genericPoint_of_isTop F₁ hy₁
  obtain ⟨_, hc⟩ := Gen.isCov_pullback_fst hq₀ A₀ hβ (fun _ : Unit => h.isVB) F₀.univ
  obtain ⟨u, wu, _, cu⟩ := exists_isIso_compat F₁.univ
    (FlagBaseChange.isFlagBundle_pullFlag B₀ F₀.Y B F₀.π β Unit _ _ _ F₀.univ)
  have hu : u (genericPoint F₁.Y) = genericPoint (Limits.pullback F₀.π β : Scheme.{0}) := by
    obtain ⟨y, hy⟩ := u.homeomorph.surjective (genericPoint _)
    exact LineBundleBaseChange.map_genericPoint_of_mem u y hy
  have du : u.residueDegree (genericPoint F₁.Y) = 1 := GlobalTheory.Published.residueDegree_of_isClosedImmersion u _
  have hs : Limits.pullback.snd F₀.π β (genericPoint (Limits.pullback F₀.π β : Scheme.{0})) = genericPoint B := by
    rw [← hu, ← Scheme.Hom.comp_apply, wu]
    exact hy₁.1
  have w₁ : Limits.pullback.fst F₀.π β ≫ F₀.π ≫ q₀ = Limits.pullback.snd F₀.π β ≫ β ≫ q₀ :=
    Limits.pullback.condition_assoc q₀
  have w₂ : u ≫ Limits.pullback.snd F₀.π β ≫ β ≫ q₀ = F₁.π ≫ β ≫ q₀ := by rw [reassoc_of% wu]
  have e₁ : e + 2 + g.choose 2 = (e + 1 + g.choose 2) + 1 := by omega
  rw [e₁, isHtFun_generic_iff] at hΦ
  have P₁ := (hA.arProj k _ _ _ _ _ A₀ (w₁ ▸ hc.1) _ w₁ hc.2.1 hc.2.2).2 _ _ Φ hΦ
  have P₂ := (hA.arProj k _ _ _ _ _ (w₁ ▸ hc.1) A₁ u w₂ hu (du.trans_ne one_ne_zero)).2 _ _ _ P₁
  have P₃ := ((hA.arIso k _ _ _ A₁).2 _ _ _ P₂).2.1 (F₁.fam (H.pull β rfl) (N.pull β rfl)) (by
    rintro (_ | i)
    · exact ((Gen.isometric_sq Limits.pullback.condition N rfl rfl w₁ rfl).pull u w₂).trans
        ((HermLB.isometric_of_refines (HermLB.refines_pull_pull (N.pull β rfl) _ rfl u w₂ (by rw [wu]))).trans
          (HermLB.isometric_pull_of_eq _ wu _ rfl))
    · exact ((Gen.isometric_grLB_pull_ofIso (H.pull F₀.π rfl) _ w₁
        (Gen.isIsometry_sqIso Limits.pullback.condition h rfl rfl w₁ rfl) F₀.fl i).pull u w₂).trans
        (VMetric.isometric_grLB_of_steps_pull _ _ _ _ _ _ (H.pull β rfl) _ F₁.fl u wu (cu ()) w₂ i).symm)
  refine ⟨_, _, hy₁, by rw [e₁, isHtFun_generic_iff]; exact P₃, ?_⟩
  rw [du, residueDegree_fst _ _ hs hβ.2.2, LinearMap.smul_apply, LinearMap.smul_apply, ha]
  simp

end GlobalTheory.FlagCoverVal

end
