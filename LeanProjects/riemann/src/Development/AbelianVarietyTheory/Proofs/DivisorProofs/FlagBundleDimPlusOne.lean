import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open Limits GlobalTheory.QCoh

namespace GlobalTheory.FlagLineDim

theorem exists_local_section (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules)
    (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a))
    (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a)) (hfl : IsFlagBundle π E r fl) (b : B) :
    ∃ (V : B.Opens) (g : V.toScheme ⟶ Y), b ∈ V ∧ g ≫ π = V.ι := by
  choose U e hb he using fun a => hE a b
  let V : B.Opens := Finset.univ.inf U
  have hle : ∀ a, V ≤ U a := fun a => Finset.inf_le (Finset.mem_univ a)
  have hbV : b ∈ V := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using hb
  have hfr (a : ι) := (isFrame_restrict_iff V.ι _).2 ((he a).res ((V.ι_image_le ⊤).trans (hle a)))
  let φ : ∀ a, freeModule V.toScheme (Fin (r a)) ≅ (Scheme.Modules.pullback V.ι).obj (E a) := fun a =>
    (isFrame_freeFrame _ _).iso (hfr a) ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (E a)
  obtain ⟨g', ⟨w, -⟩, -⟩ := hfl V.toScheme V.ι (fun a => (GlobalTheory.FlagSurj.freeFlag V.toScheme (r a)).ofIso (φ a))
  exact ⟨V, g', hbV, w⟩

theorem isLocallyNoetherian_base (B Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : Y ⟶ B) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a))
    (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a)) (hfl : IsFlagBundle π E r fl) : IsLocallyNoetherian B := by
  choose V g hbV hg using exists_local_section B Y π ι E r fl hE hfl
  let S : {U : B.affineOpens // ∃ b, (U : B.Opens) ≤ V b} → B.affineOpens := fun U => U.1
  refine isLocallyNoetherian_of_affine_cover (S := S) ?_ ?_
  · refine top_le_iff.1 fun b _ => ?_
    obtain ⟨U, hU, hbU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp B.isBasis_affineOpens (hbV b)
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨⟨U, hU⟩, b, hUV⟩, hbU⟩
  · rintro ⟨U, b, hUV⟩
    let s : (U : B.Opens).toScheme ⟶ Y := B.homOfLE hUV ≫ g b
    have hs : s ≫ π = (U : B.Opens).ι := by
      simp only [s, Category.assoc, hg, Scheme.homOfLE_ι]
    haveI : LocallyOfFiniteType (s ≫ π) := by rw [hs]; infer_instance
    haveI : LocallyOfFiniteType s := locallyOfFiniteType_of_comp s π
    haveI : IsLocallyNoetherian (U : B.Opens).toScheme := LocallyOfFiniteType.isLocallyNoetherian s
    haveI : IsAffine (U : B.Opens).toScheme := U.2
    have := IsLocallyNoetherian.component_noetherian (X := (U : B.Opens).toScheme) ⟨⊤, isAffineOpen_top _⟩
    exact isNoetherianRing_of_ringEquiv _ ((U : B.Opens).topIso).commRingCatIsoToRingEquiv

theorem iSup_add_one_le {ι : Type} [Nonempty ι] (f : ι → WithBot ℕ∞) (hf : ∀ i, f i ≠ ⊥) (c : WithBot ℕ∞)
    (h : ∀ i, f i + 1 ≤ c) : (⨆ i, f i) + 1 ≤ c := by
  choose g hg using fun i => WithBot.ne_bot_iff_exists.mp (hf i)
  obtain rfl : f = fun i => ((g i : ℕ∞) : WithBot ℕ∞) := funext fun i => (hg i).symm
  rw [← WithBot.coe_iSup (OrderTop.bddAbove _), ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add,
    WithBot.coe_iSup (OrderTop.bddAbove _)]
  exact iSup_le fun i => by simpa using h i

end GlobalTheory.FlagLineDim

namespace GlobalTheory.FlagLineDim

theorem topologicalKrullDim_eq_add_one : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (Y Y₁ : Scheme.{0}) (p : Y ⟶ Sp k) (ρ : Y ⟶ Y₁) (E₁ : Y₁.Modules)
    (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2), IsProjOver p → GlobalTheory.VB.IsVB E₁ 2 →
    IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) → topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 := by
  intro k _ _ Y Y₁ p ρ E₁ fl₁ hp hE hfl
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian Y₁ := isLocallyNoetherian_base Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁)
    (fun _ => hE) hfl
  have hsm := GlobalTheory.T.flag_bundle_smooth_relative_dimension Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁) (fun _ => hE) hfl
  have h1 : (∑ _a : Unit, 2 * (2 - 1) / 2) = 1 := by decide
  rw [h1] at hsm
  haveI : SmoothOfRelativeDimension 1 ρ := hsm
  haveI : Smooth ρ := SmoothOfRelativeDimension.smooth 1 ρ
  have hsurj := GlobalTheory.FlagSurj.isFlagBundle_surjective Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁)
    (fun _ => hE) hfl
  rw [GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk, GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]
  simp_rw [GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_eq_add Y₁ Y ρ]
  rcases isEmpty_or_nonempty Y₁ with hY₁ | hY₁
  · haveI : IsEmpty Y := ⟨fun y => hY₁.false (ρ y)⟩
    simp [iSup_of_empty]
  apply le_antisymm
  · refine iSup_le fun y => add_le_add (le_iSup (fun b : Y₁ => ringKrullDim (Y₁.presheaf.stalk b)) (ρ y)) ?_
    simpa using GlobalTheory.SmoothDimTotal.fib_le Y₁ Y ρ 1 y
  · refine iSup_add_one_le _ (fun b => ?_) _ fun b => ?_
    · exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
    · obtain ⟨y₀, rfl⟩ := hsurj b
      obtain ⟨y, hy, hge⟩ := GlobalTheory.SmoothDimTotal.fib_ge Y₁ Y ρ 1 y₀
      rw [← hy]
      exact le_iSup_of_le y (add_le_add le_rfl (by simpa using hge))

end GlobalTheory.FlagLineDim
