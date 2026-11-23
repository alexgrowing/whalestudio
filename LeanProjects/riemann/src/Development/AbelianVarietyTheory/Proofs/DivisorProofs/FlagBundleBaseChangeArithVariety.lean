import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTotalSpaceIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackBaseChangeStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.LineBundleBaseChange

theorem residueDegree_fst_ne_zero {X Y₁ Y₂ : Scheme.{0}} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (z : ↥(pullback f g))
    (h : g.residueDegree (pullback.snd f g z) ≠ 0) : (pullback.fst f g).residueDegree z ≠ 0 := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  have hg : ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite :=
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite g _).1 h).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hy).inv).2)
  have hl : T.tensorInl.hom.Finite :=
    RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg
  let s : PrimeSpectrum T.tensor := Scheme.Pullback.SpecOfPoint z
  have hs : T.SpecTensorTo s = z := Scheme.Pullback.SpecTensorTo_SpecOfPoint z
  have hm : s.asIdeal.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' T.tensorInl.hom hl.to_isIntegral s.asIdeal ?_
    have hp : (s.asIdeal.comap T.tensorInl.hom).IsPrime := inferInstance
    rw [Ideal.eq_bot_of_prime (s.asIdeal.comap T.tensorInl.hom)]
    exact Ideal.bot_isMaximal
  letI := Ideal.Quotient.field s.asIdeal
  let ρ : T.tensor ⟶ CommRingCat.of (T.tensor ⧸ s.asIdeal) := CommRingCat.ofHom (Ideal.Quotient.mk s.asIdeal)
  have hρ : ρ.hom.Finite := RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  let q : Spec (CommRingCat.of (T.tensor ⧸ s.asIdeal)) := (⊥ : PrimeSpectrum (T.tensor ⧸ s.asIdeal))
  have hq : Spec.map ρ q = s := PrimeSpectrum.ext Ideal.mk_ker
  have e : (Spec.map ρ ≫ T.SpecTensorTo) q = z := by
    rw [Scheme.Hom.comp_apply, hq, hs]
  rw [← e]
  refine PullbackFinitePoint.residueDegree_ne_zero_of_fieldPoint _ _ T.x (T.tensorInl ≫ ρ) (hρ.comp hl) ?_ q
  rw [Category.assoc, T.specTensorTo_fst, Spec.map_comp, Category.assoc]

theorem map_genericPoint_of_mem {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) : f (genericPoint X) = genericPoint Y :=
  ((h ▸ (genericPoint_specializes x).map f.continuous : f (genericPoint X) ⤳ genericPoint Y).antisymm
    (genericPoint_specializes _)).eq

theorem main : ∀ (k : Type) [CommRing k] (B Y B' : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsIntegral B']
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p)
    (E : B.Modules), GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ g : B' ⟶ B, IsArithVar (g ≫ q) d →
    g (genericPoint B') = genericPoint B → g.residueDegree (genericPoint B') ≠ 0 →
    ∃ (_ : IsIntegral (pullback π g : Scheme.{0})), IsArithVar (pullback.fst π g ≫ p) (d + 1) ∧
      pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y ∧
      (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0 := by
  intro k _ B Y B' _ _ _ q p d hq hp π w E hE fl hfl g hg hgen hdeg
  subst w
  have := hg.isLocallyNoetherian
  have hfl' := GlobalTheory.T.flag_bundle_pullback_base_change B Y B' π g Unit (fun _ => E) (fun _ => 2) (fun _ => fl) hfl
  have hE' : ∀ _ : Unit, GlobalTheory.VB.IsVB ((Scheme.Modules.pullback g).obj E) 2 := fun _ => hE.pullback g
  have hsm : SmoothOfRelativeDimension 1 (pullback.snd π g) := by
    simpa using GlobalTheory.T.flag_bundle_smooth_relative_dimension B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have hs' := GlobalTheory.T.flag_bundle_projection_surjective B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have hs := GlobalTheory.T.flag_bundle_projection_surjective B Y π Unit _ _ _ (fun _ => hE) hfl
  have := GlobalTheory.T.flag_bundle_total_space_irreducible B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have := SmoothOfRelativeDimension.smooth 1 (pullback.snd π g)
  have := GlobalTheory.geometricallyReduced_of_smooth (pullback.snd π g)
  have := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd π g)
  have hI : IsIntegral (pullback π g : Scheme.{0}) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hπ : π (genericPoint Y) = genericPoint B := by
    obtain ⟨y, hy⟩ := hs (genericPoint B)
    exact map_genericPoint_of_mem π y hy
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := g) _ _ (hπ.trans hgen.symm)
  refine ⟨hI, ⟨hq.isDomain, hq.finite, hI, ?_, ?_, ?_⟩, map_genericPoint_of_mem _ z hz₁,
    residueDegree_fst_ne_zero π g _ ?_⟩
  · have : IsSeparated q := by
      obtain ⟨N, j, _, rfl⟩ := hq.isProjOver
      have := isProper_str k N
      infer_instance
    have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc π g q)
      (ProjSpace.isProjOver_pullback hp.isProjOver hg.isProjOver)
    rwa [pullback.lift_fst_assoc, Category.comp_id] at h
  · rw [← Category.assoc (pullback.fst π g), pullback.condition, Category.assoc (pullback.snd π g),
      Category.assoc (pullback.snd π g)]
    have := hg.flat
    infer_instance
  · exact GlobalTheory.T.krull_dim_smooth_surjective_total B' _ (pullback.snd π g) 1 d hs' hg.dim_eq
  · rw [map_genericPoint_of_mem _ z hz₂]
    exact hdeg

end GlobalTheory.LineBundleBaseChange

end
