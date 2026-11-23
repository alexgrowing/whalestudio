import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmooth
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem bij_stalkMap {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    Function.Bijective (φ.stalkMap x).hom := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

private theorem isIntegral_of_flat {G X : Scheme.{0}} (φ : G ⟶ X) [Flat φ] [IsPreimmersion φ] [IsIntegral X]
    [Nonempty G] : IsIntegral G := by
  have hd (x : G) : IsDomain (G.presheaf.stalk x) :=
    (RingEquiv.ofBijective _ (bij_stalkMap φ x)).symm.toMulEquiv.isDomain _
  have hr (x : G) : _root_.IsReduced (G.presheaf.stalk x) := inferInstance
  have : IsReduced G := isReduced_of_isReduced_stalk G
  obtain ⟨g⟩ := ‹Nonempty G›
  obtain ⟨η, -, hη⟩ := Flat.generalizingMap φ (genericPoint_specializes (φ g))
  have hs (x : G) : η ⤳ x := by
    rw [← φ.isEmbedding.isInducing.specializes_iff, hη]
    exact genericPoint_specializes _
  have hc : closure ({η} : Set G) = Set.univ :=
    Set.eq_univ_of_forall fun x => specializes_iff_mem_closure.1 (hs x)
  have hi : IsIrreducible (Set.univ : Set G) := hc ▸ isIrreducible_singleton.closure
  have : PreirreducibleSpace G := ⟨hi.2⟩
  have : IrreducibleSpace G := ⟨⟨g⟩⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced G

theorem UpperTheory.isPullback_of_unique_points :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (X : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)) (d : ℕ), IsArithVar p d → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ j : Y.X ⟶ X, j ≫ p = Y.str ≫ spMap (algebraMap (𝓞 F) F) → (∀ (K : Type) [Field K] [IsAlgClosed K] (q : Sp K ⟶ X) (ψ : F →+* K), q ≫ p = spMap ψ ≫ spMap (algebraMap (𝓞 F) F) → ∃! y : Sp K ⟶ Y.X, y ≫ j = q) → IsPullback j Y.str p (spMap (algebraMap (𝓞 F) F)) := by
  intro F _ _ Y X p d ar hN j hj hb
  have := ar.isIntegral
  have hpre : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have hfl : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  set s := spMap (algebraMap (𝓞 F) F) with hs
  have hP : IsProper p := by
    obtain ⟨N, i, _, hi⟩ := ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← hi]
    infer_instance
  let f : Y.X ⟶ Limits.pullback p s := Limits.pullback.lift j Y.str hj
  have hf1 : f ≫ Limits.pullback.fst p s = j := Limits.pullback.lift_fst _ _ _
  have hf2 : f ≫ Limits.pullback.snd p s = Y.str := Limits.pullback.lift_snd _ _ _
  have : IsPreimmersion (Limits.pullback.fst p s) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback p s).flip hpre
  have : Flat (Limits.pullback.fst p s) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback p s).flip hfl
  have : Nonempty (Limits.pullback p s : Scheme.{0}) := ⟨f (genericPoint Y.X)⟩
  have : IsIntegral (Limits.pullback p s) := isIntegral_of_flat (Limits.pullback.fst p s)
  have : IsProper (f ≫ Limits.pullback.snd p s) := by rw [hf2]; infer_instance
  have : IsProper f := IsProper.of_comp f (Limits.pullback.snd p s)
  have : IsIso f := by
    refine GlobalTheory.FlagSmooth.isIso_of_bijective_geomPts F _ _ f (Limits.pullback.snd p s) inferInstance inferInstance
      inferInstance (fun t => ?_) (fun Ω _ _ t => ?_)
    · have := (hN (Limits.pullback.fst p s t)).2
      exact IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective _ (bij_stalkMap (Limits.pullback.fst p s) t))
    · obtain ⟨y, hy, hu⟩ := hb Ω (t ≫ Limits.pullback.fst p s) (Spec.preimage (t ≫ Limits.pullback.snd p s)).hom (by
        have e : spMap (Spec.preimage (t ≫ Limits.pullback.snd p s)).hom = t ≫ Limits.pullback.snd p s :=
          Spec.map_preimage _
        rw [e, Category.assoc, Category.assoc, Limits.pullback.condition])
      refine ⟨y, ?_, fun y' hy' => hu y' ?_⟩
      · show y ≫ f = t
        rw [← cancel_mono (Limits.pullback.fst p s), Category.assoc, hf1, hy]
      · show y' ≫ j = _
        rw [← hf1, ← Category.assoc, hy']
  exact IsPullback.of_iso_pullback ⟨hj⟩ (asIso f) hf1 hf2
