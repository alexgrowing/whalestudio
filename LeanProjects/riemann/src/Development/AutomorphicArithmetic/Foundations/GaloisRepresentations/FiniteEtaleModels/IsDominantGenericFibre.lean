import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalOfSmooth
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsOpenImmersionOfSurj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem exists_geomPoint (P : Scheme.{0}) (p : P) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (t : Sp Ω ⟶ P) (q : Sp Ω), t q = p := by
  refine ⟨AlgebraicClosure (P.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (P.residueField p) (AlgebraicClosure (P.residueField p)))) ≫
      P.fromSpecResidueField p, IsLocalRing.closedPoint _, ?_⟩
  change (P.fromSpecResidueField p) ((Spec.map (CommRingCat.ofHom (algebraMap (P.residueField p)
    (AlgebraicClosure (P.residueField p))))) (IsLocalRing.closedPoint _)) = p
  exact Scheme.fromSpecResidueField_apply p _

private theorem isDominant_genericFibre (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap (algebraMap O E))) := by
  refine ⟨fun x => ?_⟩
  let gp : Sp E := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E)
  have hgp : spMap (algebraMap O E) gp ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O) _ _).1 ?_
    show Ideal.comap (algebraMap O E) ⊥ ≤ _
    rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective O E)]
    exact bot_le
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hgp
  refine hx'.mem_closed isClosed_closure (subset_closure ?_)
  rw [Scheme.Pullback.range_fst]
  exact ⟨gp, e.symm⟩

private theorem eq_of_geomPoints {P Y B : Scheme.{0}} [IsReduced P] (a b : P ⟶ Y) (g : Y ⟶ B) [IsSeparated g]
    (hab : a ≫ g = b ≫ g)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ P), t ≫ a = t ≫ b) : a = b := by
  let d : P ⟶ pullback g g := pullback.lift a b hab
  let k₀ : pullback d (pullback.diagonal g) ⟶ P := pullback.fst d (pullback.diagonal g)
  have hd₁ : d ≫ pullback.fst g g = a := pullback.lift_fst _ _ _
  have hd₂ : d ≫ pullback.snd g g = b := pullback.lift_snd _ _ _
  have hc : k₀ ≫ d = pullback.snd d (pullback.diagonal g) ≫ pullback.diagonal g := pullback.condition
  have hk : k₀ ≫ a = k₀ ≫ b := by
    have h1 : k₀ ≫ a = pullback.snd d (pullback.diagonal g) := by
      calc k₀ ≫ a = (k₀ ≫ d) ≫ pullback.fst g g := by rw [Category.assoc, hd₁]
        _ = _ := by rw [hc]; simp
    have h2 : k₀ ≫ b = pullback.snd d (pullback.diagonal g) := by
      calc k₀ ≫ b = (k₀ ≫ d) ≫ pullback.snd g g := by rw [Category.assoc, hd₂]
        _ = _ := by rw [hc]; simp
    rw [h1, h2]
  have hsur : Surjective k₀ := ⟨fun p => by
    obtain ⟨Ω, _, _, t, q, rfl⟩ := exists_geomPoint P p
    have hd : t ≫ d = (t ≫ a) ≫ pullback.diagonal g := by
      apply pullback.hom_ext
      · rw [Category.assoc, hd₁]; simp
      · rw [Category.assoc, hd₂, ← h Ω t]; simp
    refine ⟨(pullback.lift t (t ≫ a) hd : Sp Ω ⟶ _) q, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun m : Sp Ω ⟶ P => m q) (pullback.lift_fst _ _ _)⟩
  have : IsDominant k₀ := inferInstance
  exact ext_of_isDominant_of_isSeparated g hab k₀ hk

theorem UpperTheory.Gal.FiniteEtaleModels.descExt_of :
    NormExt → DescExt := by
  intro hN O E _ _ _ _ _ _ V X Y B s σ j ov hs hfin het hgeo f g y hg hy hker
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsLocalization.Away ϖ E := GlobalTheory.Reg.ChartOpens.away_irreducible hϖ
  have : IsOpenImmersion (spMap (algebraMap O E)) := IsOpenImmersion.of_isLocalization ϖ
  let e : Sp E ⟶ Sp O := spMap (algebraMap O E)
  let u : pullback s e ⟶ X := pullback.fst s e
  let j' : V ⟶ pullback s e := pullback.lift j σ ov
  have hj' : j' ≫ u = j := pullback.lift_fst _ _ _
  have hjσ : j' ≫ pullback.snd s e = σ := pullback.lift_snd _ _ _
  have hdom : IsDominant u := isDominant_genericFibre O E s
  have hsurj : Surjective j' := ⟨fun w => by
    obtain ⟨Ω, _, _, t, q, rfl⟩ := exists_geomPoint _ w
    obtain ⟨v, hv₁, hv₂⟩ := hgeo Ω (t ≫ u) (t ≫ pullback.snd s e) (by
      rw [Category.assoc, Category.assoc]
      exact congrArg (t ≫ ·) pullback.condition)
    have hv : v ≫ j' = t := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        change v ≫ j' ≫ u = t ≫ u
        rw [hj', hv₁]
      · rw [Category.assoc, hjσ, hv₂]
    refine ⟨v q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hv]⟩

  have hsm : Smooth (pullback.fst j' j' ≫ j' ≫ u ≫ s) := inferInstance
  have hred : IsReduced (pullback j' j') := by
    have : ∀ x : (pullback j' j' : Scheme.{0}), _root_.IsReduced ((pullback j' j' : Scheme.{0}).presheaf.stalk x) := fun x => by
      have := (GlobalTheory.ESOrdM.stalk_normal_of_smooth O _ (pullback.fst j' j' ≫ j' ≫ u ≫ s) x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hP : pullback.fst j' j' ≫ y = pullback.snd j' j' ≫ y := by
    refine eq_of_geomPoints _ _ g ?_ fun Ω _ _ t => ?_
    · rw [Category.assoc, Category.assoc, hy, ← hj', Category.assoc, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine hker Ω _ _ ?_
      rw [Category.assoc, Category.assoc, ← hj', pullback.condition_assoc]
  have hee : EffectiveEpi j' := inferInstance
  let z : pullback s e ⟶ Y := EffectiveEpi.desc j' y (fun {T} g₁ g₂ h => by
    calc g₁ ≫ y = (pullback.lift g₁ g₂ h ≫ pullback.fst j' j') ≫ y := by rw [pullback.lift_fst]
      _ = (pullback.lift g₁ g₂ h ≫ pullback.snd j' j') ≫ y := by
        rw [Category.assoc, Category.assoc, hP]
      _ = g₂ ≫ y := by rw [pullback.lift_snd])
  have hz : j' ≫ z = y := EffectiveEpi.fac _ _ _
  have hzg : z ≫ g = u ≫ f := by
    rw [← cancel_epi j', ← Category.assoc, hz, hy, ← hj', Category.assoc]
  obtain ⟨y', h₁, h₂⟩ := hN _ X Y B u f g z inferInstance hdom (LocallyOfFiniteType.isLocallyNoetherian s)
    (fun x => (GlobalTheory.ESOrdM.stalk_normal_of_smooth O X s x).1)
    (fun x => (GlobalTheory.ESOrdM.stalk_normal_of_smooth O X s x).2) hg hzg
  exact ⟨y', by rw [← hj', Category.assoc, h₁, hz], h₂⟩
