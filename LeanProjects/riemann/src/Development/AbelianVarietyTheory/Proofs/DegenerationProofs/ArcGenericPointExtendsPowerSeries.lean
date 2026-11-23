import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcExtends

theorem exists_lift_finite {K : Type} [Field K] {Z X : Scheme.{0}} (π : Z ⟶ X) [IsFinite π] [Surjective π]
    (x : Sp K ⟶ X) : ∃ (L : Type) (_ : Field L) (σ : K →+* L) (z : Sp L ⟶ Z), σ.Finite ∧ z ≫ π = spMap σ ≫ x := by
  have : CompactSpace ↥(pullback π x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (default : PrimeSpectrum K)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π x)) ⟨p, trivial⟩
  have := isClosed_singleton_iff_isClosedImmersion.mp hq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback π x).fromSpecResidueField q ≫ pullback.snd π x)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  refine ⟨(pullback π x).residueField q, inferInstance, φ.hom,
    (pullback π x).fromSpecResidueField q ≫ pullback.fst π x, (IsFinite.SpecMap_iff φ).1 hf, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hφ]
  rfl

theorem spMap_jK {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ jK R = jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem finite_fractionRing {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) : gam.Finite := by
  letI := g.toAlgebra
  letI := gam.toAlgebra
  have : Module.Finite R R₁ := hg
  have : IsScalarTower R (FractionRing R) (FractionRing R₁) := IsScalarTower.of_algebraMap_eq fun r => (h r).symm
  have : FaithfulSMul R R₁ := (faithfulSMul_iff_algebraMap_injective R R₁).2 fun a b e =>
    IsFractionRing.injective R (FractionRing R) (gam.injective (by
      rw [h, h]; exact congrArg _ e))
  show Module.Finite (FractionRing R) (FractionRing R₁)
  exact Module.Finite.of_isLocalization R R₁ (nonZeroDivisors R)

theorem exists_normalisation (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (hc : IsAdicComplete (IsLocalRing.maximalIdeal R) R) {R₁ : Type} [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) {L : Type} [Field L] {σ : FractionRing R₁ →+* L} (hσ : σ.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (_ : IsNoetherianRing R₂)
      (_ : IsIntegrallyClosed R₂) (_ : CharZero R₂) (g₂ : R₁ →+* R₂) (f : L →+* FractionRing R₂),
      (∀ r, (f.comp σ) (algebraMap R₁ _ r) = algebraMap R₂ _ (g₂ r)) ∧ (g₂.comp g).IsIntegral := by
  letI := (σ.comp gam).toAlgebra
  letI := ((σ.comp gam).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (FractionRing R) L := hσ.comp (finite_fractionRing h hg)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hc L
  have hR : ∀ r, algebraMap R L r = σ (algebraMap R₁ _ (g r)) := fun r => congrArg σ (h r)
  have hi : ∀ r : R₁, (σ.comp (algebraMap R₁ (FractionRing R₁))) r ∈ integralClosure R L := fun r => by
    obtain ⟨p, hp, e⟩ := hg.to_isIntegral r
    refine ⟨p, hp, ?_⟩
    have e' := congrArg (σ.comp (algebraMap R₁ (FractionRing R₁))) e
    rw [Polynomial.hom_eval₂, map_zero] at e'
    rw [← e']
    congr 1
    exact RingHom.ext hR
  have hinj : Function.Injective (algebraMap R L) :=
    (σ.comp gam).injective.comp (IsFractionRing.injective R (FractionRing R))
  have : CharZero L := charZero_of_injective_algebraMap hinj
  let g₂ : R₁ →+* integralClosure R L := (σ.comp (algebraMap R₁ (FractionRing R₁))).codRestrict _ hi
  refine ⟨integralClosure R L, inferInstance, inferInstance, h₂, h₃, h₄, inferInstance, g₂,
    (FractionRing.algEquiv (integralClosure R L) L).symm.toRingHom, fun r => ?_, ?_⟩
  · exact (FractionRing.algEquiv (integralClosure R L) L).symm.commutes (g₂ r)
  · have e : g₂.comp g = algebraMap R (integralClosure R L) := RingHom.ext fun r => Subtype.ext (hR r).symm
    rw [e]
    exact (RingHom.finite_algebraMap.2 h₁).to_isIntegral

theorem arcBase_complete {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : ArcBase O' ϖ) :
    ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
  rcases h with ⟨hF, -⟩ | ⟨hD, hi, hc⟩
  · letI := hF.toField
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · refine ⟨inferInstance, inferInstance, ?_⟩
    rwa [hi.maximalIdeal_eq]

theorem polAt_moduli {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K]
    (y : Sp K ⟶ Xo.XF c) : PolAt Y.t (y ≫ Y.j) := by
  have hm : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp := isGrpPullback_pullback Y.t.G (y ≫ Y.j)
  let ψ : ((Over.pullback (y ≫ Y.j)).obj Y.t.G).left ⟶ Y.oF.t.G.left :=
    hm.1.lift (pullback.fst Y.t.G.hom (y ≫ Y.j)) (pullback.snd Y.t.G.hom (y ≫ Y.j) ≫ y)
      (by rw [Category.assoc]; exact pullback.condition)
  have e₁ : ψ ≫ Y.m.φ = pullback.fst Y.t.G.hom (y ≫ Y.j) := hm.1.lift_fst _ _ _
  have hq : IsGrpPullback ((Over.pullback (y ≫ Y.j)).obj Y.t.G) Y.oF.t.G y ψ :=
    IsGrpPullback.cancel hm (hp.congr rfl e₁.symm) (hm.1.lift_snd _ _ _)
  obtain ⟨w, hw, -⟩ := Y.m.lin
  have hI : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (pullback.fst Y.t.G.hom (y ≫ Y.j))) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L _ _ _ ψ fun _ => e₁.symm) ⟨w, hw⟩
  have := Y.oF.proper
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hq.1 Y.oF.proper,
    amplePt _ K y _ _ ψ hq _ _ Y.oF.t.PP.isLB (pull_isLB Y.t.PP.isLB _) hI.symm Y.oF.ample Y.oF.ktriv⟩

theorem exists_extension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  intro hL hL₂ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hO m Z π t mt hfin hsurj ⟨Am⟩ R₁ _ _ g y₁ gam hgam hg _ y hy hs
    ⟨θ₁, hθ₁⟩ ⟨n, f₁, hf₁⟩
  obtain ⟨_, _, hc⟩ := arcBase_complete hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨L, _, σ, z, hσ, hz⟩ := exists_lift_finite π (y₁ ≫ Y.j)
  obtain ⟨R₂, _, _, _, _, _, hch, g₂, f, hf, hint⟩ :=
    exists_normalisation (PowerSeries O') ReciprocityTheory.P1.isAdicComplete_ps hgam hg hσ
  have hx : (spMap f ≫ z) ≫ π = spMap (f.comp σ) ≫ y₁ ≫ Y.j := by
    rw [Category.assoc, hz, spMap_comp, Category.assoc]
  have hP := polAt_moduli Y y₁
  obtain ⟨θ, hθ, bθ⟩ := GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP 1 1 _ hθ₁
  obtain ⟨ff, hff, bff⟩ := GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP (m ^ 2) n _ hf₁
  obtain ⟨θ', rfl⟩ : ∃ θ', θ = fun _ : Fin 1 => θ' := ⟨θ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hab : Set.range (spMap f ≫ z) ⊆ abLocus t.G := by
    rintro _ ⟨p, rfl⟩
    refine (abLocus_pullback abLocusOne Y.t.semi mt.cart.1 _).1 (abLocusOne _ Y.t.G Y.t.semi _ _ hP.1 ?_)
    exact ⟨spMap (f.comp σ) p, (congrArg (fun q => q p) hx).symm⟩
  obtain ⟨e, he, hE⟩ := GlobalTheory.FrameGen.exists_gen_of_frames Z t.G t.PP.L t.PP.isLB (m ^ 2) Am Am.A rfl R₂ _ hab θ' n ff hθ hff bθ bff hch
  have := projProper _ _ _ Y.proj
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (π ≫ Y.s)
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (π ≫ Y.s)
  have hG : ∀ r, ((f.comp σ).comp gam) (algebraMap (PowerSeries O') _ r) = algebraMap R₂ _ ((g₂.comp g) r) := fun r =>
    (congrArg (f.comp σ) (hgam r)).trans (hf _)
  have hx' : (spMap f ≫ z) ≫ π = spMap ((f.comp σ).comp gam) ≫ y ≫ Y.j := by
    rw [hx, ← hy, spMap_comp gam]
    simp only [Category.assoc]
  obtain ⟨χ₂, hχ₂⟩ := GlobalTheory.ExtLB.exists_extension Z Am.A Am.isLB Am.ample R₂ _ e he fun V _ _ _ hV φ gV hgV => by
    have := hV.1
    obtain ⟨χ, hχ, -⟩ := val_exists (π ≫ Y.s) (spMap gV ≫ spMap f ≫ z)
      (spMap φ ≫ spMap (g₂.comp g) ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b) (by
        rw [Category.assoc, ← Category.assoc (spMap f ≫ z), hx', Category.assoc, Category.assoc, hs,
          ← Category.assoc (spMap _) (jK _), spMap_jK hG, Category.assoc, ← Category.assoc (spMap gV), spMap_jK hgV,
          Category.assoc])
    exact ⟨χ, hχ.symm, hE V hV φ gV hgV χ hχ.symm⟩
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.extension_descends_of_isIntegral _ R₂ _ _ hG hint Y.X (y ≫ Y.j) (χ₂ ≫ π)
    (by rw [← Category.assoc, hχ₂, hx'])
  exact ⟨χ, hχ⟩

end GlobalTheory.LN.ArcExtends
