import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianAmpleAcyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleRelativelyAcyclic
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxForm (IsRelAcyclic)
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.RelAcyclicAmple
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleAcyclicModel

theorem of_ampleVanishing (AV : GlobalTheory.Published.AmpleVanishing) :
    ∀ (k : Type) [CommRing k] (S : Scheme.{0}) [IsLocallyNoetherian S] (p : S ⟶ Sp k) (A : Over S) [GrpObj A],
      IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic (A.hom ≫ p) A.hom L := by
  intro k _ S _ p A _ hA L hL hamp U hU κ _ _ W hW hWU n
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let t : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  have h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t := IsPullback.of_hasPullback _ _
  obtain ⟨hproj, hsm, -, -⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp
    Γ(S, U) t _ _ _ h
  haveI : Flat (pullback.snd A.hom t) := inferInstance
  have hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U := by
    ext x
    change x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)
    rw [Scheme.Pullback.range_fst, hU.range_fromSpec]
    rfl
  have hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange := fun i =>
    hrange ▸ (le_iSup W i).trans hWU.le
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle
  refine HomologicalComplex.ExactAt.of_iso ?_ e
  refine (cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_
  refine cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _
    (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n
  · intro P hP
    letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P
    let χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P) :=
      (algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)
    refine ⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩
    · rw [RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]
    · intro κ' _ _ D' hD' hc' m
      have := hA.proper
      let B := (Over.pullback t).obj A
      have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj t A hA
      have : IsProper B.hom := hB.proper
      have hLB : (L.pull (pullback.fst A.hom t)).IsLB := LB.isLB_pull hL _
      have hampB : Out.RelAmple B (L.pull (pullback.fst A.hom t)) := AmpleBaseChange.relAmple_of_isPullback hL hamp h
      let A₀ := (Over.pullback (Spec.map (CommRingCat.ofHom χ))).obj B
      have hA₀ : IsAbelianScheme A₀ := isAbelianScheme_pullback_obj _ B hB
      have hamp₀ := AmpleBaseChange.relAmple_of_isPullback hLB hampB
        (IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom χ)))
      exact AV _ A₀ hA₀ _ (LB.isLB_pull hLB _) hamp₀ ⊤ (isAffineOpen_top _) κ' D' hD'
        (by rw [hc', Scheme.Hom.preimage_top]) m
  · rw [← Scheme.Hom.preimage_iSup, hWU, ← hrange]
    exact Scheme.Hom.preimage_opensRange _

theorem iff_ampleVanishing : GlobalTheory.Published.AbelianAmpleAcyclic ↔ GlobalTheory.Published.AmpleVanishing := by
  refine ⟨fun H K _ _ A _ hA L hL hamp => ?_, fun AV k _ S _ _ p A _ => of_ampleVanishing AV k S p A⟩
  have : ConnectedSpace (Sp K) := inferInstanceAs (ConnectedSpace (PrimeSpectrum K))
  have h := H K (Sp K) (𝟙 _) A hA L hL hamp
  rwa [Category.comp_id] at h

theorem hyp_ell {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    IsLocallyNoetherian (Sp R) ∧ ConnectedSpace (Sp R) ∧ IsAbelianScheme (WeierstrassCurve.ellPolAV W).A ∧
      (WeierstrassCurve.ellPolAV W).g = 1 ∧ (WeierstrassCurve.ellPolAV W).L.IsLB ∧
      Out.RelAmple (WeierstrassCurve.ellPolAV W).A (WeierstrassCurve.ellPolAV W).L :=
  ⟨inferInstance, inferInstanceAs (ConnectedSpace (PrimeSpectrum R)), (WeierstrassCurve.ellPolAV W).isAb,
    WeierstrassCurve.ellPolAV_g W, (WeierstrassCurve.ellPolAV W).isLB, (WeierstrassCurve.ellPolAV W).ample⟩

example : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩

theorem ell_exactAt_one (H : GlobalTheory.Published.AbelianAmpleAcyclic) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (D : Fin 2 → (WeierstrassCurve.ellPolAV W).A.left.Opens)
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) :
    (cechLB (WeierstrassCurve.ellPolAV W).A.hom (WeierstrassCurve.ellPolAV W).L D).ExactAt 1 := by
  obtain ⟨h₁, h₂, h₃, -, h₅, h₆⟩ := hyp_ell W
  have h := H R (Sp R) (𝟙 _) _ h₃ _ h₅ h₆ ⊤ (isAffineOpen_top _) (Fin 2) D hD (by rw [hc]; rfl) 0
  rwa [Category.comp_id] at h

end GlobalTheory.AmpleAcyclicModel
