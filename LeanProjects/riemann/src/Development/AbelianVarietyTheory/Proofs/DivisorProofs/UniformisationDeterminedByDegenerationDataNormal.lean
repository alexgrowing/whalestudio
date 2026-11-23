import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfModelIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericRel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoExtendingGenericCompleteLocalNormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DataDetNormal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem isMonHom_generic (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j)
    (hw : GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) : IsMonHom Φ.hom := by
  let ψ : A'.A ≅ A.A := U'.gen.symm ≪≫ Φ ≪≫ U.gen
  have hψ : Φ.hom ≫ U.gen.hom = U'.gen.hom ≫ ψ.hom := by simp [ψ]
  have := U.gen_hom
  have := U'.gen_hom
  have hm : IsMonHom ψ.hom := hL.rigidity _ _ _ A'.isAb A.isAb _ (by
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, ← hψ, ← Category.assoc, hw.one hL hR hI hG hG' hj hE,
      IsMonHom.one_hom])
  have e : Φ.hom = U'.gen.hom ≫ ψ.hom ≫ U.gen.inv := by simp [ψ]
  rw [e]
  infer_instance

end GlobalTheory.DataDetNormal

namespace GlobalTheory.DataDetNormal

theorem exists_iso_extending {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) [IsMonHom Φ.hom] :
    ∃ ψ : G' ≅ G, IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = Φ.hom := by
  have h := GlobalTheory.semiAbelianHomExtension_holds
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h.fractionField R (FractionRing R) G' G hG' hG Φ.hom
  obtain ⟨F₁, ⟨hF₁, hF₁'⟩, -⟩ := h.fractionField R (FractionRing R) G G' hG hG' Φ.inv
  obtain ⟨E₁, -, u₁⟩ := h.fractionField R (FractionRing R) G' G' hG' hG' (𝟙 _)
  obtain ⟨E₂, -, u₂⟩ := h.fractionField R (FractionRing R) G G hG hG (𝟙 _)
  have c₁ : F ≫ F₁ = 𝟙 G' := (u₁ _ ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', Iso.hom_inv_id]⟩).trans
    (u₁ _ ⟨inferInstance, (Over.pullback _).map_id _⟩).symm
  have c₂ : F₁ ≫ F = 𝟙 G := (u₂ _ ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', Iso.inv_hom_id]⟩).trans
    (u₂ _ ⟨inferInstance, (Over.pullback _).map_id _⟩).symm
  exact ⟨⟨F, F₁, c₁, c₂⟩, hF, hF'⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem thick_compat (hL : Laws) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j)
    (hw : GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) (ψ : G' ⟶ G)
    (hψ : (Over.pullback (jK R)).map ψ = Φ.hom) (e : ℕ) :
    (fstG I e G').left ≫ ψ.left = (j e).hom.left ≫ (fstG I e G).left := by
  have := hR.1
  have := hG.smooth
  have := hG.separated
  have := hG'.smooth
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R (FractionRing R)
  have eψ : Φ.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.left := by
    rw [← hψ]; exact pullback.lift_fst _ _ _
  have hx0 : ∀ x : G'.left, I ≤ (G'.hom x).asIdeal → x ∈ Set.range (fstG I 0 G').left := fun x hx => by
    show x ∈ Set.range (pullback.fst G'.hom (thick R I 0))
    rw [Scheme.Pullback.range_fst]
    exact (GlobalTheory.FormalExt.range_thick I 0 _).2 hx
  refine GlobalTheory.FormalExt.hom_ext_of_flat_family _ _ fun y => ?_
  obtain ⟨x, hx⟩ := hx0 ((fstG I e G').left y) ((GlobalTheory.FormalExt.range_thick I e _).1 (by
    have : (fstG I e G').left y ∈ Set.range (pullback.fst G'.hom (thick R I e)) := ⟨y, rfl⟩
    rw [Scheme.Pullback.range_fst] at this
    exact this))
  obtain ⟨jL, hjL⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', hjL'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, hB, -, hg'f, hxr, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G'
    (fun e => (j e).hom) (fun e => (hj e).2.1) x _ _ hjL hjL'
  have hpt : ∀ {Z : Scheme.{0}} (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left),
      r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g :=
    fun ρ r hr => hw.point hL hR hG hG' hE hB h₁ h₂ h₃ h₄ h₅ ρ r hr
  have hg : g' ≫ ψ.left = g := by
    let a : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk (g' ≫ ψ.left) (by simp)
    let b : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk g (h₂.trans h₁.symm)
    have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R)) := inferInstance
    have : IsSchemeTheoreticallyDominant (pullback.fst g' (pullback.fst G'.hom (jK R))) := inferInstance
    have := GlobalTheory.over_ext_of_schemeTheoreticallyDominant (a := a) (b := b)
      (pullback.fst g' (pullback.fst G'.hom (jK R))) (by
        have := hpt _ (pullback.snd g' (pullback.fst G'.hom (jK R))) pullback.condition.symm
        rw [eψ] at this
        exact (pullback.condition_assoc _).trans this)
    exact congr(($this).left)
  refine ⟨_, pullback.snd g' (fstG I e G').left, inferInstance, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd]
    show (fstG I e G').left y ∈ Set.range g'
    rw [← hx]; exact hxr
  · rw [h₅ e _ _ _ pullback.condition.symm, ← pullback.condition_assoc, hg]

end GlobalTheory.DataDetNormal

theorem GlobalTheory.unif_determined_by_data_normal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, GlobalTheory.UT.Cl.Determined U := by
  intro R _ _ _ hR D A G _ _ hG U D' A' G' _ _ hG' U' hD
  have hL := GlobalTheory.firstFiveLaws.1
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hR.1
  have := hR.2.2.1
  obtain ⟨j, hj⟩ := GlobalTheory.GenericIso.exists_levelIso U.toUnifPre U'.toUnifPre hD hL.globalFns
  have hE := hj.enough hL.globalFns U.expand U'.expand
  obtain ⟨Φ, w, hw⟩ := GlobalTheory.GenericIso.exists_genericRel hL R _ hR D D' A A' G G' hG hG' U U' hD j hj hE
  have hΦ : IsMonHom Φ.hom := GlobalTheory.DataDetNormal.isMonHom_generic hL hR hI hG hG' hj hE hw
  obtain ⟨ψ, hψm, hψK⟩ := GlobalTheory.DataDetNormal.exists_iso_extending hG hG' Φ
  have hth := GlobalTheory.DataDetNormal.thick_compat hL hR hG hG' hj hE hw ψ.hom hψK
  obtain ⟨wL, hwL, H⟩ := GlobalTheory.T.exists_bundleIso_extending_generic_completeLocalNormal R hR D D' A A' G G' hG hG' U U' hD j hj Φ w hw ψ hψm hψK hth
  have hs := Geo.Tor.specOf_id R
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso ((isGrpPullback_of_iso ψ).congr hs.symm rfl)
    (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have hbc' : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left := hbc
  have he₀ : eSec G' ≫ ψ.hom.left = eSec G := congrArg Over.Hom.left hψm.one_hom
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G :=
    (congrArg (_ ≫ ·) hbc').trans (he₀.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _)).symm)
  have hr := GlobalTheory.pmaps_rig_of_thick_compat hI U.toUnifPre U'.toUnifPre hD (fun e => (j e).hom) (fun e => (hj e).1)
    he₀ wL hwL H
  have hP : IsPullUnif (RingHom.id R) hD bc U U' := (isPullUnif_iff_stalks R R _ _ _ D D' hD A A' G G' bc U U').2
    ⟨pullCongr hbc'.symm wL, (isGen_iff _).2 (pgen_pullCongr _ ((isGen_iff _).1 hwL)), he, ?_, fun e =>
      ⟨(j e).hom.left, (hth e).symm.trans (congrArg (_ ≫ ·) hbc'.symm), (hj e).2.2,
        fun Z r z jM jM' jL jL' h₁ h₂ h₃ h₄ => ?_⟩⟩
  · obtain ⟨φ, h1, h2, h3⟩ := GlobalTheory.UT.exists_genericFibre_iso_of_model_iso R _ D D' A A' G G' U.toUnifPre
      U'.toUnifPre ψ hψm ⟨wL, hwL⟩
    exact ⟨ψ, bc, φ, hψm, mbc, hbc', hP, h1, h2, h3⟩
  · refine (Geo.Tor.maps_iff _ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
      (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr _ ?_)
    exact (congrArg (PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig)
      hs).mpr hr
  · rw [gw_pullCongr]
    refine H e Z r z jM jM' jL jL' h₁ h₂ ?_ h₄
    rw [hbc'] at h₃
    exact (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (hth e)).mp h₃
