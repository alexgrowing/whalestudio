import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleDescent

theorem isAmpleLB_of_pull {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') [Flat (specOf g)]
    [Surjective (specOf g)] {X X' : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')} [UniversallyClosed f']
    (H : IsPullback π f' f (specOf g)) {L : LB X} (hL : L.IsLB) (h : IsAmpleLB (L.pull π)) : IsAmpleLB L := by
  have hg : g.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 (inferInstance : Flat (specOf g))
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨n, hn, s, hs, -⟩ := h.exists_affine z
  have hM := isLB_lbPow hL n
  obtain ⟨σ, hσ⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hM π) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL π n).symm s
  obtain ⟨m, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ hM σ
  obtain ⟨k, hk⟩ := exists_chart hM (π z)
  have hz : IsUnit (gs (𝟙 X') z _ (σ.f fun _ => k)) :=
    (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => k) (mem_pull.2 hk)).1 (hσ.ge hs)
  rw [hu z k hk] at hz
  obtain ⟨j, -, hj⟩ := IsLocalRing.exists_of_isUnit_sum hz
  refine ⟨n, hn, u j, (mem_nonzeroLocus_iff_pull (u j) π z hk).2 (isUnit_of_mul_isUnit_right hj), ?_⟩
  have ha := h.isAffineOpen_nonzeroLocus f' hn (secPowPull (u j) π)
  rw [nonzeroLocus_secPowPull] at ha
  have : IsAffine (π ⁻¹ᵁ nonzeroLocus (u j)) := ha
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict π (nonzeroLocus (u j))).paste_vert H)

theorem kTriv_of_pull {S S' : Scheme.{0}} [IsAffine S] [IsAffine S'] {f : S' ⟶ S} [Flat f] [Surjective f]
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L') :
    KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  obtain ⟨R', g, t', hg, sq⟩ : ∃ (R' : CommRingCat.{0}) (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S'),
      Epi g ∧ g ≫ t = t' ≫ f := by
    refine ⟨Γ(pullback t f, ⊤), (pullback t f).isoSpec.inv ≫ pullback.fst t f,
      (pullback t f).isoSpec.inv ≫ pullback.snd t f, Flat.epi_of_flat_of_surjective _, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact Over.OverMorphism.ext ((cancel_epi g).1 (congrArg (fun q => q.left) e₂))

theorem proper_relAmple_kTriv_of_fieldExtension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [QuasiCompact G.hom] [IsSeparated G.hom] [Smooth G.hom] (G' : Over (Spec (CommRingCat.of K'))) [GrpObj G'] (Ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (specOf i) Ψ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (L.pull Ψ) → IsProper G'.hom → RelAmple G' L' → KTriv G' L' → IsProper G.hom ∧ RelAmple G L ∧ KTriv G L := by
  intro K K' _ _ i G _ _ _ _ G' _ Ψ h L L' hL hL' hw hP hA hK
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
  have : Flat (specOf i) := inferInstance
  have : Surjective (specOf i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hG : IsProper G.hom := ⟨⟩
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  refine ⟨hG, (relAmple_iff_isAmpleLB_of_isAffine G hL).2 (isAmpleLB_of_pull i h.1 hL ?_),
    kTriv_of_pull h hL hL' hw hK⟩
  exact (isAmpleLB_of_relAmple_of_isAffine G' hL' hA).of_lbIso (LB.isLB_pull hL Ψ) hw.symm

end GlobalTheory.AmpleDescent
