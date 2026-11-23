import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomMumfordGeneratorNormalisedOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMumfordGeneratorAdditiveCubicalStructuresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

open GlobalTheory.HomMum in

theorem GlobalTheory.HomMum.lbIso_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], AdmBase R (maximalIdeal R) → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom fB → IsMonHom gB → Over₀ U₁.toUnifPre U₂.toUnifPre f fB → Over₀ U₁.toUnifPre U₂.toUnifPre g gB → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ f) (snd G₁ G₁ ≫ g) : G2 G₁ ⟶ G2 G₂).left) → LBIso (abelian₂ D₁.toPre.P.A D₁.toPre.P.L) ((abelian₂ D₂.toPre.P.A D₂.toPre.P.L).pull (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ fB) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ gB) : G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left) := by
  intro R _ _ _ _ hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ f g fB gB _ _ _ _ of og H
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := hG₁.geomConnected
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  obtain ⟨w, hw⟩ := H
  obtain ⟨t, ht, -⟩ := exists_gen_of_iso (isPart_inr U₁.LG.L U₂.LG.L) (isPart_inl U₁.LG.L U₂.LG.L) w hw
  have hN := join_isLB U₁.LG.isLB U₂.LG.isLB
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_homMumfordGenerator_normalised_origin hN f g t ht
  have sj := (FamGerm.surjective_appTop_sq_cube U₁.toUnifPre).2
  have hP : AbLaw.IsProjBy D₁.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _)
  obtain ⟨V, hV, t', ht'⟩ := GlobalTheory.EndRosati.loc_gen_of_thickenings hGF (maximalIdeal R) _
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D₁.toPre.P.isAb D₁.toPre.P.isAb)
    (AbLaw.isProjBy_tensor R _ _ hP hP) (jn_isLB D₁.toPre D₂.toPre) (mφ D₁.toPre.P.A D₂.toPre.P.A fB gB) mε
    (fun e => by
      have := EndTorus.connectedSpace_thickening (maximalIdeal R) e
      have : GeometricallyConnected (thickObj R (maximalIdeal R) e G₁).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G₁.hom (thick R (maximalIdeal R) e)))
      have : ConnectedSpace (thickObj R (maximalIdeal R) e G₁).left :=
        GroupConn.connectedSpace_of_section (thickObj R (maximalIdeal R) e G₁).hom
          (η : 𝟙_ _ ⟶ thickObj R (maximalIdeal R) e G₁).left (Over.w _)
      exact GlobalTheory.T.exists_mumfordGenerator_abelianPart_at_level U₁.toUnifPre U₂.toUnifPre e (of e) (og e) u hu
        fun T z J hJ x x' y => GlobalTheory.T.homMumfordGenerator_additive_cubicalStructures U₁.cubG U₂.cubG hN sj f g u hu T z J hJ x x' y) (closedPoint R)
  have hall : ∀ p : PrimeSpectrum R, p ∈ V := fun p =>
    ((PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.isPrime.ne_top)).mem_open V.isOpen hV
  obtain ⟨t'', ht'', -⟩ := glue_gen (jn_isLB D₁.toPre D₂.toPre) (mφ D₁.toPre.P.A D₂.toPre.P.A fB gB) mε
    (fun _ : Unit => (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom ⁻¹ᵁ V) (fun y => ⟨(), hall _⟩) (fun _ => t') (fun _ => ht')
    (fun _ _ Z r r' z J _ h => by
      obtain rfl := (cancel_mono _).1 h
      rfl)
  obtain ⟨w', hw', -⟩ := exists_iso_of_gen (isPart_inr D₁.toPre.P.L D₂.toPre.P.L) (isPart_inl D₁.toPre.P.L D₂.toPre.P.L)
    D₂.toPre.P.isLB D₁.toPre.P.isLB (snd_surjective D₁.toPre.P.isLB) (fst_surjective D₂.toPre.P.isLB) t'' ht''
  exact ⟨w', hw'⟩
