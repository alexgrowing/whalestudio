import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecsOfIntFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLeadValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullOfSval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermNonzeroClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.SecsAsm

theorem gs_scal_one {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Y ⟶ Sp R) (p : Z ⟶ Y) (z : Z) :
    gs p z ⊤ (scal q 1) = 1 := by
  unfold scal
  rw [map_one, map_one, gs_eq p z ⊤ trivial, map_one, map_one]

theorem closed_pt (R : Type) [CommRing R] [IsLocalRing R] :
    spMap (residue R) (closedPoint (ResidueField R)) = closedPoint R :=
  IsLocalRing.comap_closedPoint (residue R)

theorem secs_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) : Nonempty (Secs C.toModif C.G C.P.L.L C.α) := by
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨hsm, -, -, -, -⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨S, k₁, himm⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  obtain ⟨hth, hth0⟩ := GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D
  choose k₀ hk₀ using hth
  obtain ⟨⟨j₀, hdesc⟩, hdescθ⟩ := GlobalTheory.Mum.exists_secs_of_intFam R hB D C
  have hk : k₁ + ∑ a ∈ S, k₀ a ≤ C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) :=
    (le_max_right _ _).trans (Nat.lt_pow_self C.n_prime.one_lt).le
  obtain ⟨Φ, hΦ⟩ := hdesc (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) (le_max_left _ _)
  obtain ⟨N, α, b, τ, hτ, hατ, hI⟩ := himm _ ((Nat.le_add_right _ _).trans hk)
  have hF : ∀ i, ∃ F : IntFam (maximalIdeal R) D.toPre (C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a))), F.Lead (α i) (b i) :=
    fun i => hk₀ (α i) _ (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hατ i).1).trans
      (Nat.le_add_left _ _)).trans hk) (b i)
  choose F hFl using hF
  obtain ⟨bθ, τθ, y₀, hθt, hy₀c, hy₀⟩ := GlobalTheory.Mum.exists_term_nonzero_closed R hB D Y
  obtain ⟨F₁, hF₁⟩ := hth0 1 le_rfl bθ
  obtain ⟨θ, hθ⟩ := hdescθ F₁
  have hsm0 : Smooth ((Over.pullback (spMap (residue R))).obj Y.H).hom :=
    inferInstanceAs (Smooth (pullback.snd Y.H.hom (spMap (residue R))))
  have himm0 : IsImmersion (pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
    have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
    have : IsClosedImmersion (pullback.fst Y.H.hom (spMap (residue R))) := inferInstance
    infer_instance
  refine ⟨{ N := N, k := _, s := fun i => Φ (F i), θ := θ, Y := (Over.pullback (spMap (residue R))).obj Y.H
            smooth := hsm0
            j := pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
            j_over := ?_
            imm := himm0
            O := pullback.fst Y.H.hom (spMap (residue R)) ⁻¹ᵁ nonzeroLocus τθ
            O_ne := ?_
            trait := ?_ }⟩
  · rw [Category.assoc, GlobalTheory.ProjSpace.toProj_str, pullback.condition]; rfl
  · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.H.hom) (g := spMap (residue R)) y₀
      (closedPoint _) (hy₀c.trans (closed_pt R).symm)
    exact ⟨z, show pullback.fst Y.H.hom (spMap (residue R)) z ∈ nonzeroLocus τθ by rw [hz]; exact hy₀⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, T, hio, hfin, hTφ, hTξ⟩ := C.exists_trait W hW φ ξ hφ hloc hξ
  obtain ⟨u, hu⟩ := hΦ W' T
  obtain ⟨uθ, huθ⟩ := hθ W' T
  choose σ hσE hσA using fun i => hu (F i)
  obtain ⟨θ', hθE, hθA⟩ := huθ
  obtain ⟨κ, e, hκ, he, hred⟩ := GlobalTheory.Mum.trait_lead_value R hB D C Y W' T
  have hκ' : κ.comp (residue R) = (residue W').comp (io.comp φ) := by rw [hκ, hTφ]
  refine ⟨W', _, inferInstance, inferInstance, io, T.G, inferInstance, T.β, σ, θ', κ, e, T.cdvr, hio, hfin,
    by rw [← hTξ]; exact T.cart, hκ', he, fun i Z p p' hpp z J hJ => ?_, fun Z p p' hpp z J hJ => ?_, ?_⟩
  · rw [hσA i Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  · rw [hθA Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  intro Ω _ p p' y hp hy
  have hval := hred (Sp Ω) p p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) hp
    (by rw [hy]; simp only [Category.assoc])
  have e1 : spMap (residue W') ≫ spMap (io.comp φ) = spMap κ ≫ spMap (residue R) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ']
  have hw := Over.w e.hom
  have hbase : p' ≫ T.G.hom ≫ spMap (io.comp φ) = (y ≫ pullback.fst Y.H.hom (spMap (residue R))) ≫ Y.H.hom := by
    rw [hp]
    simp only [Category.assoc]
    rw [pullback.condition_assoc, e1, pullback.condition]
    rw [hy]
    simp only [Category.assoc]
    erw [pullback.condition_assoc]
    rw [← Category.assoc e.hom.left]
    erw [hw]
    rfl
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨-, hs, hP⟩ := GlobalTheory.Mum.toProj_secPull_of_sval R Ω C.G.left D.toPre.P.A.left T.G.left Y.H.left C.P.L.L D.toPre.P.L
      T.β Y.q.left _ N σ τ Y.H.hom hτ p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) C.P.L.isLB D.toPre.P.isLB
      (fun z J J' hJ hJ' => by
        obtain ⟨c, hc⟩ := hval _ u z J J' hJ hJ'
        exact ⟨c, fun i => hc (α i) (b i) (τ i) (F i) (σ i) (hατ i).2 (hFl i) (hσE i)⟩)
    rw [hbase]
    exact ⟨hs, hP.trans (by simp only [Category.assoc])⟩
  · choose J hJ using fun χ : Sp Ω ⟶ C.G.left => exists_chart C.P.L.isLB (χ x)
    choose J' hJ' using fun χ : Sp Ω ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ x)
    obtain ⟨c, hc⟩ := hval 1 uθ x J J' hJ hJ'
    have h1 := hc 0 bθ τθ F₁ θ' hθt hF₁ hθE
    have hx' : (y ≫ pullback.fst Y.H.hom (spMap (residue R))) x ∈ nonzeroLocus τθ := hx
    have hu1 := (GlobalTheory.mem_nonzeroLocus_iff_pull τθ _ x (Good.mem hJ' _ _)).1 hx'
    refine (GlobalTheory.mem_nonzeroLocus_iff_pull θ' p' x (Good.mem hJ _ _)).2 ?_
    change IsUnit (sval θ' p' x J)
    rw [h1]
    exact c.isUnit.mul hu1

end GlobalTheory.Mum.SecsAsm

theorem GlobalTheory.Mum.exists_secs_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (C₁ : LabCover D₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ Nonempty (Secs C₁.toModif C₁.G C₁.P.L.L C₁.α) := by
  intro R _ _ _ hB D C
  obtain ⟨h, -, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D, C,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, ⟨h⟩, GlobalTheory.Mum.SecsAsm.secs_exists R hB D C⟩
