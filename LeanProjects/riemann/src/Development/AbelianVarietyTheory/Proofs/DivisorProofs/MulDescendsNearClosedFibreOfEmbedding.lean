import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismDescendsNearFibreRigidityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenMulPointOnPullbackContainingClosedFibrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordConstantOnProjectionFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismLocalDescentsGlueUnionStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Near.law_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → N.Law := by
  intro R _ _ _ hR M G' _ _ _ E N fU l hl1 hl2
  obtain ⟨hNoeth, -, hIC, -⟩ := hR
  obtain ⟨hbij, hsurj⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  haveI := M.proper
  haveI := M.integral
  haveI := N.smooth
  obtain ⟨O, h, hfib, hover, hpt⟩ := GlobalTheory.T.exists_open_mul_point_on_pullback_containing_closedFibre R M G' N
  have hconst := GlobalTheory.T.closedFibre_productCoord_constant_on_projectionFibres R M G' E N fU l hl1 hl2 hsurj O h hpt
  have hflat : Flat (N.U ⊗ N.U).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hPB : IsPullback (pullback.fst (N.U ⊗ N.U).hom M.π) (pullback.snd (N.U ⊗ N.U).hom M.π) (N.U ⊗ N.U).hom M.π :=
    IsPullback.of_hasPullback _ _
  have hpsurj : Surjective (pullback.fst (N.U ⊗ N.U).hom M.π) := by
    haveI : Surjective M.π := hsurj
    infer_instance
  have key : ∀ i : {y₀ : (N.U ⊗ N.U).left // (N.U ⊗ N.U).hom y₀ = closedPoint R},
      ∃ (V : (N.U ⊗ N.U).left.Opens) (hV : pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ N.U.left),
        i.1 ∈ V ∧ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ V) ≫ h₀ = (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV ≫ h := by
    rintro ⟨y₀, hy₀⟩
    obtain ⟨z, hz⟩ := hpsurj.surj y₀
    have hzO : z ∈ O := hfib z (by rw [hz]; exact hy₀)
    exact GlobalTheory.T.morphism_descends_near_fibre_rigidity R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj hbij hflat hPB O h y₀ (h ⟨z, hzO⟩)
      (fun z' hz' => hfib z' (by rw [hz']; exact hy₀))
      (fun z' hz' => hconst z' ⟨z, hzO⟩ (by rw [hz']; exact hz.symm) (by rw [hz']; exact hy₀))
  choose V hV h₀ hmem hcomm using key
  obtain ⟨hV', m, hm, huniq⟩ := GlobalTheory.T.morphism_local_descents_glue_union R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj M.integral hflat hPB O h _ V hV h₀ hcomm
  refine ⟨⨆ i, V i, m, fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hmem _⟩, ?_, ?_⟩
  · apply huniq
    simp only [reassoc_of% hm, hover, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc]
  · intro T v s x y hx hy
    have hc : (v ≫ (⨆ i, V i).ι) ≫ (N.U ⊗ N.U).hom = s ≫ M.π := by
      obtain ⟨x₀, h1, h2, -⟩ := hx
      have e1 : (fst N.U N.U).left ≫ N.U.hom = (N.U ⊗ N.U).hom := Over.w _
      simp only [← e1, ← h2, Category.assoc, ← pullback.condition]
      rw [reassoc_of% h1]
    let z : T ⟶ pullback (N.U ⊗ N.U).hom M.π := pullback.lift (v ≫ (⨆ i, V i).ι) s hc
    let z₁ := (isPullback_morphismRestrict (pullback.fst (N.U ⊗ N.U).hom M.π) (⨆ i, V i)).lift v z (pullback.lift_fst _ _ _).symm
    have hz₁a : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ ⨆ i, V i) = v := IsPullback.lift_fst _ _ _ _
    have hz₁b : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ ⨆ i, V i).ι = z := IsPullback.lift_snd _ _ _ _
    let t := z₁ ≫ (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV'
    have ht : t ≫ O.ι = z := by
      simp only [t, Category.assoc, Scheme.homOfLE_ι, hz₁b]
    have hvm : v ≫ m = t ≫ h := by rw [← hz₁a, Category.assoc, hm, Category.assoc]
    rw [hvm]
    refine hpt T t s x y (by rw [reassoc_of% ht, pullback.lift_snd]) ?_ ?_
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hx
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hy

end GlobalTheory.Mum
