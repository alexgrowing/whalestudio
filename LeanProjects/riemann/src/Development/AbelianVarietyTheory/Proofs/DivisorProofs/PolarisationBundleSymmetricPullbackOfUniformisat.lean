import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LinearUniformisationTorsionMapIsLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWFinal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PrimDescent

theorem isPrim_of_unif : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  intro R _ _ _ I hI D A G _ _ hS U O _ _ _ o oA oG hlin w hprim
  have := hI.2.2.2
  haveI := oG.hom w
  haveI := oG.hom (1 + w)
  haveI := o.onB.hom w
  haveI := o.onB.hom (1 + w)
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hprim
  have hRig := GlobalTheory.PullGenG.hasGen_one U.LG
  have h0 := (HasGen.of_gen ρ hρ).neg.add hRig
  obtain ⟨uΨ, huΨ⟩ := h0.gen U.LG.isLB (K' := Fin 4)
    ![(padd G (𝟙 _) (oG.act w)).left, 𝟙 G.left, (oG.act w).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      have h1' : (toUnit G ≫ η[G] : G ⟶ G) = 1 := rfl
      simp [fsum, Fin.sum_univ_four, Fin.sum_univ_five, GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, lf_single, padd_eq_mul, h1',
        Finsupp.single_neg, single_two, single_neg_two, Matrix.vecHead, Matrix.vecTail]
      abel)
  obtain ⟨u, hu, hn⟩ := GlobalTheory.PsiRescale.exists_normalised U.LG.isLB (oG.act w) uΨ huΨ
  have iG : ∀ i, IsMonHom ((![oG.act (1 + w), 𝟙 G, oG.act w, 1] : Fin 4 → (G ⟶ G)) i) := fun i => by
    fin_cases i
    exacts [oG.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 G)), oG.hom w, inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))]
  have iB : ∀ i, IsMonHom ((![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] : Fin 4 → (D.toPre.P.A ⟶ D.toPre.P.A)) i) :=
    fun i => by
    fin_cases i
    exacts [o.onB.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 _)), o.onB.hom w,
      inferInstanceAs (IsMonHom (toUnit _ ≫ η[D.toPre.P.A]))]
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.UT.PullDescent.exists_descent U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hS (fun V _ c => by
      rw [Fin.prod_univ_four]
      show c ^ (1 : ℤ) * c ^ (-2 : ℤ) * c ^ (-1 : ℤ) * c ^ (2 : ℤ) = 1
      group)
    ![oG.act (1 + w), 𝟙 G, oG.act w, 1] ![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] (fun e i => by
      have := (U.gt e).q_hom
      fin_cases i
      · exact hlin.q_lin e (1 + w)
      · show (Over.pullback (thick R I e)).map (𝟙 G) ≫ _ = _ ≫ (Over.pullback (thick R I e)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      · exact hlin.q_lin e w
      · show (Over.pullback (thick R I e)).map (1 : G ⟶ G) ≫ _ =
          _ ≫ (Over.pullback (thick R I e)).map (1 : D.toPre.P.A ⟶ D.toPre.P.A)
        rw [CategoryTheory.Functor.map_one, CategoryTheory.Functor.map_one, MonObj.one_comp, MonObj.comp_one])
    (fun i => by
      fin_cases i
      · show (oG.act (1 + w)).left = (padd G (𝟙 _) (oG.act w)).left
        rw [oG.map_add, oG.map_one]
      all_goals rfl)
    (ψ := ![(padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left, 𝟙 D.toPre.P.A.left, (o.onB.act w).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left])
    (fun i => by
      fin_cases i
      · show (o.onB.act (1 + w)).left = (padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left
        rw [o.onB.map_add, o.onB.map_one]
      all_goals rfl) u hu hn
  exact ⟨κ, hκ.1⟩

end GlobalTheory.PrimDescent
