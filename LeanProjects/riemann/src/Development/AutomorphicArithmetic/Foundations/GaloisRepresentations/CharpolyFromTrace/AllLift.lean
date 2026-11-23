import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLMemWeil
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem dec_restrict {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {g : G K Ω} (hg : g ∈ Dec (F := K) A) :
    AlgEquiv.restrictScalars F g ∈ Dec (F := F) A :=
  GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec hg x

private def Carry {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ)
    [Fact l.Prime] (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E))) (X : UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fld E Ω) : Prop :=
  ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
    UpperTheory.Gal.InertialTypesAlt.Lifts (UpperTheory.Gal.InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : UpperTheory.Gal.InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
    (∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))) ∧
    ∀ u ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A u → (∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) →
      ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → ∃ B, (CG.mk P).HasSat w' B

theorem UpperTheory.Gal.NearKilling.allLift :
    StepLift → UpperTheory.Gal.UnramifiedFromSplittingCriterion.SatSplit → AllLift := by
  intro hStep hSat E Ω _ _ _ _ _ _ l a _ ha π χ hχ S hS X hX
  suffices H : Carry l a π S X by
    obtain ⟨P, χ', h1, h2, h3, -⟩ := H
    exact ⟨P, χ', h1, h2, h3⟩
  refine UpperTheory.Gal.UnramifiedFromSplittingCriterion.Tower.induction (S := S) (P := Carry l a π S) ?_ ?_ hX
  · refine ⟨π, χ, Relation.ReflTransGen.refl, hχ, fun ι r h => ?_, fun u hu A hA _ w' hw' => ?_⟩
    · exact h
    · have e : w' = u := HeightOneSpectrum.ext (Ideal.ext fun x => (hw' x).symm.trans (hA x))
      rw [e]
      exact hS u hu
  · rintro X Y - ⟨alg, t1, t2, hG, hp, u, hu, hsp, A, hA, τ, hτ, hτn⟩ ⟨P, χ', h1, h2, h3, h4⟩
    obtain ⟨v, hv, -⟩ := GlobalTheory.AboveL.exists_isPlaceOver_of_tower E X.K Ω A u hA
    have hfix : ∀ g ∈ Dec (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg =>
      (hsp A hA (AlgEquiv.restrictScalars _ g) (dec_restrict hg)).2
    obtain ⟨P', χ'', hbc, hsl, hsc, -, hweak⟩ :=
      hStep X.K Y.K Ω hp l a ha P χ' h2 A v hv ⟨τ, hτ, hτn⟩ (h4 u hu A hA hfix v hv)
    refine ⟨P', χ'', Relation.ReflTransGen.tail h1 ⟨alg, t2, hG, hp, hbc⟩, hsc, fun ι r h => ?_, ?_⟩
    · exact hweak ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K)) (h3 ι r h)
    · intro u' hu' A' hA' hfix' w' hw'
      have hv' : IsPlaceOver A' (w'.under (𝓞 X.K)) := fun x => by
        rw [IsScalarTower.algebraMap_apply X.K Y.K Ω]
        exact hw' (algebraMap (𝓞 X.K) (𝓞 Y.K) x)
      have hfixX : ∀ g ∈ Dec (F := E) A', UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g := fun g hg x => by
        have := hfix' g hg (algebraMap X.K Y.K x)
        rwa [← IsScalarTower.algebraMap_apply] at this
      obtain ⟨B, hB⟩ := h4 u' hu' A' hA' hfixX _ hv'
      exact ⟨B, hSat X.K Y.K Ω A' _ w' hv' hw' (fun g hg => hfix' _ (dec_restrict hg)) a P P' hsl B hB⟩
