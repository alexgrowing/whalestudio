import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreduciblesStatement

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem redK_mem_unipRad {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {g : GL (Fin n) k}
    (hu : g ∈ unipRad k e) (hK : g ∈ KO k (Fin n)) : redK k (Fin n) ⟨g, hK⟩ ∈ unipRad 𝓀[k] e := by
  refine CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_
  have h := CuspMax.mem_unipRad_iff_entries.1 hu i j hij
  by_cases hh : i = j
  · subst hh
    have h1 := (redK_eq_iff ⟨g, hK⟩ i i 1).2 (by simp [h])
    simpa using h1
  · rw [Matrix.one_apply_ne hh]
    exact (redK_eq_zero_iff ⟨g, hK⟩ i j).2 (by simp [h, Matrix.one_apply_ne hh])

private theorem finCusp_levelZero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (hc : IsCuspidal π) : PositivityTheory.Rg.DzCount.FinCusp (levelZero π) := by
  intro s d e hne v hv
  have hV : (v : V) ∈ fixed π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    refine GlobalTheory.DepthZeroJac.mem_fixed_sup v.2 (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_)
    have h1 := congrArg Subtype.val (hv _ (redK_mem_unipRad e hg.1 hg.2))
    rwa [levelZero_apply] at h1
  have hne' : unipRad k e ≠ ⊥ := CuspMax.unipRad_ne_bot_iff.2 (CuspMax.unipRad_ne_bot_iff.1 hne)
  haveI := hc.2 s d e hne'
  exact Subtype.ext (GlobalTheory.DepthZeroJac.depthZeroJacquetInjective k n s d e ⟨V, π, hs, hi⟩ (v : V) hV (Subsingleton.elim _ _))

private theorem irreducible_levelZero (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (hω : HasCentralChar π.ρ ω)
    (hF : PositivityTheory.Rg.DzCount.FinCusp (levelZero π.ρ)) (hD : fixed π.ρ (KOne k (Fin n)) ≠ ⊥) :
    (levelZero π.ρ).IsIrreducible := by
  have key : ∀ W : Subrepresentation (levelZero π.ρ), W ≠ ⊥ → W = ⊤ := by
    intro W hW
    haveI : Nontrivial W.toSubmodule := by
      rw [Submodule.nontrivial_iff_ne_bot]
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    let j : W.toSubmodule →ₗ[ℂ] π.V := (fixed π.ρ (KOne k (Fin n))).subtype ∘ₗ W.toSubmodule.subtype
    have hFτ : PositivityTheory.Rg.DzCount.FinCusp W.toRepresentation := by
      intro s d e hne w hw
      exact Subtype.ext (hF s d e hne w (fun u hu => congrArg Subtype.val (hw u hu)))
    have hj : PositivityTheory.Rg.DzCount.IsTypeMap W.toRepresentation π.ρ j := by
      refine ⟨?_, ?_⟩
      · intro a c hac
        exact Subtype.ext (Subtype.ext hac)
      · intro g w
        exact levelZero_apply π.ρ g w
    have hfix := PositivityTheory.Rg.DzCount.B.st6 k W.toSubmodule n W.toRepresentation hFτ π ω hω j hj
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule = ⊤
    rw [eq_top_iff]
    intro v _
    have hv : (v : π.V) ∈ LinearMap.range j := hfix ▸ v.2
    obtain ⟨w, hw⟩ := hv
    have hwv : (w : fixed π.ρ (KOne k (Fin n))) = v := Subtype.ext hw
    rw [← hwv]
    exact w.2
  haveI : Nontrivial (Subrepresentation (levelZero π.ρ)) := by
    refine ⟨⟨⊥, ⊤, fun h => hD ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hm : (⟨v, hv⟩ : fixed π.ρ (KOne k (Fin n))) ∈ (⊤ : Subrepresentation (levelZero π.ρ)).toSubmodule :=
      Submodule.mem_top
    rw [← h'] at hm
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm)
  constructor
  intro W
  by_cases h : W = ⊥
  · exact Or.inl h
  · exact Or.inr (key W h)

end

theorem UpperTheory.Gal.InertialTypesAlt.cuspIrr :
    CuspIrr := by
  intro k _ _ _ _ _ y hc hD
  have hadm := (UpperTheory.Zero.LLC.Pr.adm k y.1 y.2.rep.V y.rep y.2.rep.smooth y.2.rep.irr).2 (levelPre ⊥)
    (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
  rw [levelPre_bot] at hadm
  obtain ⟨ω, hω⟩ := (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles k).1 y
  have hF := finCusp_levelZero y.rep y.2.rep.smooth y.2.rep.irr hc.2
  exact ⟨hadm, irreducible_levelZero y.2.rep ω hω hF hD, hF⟩
