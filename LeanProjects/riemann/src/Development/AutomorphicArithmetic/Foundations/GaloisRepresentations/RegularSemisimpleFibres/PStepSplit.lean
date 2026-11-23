import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.stepSplit :
    StableOf → ResEmbCompat → LblIso → ∀ P₀, StepAt P₀ id := by
  intro hS hC hI P₀ K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp n hn π P hW A Θ hΘ v w hsplit hunr e e' he he' τ τ' hτ hτ' a hP ha
  refine ⟨a, Relation.ReflTransGen.refl, ?_⟩
  obtain ⟨-, hSL⟩ := hS K M hp n hn π P hW
  obtain ⟨r, j, h1, h2, h3⟩ := hC K M Ω A v w e e' he he'
  have hs : UpperTheory.ConvolutionTheory.GM.Split M v := hsplit
  let i : v.adicCompletion K ≃+* w.1.adicCompletion M :=
    RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs w⟩
  have hi : ∀ x, i x = completionMap v w.1 x := fun _ => rfl
  have hic : Continuous i := continuous_completionMap v w.1
  have hal : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x) := fun x => by
    rw [hi, completionMap_algebraMap, IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M)]
  obtain ⟨f, hf⟩ := hSL v w.1 i hic hal τ τ' hτ hτ'
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 K)).ne'
  have hle : ∀ x y : w.1.adicCompletion M, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion M)) Valued.v x y
  have hle' : ∀ x y : v.adicCompletion K, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v x y
  have hv : ∀ x : v.adicCompletion K, valuation _ (i x) ≤ 1 ↔ valuation _ x ≤ 1 := fun x => by
    have a1 := hle (i x) (i 1)
    have a2 := hle' x 1
    rw [map_one (valuation (v.adicCompletion K))] at a2
    rw [map_one i, map_one (valuation (w.1.adicCompletion M))] at a1
    rw [a1, a2, ← map_one i, hi, hi, valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0
  have hcond : ∀ (x : 𝒪[v.adicCompletion K]) (y : 𝒪[w.1.adicCompletion M]), (y : w.1.adicCompletion M) = i x →
      j (algebraMap _ _ (IsLocalRing.residue _ x)) = algebraMap _ _ (IsLocalRing.residue _ y) :=
    fun x y hy => by rw [h2, h1 x y hy]
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom :=
    MonoidHom.ext fun x => congrArg Θ (h3 x)
  exact hI _ _ i hv j hcond (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ f hf a (by rw [hθ]; exact ha)
