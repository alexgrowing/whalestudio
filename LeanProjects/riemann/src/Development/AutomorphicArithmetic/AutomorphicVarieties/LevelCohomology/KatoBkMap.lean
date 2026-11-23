import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.bkMap :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (C V : Type) [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (C' V' : Type) [CommRing C'] [Algebra ℚ_[l] C'] [AddCommGroup V'] [Module C' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul C' V'] (ρ : Representation C (G F Ω) V) (ρ' : Representation C' (G F Ω) V') (f : V →ₗ[ℚ_[l]] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c : G F Ω → V, Continuous (fun g => f (c g)) → IsBK l ρ c → IsBK l ρ' (fun g => f (c g)) := by
  intro l _ F Ω _ _ _ _ C V _ _ _ _ _ _ _ _ _ C' V' _ _ _ _ _ _ _ _ _ ρ ρ' f hf c hfc hc
  refine ⟨fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := hc.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨_, hcc⟩, x, hx⟩ := hc.above τ
    refine ⟨j, hj, ⟨?_, fun g h => ?_⟩, LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f x, fun g => ?_⟩
    · exact hfc.comp (continuous_fst.comp continuous_subtype_val)
    · have h1 := congrArg f (hcc g h)
      simpa only [map_add, hf, MonoidHom.comp_apply] using h1
    · have key : ∀ y : TensorProduct ℚ_[l] V (UpperTheory.V.Loc.Bcr l),
          LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f
            (UpperTheory.V.Loc.actC ((MonoidHom.snd _ _).comp (decJ F j).subtype)
              (ρ.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype)) g y) =
          UpperTheory.V.Loc.actC ((MonoidHom.snd _ _).comp (decJ F j).subtype)
            (ρ'.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype)) g
            (LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [UpperTheory.V.Loc.actC, hf]
        | add a b ha hb => simp only [map_add, ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
