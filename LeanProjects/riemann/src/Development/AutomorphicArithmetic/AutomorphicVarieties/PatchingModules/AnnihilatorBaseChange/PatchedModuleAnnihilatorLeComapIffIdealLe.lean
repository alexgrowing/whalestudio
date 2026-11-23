import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaSuppBc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ann_baseChange_le_iff (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (M : Type) [AddCommGroup M]
    [Module B M] [Module.Finite B M] (P : Ideal S) (hP : P.IsPrime) :
    Module.annihilator S (S ⊗[B] M) ≤ P ↔ Module.annihilator B M ≤ P.comap (algebraMap B S) := by
  have h := UpperTheory.V.AlgebraTools.mem_support_baseChange B S M ⟨P, hP⟩
  rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h
  exact h

theorem UpperTheory.V.Pa.Core.patchedModule_annihilator_le_comap_iff_ideal_le :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Function.Surjective m.π → ∀ P : Ideal (Spo A), P.IsPrime → (Module.annihilator W.R (X0 m) ≤ P.comap m.π ↔ J ≤ P.comap (algebraMap B (Spo A))) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hπ P hP
  have hfin : Module.Finite B A.b.M := by
    letI : Algebra (abelian₂ O Unit D) B := A.b.lam.toRingHom.toAlgebra
    haveI : IsScalarTower (abelian₂ O Unit D) B A.b.M :=
      IsScalarTower.of_algebraMap_smul fun a x => (A.b.smul_lam a x).symm
    haveI := A.b.fin
    exact Module.Finite.of_restrictScalars_finite (abelian₂ O Unit D) B A.b.M
  have h1 : Module.annihilator W.R (X0 m) =
      (Module.annihilator (Spo A) (Spo A ⊗[B] A.b.M)).comap m.π := by
    ext a
    rw [Ideal.mem_comap, Module.mem_annihilator, Module.mem_annihilator]
    exact Iff.rfl
  rw [h1, Ideal.comap_le_comap_iff_of_surjective m.π hπ, ann_baseChange_le_iff B (Spo A) A.b.M P hP]
  exact A.b.supp _ (Ideal.comap_isPrime _ P)
