import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

namespace GlobalTheory.CompanionTheory.IwaDbl

theorem hasSat_of_family {B K O I : Type} [CommRing B] [Field K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O K] [IsFractionRing O K] (π : I → B →+* K) (hinj : ∀ y z : B, (∀ i, π i y = π i z) → y = z)
    (hsurj : ∀ f : I → K, ∃ y : B, ∀ i, π i y = f i) (A : Subring B)
    (hA : ∀ y, y ∈ A ↔ ∀ i, π i y ∈ (algebraMap O K).range) (β : Type) [Fintype β] [DecidableEq β] : HasSat A β := by
  have hlift : ∀ {m n : Type} (f : I → Matrix m n K), ∃ X : Matrix m n B, ∀ i, X.map (π i) = f i := by
    intro m n f
    choose g hg using fun p : m × n => hsurj fun i => f i p.1 p.2
    exact ⟨Matrix.of fun a b => g (a, b), fun i => Matrix.ext fun a b => by simp [hg]⟩
  have hext : ∀ {m n : Type} (X Y : Matrix m n B), (∀ i, X.map (π i) = Y.map (π i)) → X = Y := by
    intro m n X Y h
    exact Matrix.ext fun a b => hinj _ _ fun i => by simpa using congrFun (congrFun (h i) a) b
  have hmem : ∀ {m n : Type} (X : Matrix m n B) (Y : I → Matrix m n O),
      (∀ i, X.map (π i) = (Y i).map (algebraMap O K)) → ∀ a b, X a b ∈ A := by
    intro m n X Y h a b
    refine (hA _).2 fun i => RingHom.mem_range.2 ⟨Y i a b, ?_⟩
    simpa using (congrFun (congrFun (h i) a) b).symm
  intro C N hNC
  have hleft : ∀ i, ∃ L : Matrix β (β ⊕ β) K, L * C.map (π i) = 1 := fun i =>
    ⟨N.map (π i), by rw [← Matrix.map_mul, hNC]; simp⟩
  choose t C₀ D htC hdet using fun i =>
    GlobalTheory.CompanionTheory.MatSat.exists_saturation (O := O) (C.map (π i)) (hleft i)
  obtain ⟨T, hT⟩ := hlift fun i => Units.val (t i)
  obtain ⟨T', hT'⟩ := hlift fun i => Units.val (t i)⁻¹
  obtain ⟨Dl, hDl⟩ := hlift fun i => (D i).map (algebraMap O K)
  obtain ⟨Ml, hMl⟩ := hlift fun i => ((Matrix.fromCols (C₀ i) (D i))⁻¹).map (algebraMap O K)
  have hCT : ∀ i, (C * T).map (π i) = (C₀ i).map (algebraMap O K) := fun i => by
    rw [Matrix.map_mul, hT]
    exact htC i
  refine ⟨T, T', Dl, Ml, ?_, hmem _ C₀ hCT, hmem _ D hDl,
    hmem _ (fun i => (Matrix.fromCols (C₀ i) (D i))⁻¹) hMl, ?_⟩
  · refine hext _ _ fun i => ?_
    rw [Matrix.map_mul, hT, hT', Units.mul_inv]
    simp
  · refine hext _ _ fun i => ?_
    rw [Matrix.map_mul, Matrix.fromCols_map, hMl, hCT, hDl, ← Matrix.fromCols_map, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (hdet i)]
    simp

end GlobalTheory.CompanionTheory.IwaDbl
