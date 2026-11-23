import Development.WeilBound.CoreStatements.VolumeEquality.HolNull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding

noncomputable section

namespace SheetDecomposition.One

open AlgebraicGeometry CategoryTheory Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem isHolTo_mono {X : Scheme.{0}} {n : ℕ} {B T : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)}
    (hy : IsHolTo B y) (hT : IsOpen T) (h : T ⊆ B) : IsHolTo T y := by
  intro U f
  have e : {b ∈ T | ⊤ ≤ y b ⁻¹ᵁ U} = T ∩ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    exact ⟨fun hb => ⟨hb.1, h hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
  rw [e]
  exact ⟨hT.inter (hy U f).1, (hy U f).2.mono Set.inter_subset_right⟩

theorem exists_point {K : Type} [Field K] (σ : K →+* ℂ) {X : Scheme.{0}} (s : X ⟶ Sp K) [LocallyOfFiniteType s]
    (U : X.Opens) {q : X} (hq : q ∈ U) : ∃ x : Sp ℂ ⟶ X, x ≫ s = spMap σ ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨V, hV, hqV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := q) (U := U) hq
  let ρ' : CommRingCat.of K ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)
  let ρ : K →+* Γ(X, V) := ρ'.hom
  have hρ : ρ.FiniteType := by
    have h1 := LocallyOfFiniteType.finiteType_appLE s (isAffineOpen_top (Sp K)) hV (fun _ _ => trivial)
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    exact h1.comp h2
  letI : Algebra K Γ(X, V) := ρ.toAlgebra
  haveI : Algebra.FiniteType K Γ(X, V) := hρ
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : Nonempty V := ⟨⟨q, hqV⟩⟩
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(X, V)
  haveI : IsJacobsonRing Γ(X, V) := isJacobsonRing_of_finiteType (A := K)
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (Γ(X, V) ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (Γ(X, V) ⧸ M)
  let e : (Γ(X, V) ⧸ M) →ₐ[K] ℂ := IsAlgClosed.lift
  let χ : Γ(X, V) →ₐ[K] ℂ := e.comp (Ideal.Quotient.mkₐ K M)
  let x : Sp ℂ ⟶ X := spMap χ.toRingHom ≫ hV.fromSpec
  have hmem : ∀ p, x p ∈ V := fun p => by
    have : x p = hV.fromSpec ((spMap χ.toRingHom) p) := by simp [x]
    rw [this, ← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨x, ?_, fun p _ => hVU (hmem p)⟩
  have hc : ρ' ≫ CommRingCat.ofHom χ.toRingHom = CommRingCat.ofHom σ := by
    ext z
    exact χ.commutes z
  have h0 : hV.fromSpec ≫ s = Spec.map ρ' := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  have e : x ≫ s = Spec.map (ρ' ≫ CommRingCat.ofHom χ.toRingHom) := by
    rw [Spec.map_comp]
    simp only [x, Category.assoc]
    rw [h0]
  rw [e, hc]

end SheetDecomposition.One
