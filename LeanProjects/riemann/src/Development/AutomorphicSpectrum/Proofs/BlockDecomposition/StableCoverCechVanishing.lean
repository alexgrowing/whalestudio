import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIsoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingForUpwardClosedCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfUpwardClosedCover
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GlobSt

section St
variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
  (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens)

theorem st_single_rel (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T') (h : St Q {U α} T)
    (h' : ∃ β, St Q {U β} T') : St Q {U α} T' := by
  obtain ⟨-, V, hV, hi⟩ := h
  obtain ⟨β, hQ, -⟩ := h'
  rw [Set.mem_singleton_iff] at hV
  subst hV
  exact ⟨hQ, _, rfl, GlobalTheory.T.inOpen_of_thickening_morphism _ φ hi⟩

theorem st_single_union : (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U) := by
  funext T
  refine propext ⟨?_, ?_⟩
  · rintro ⟨α, hQ, V, hV, hi⟩
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨hQ, _, ⟨α, rfl⟩, hi⟩
  · rintro ⟨hQ, V, ⟨α, rfl⟩, hi⟩
    exact ⟨α, hQ, _, rfl, hi⟩

theorem st_single_capS (S : Finset ι) (hS : S.Nonempty) :
    capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α} := by
  funext T
  refine propext ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hS
    refine ⟨(h a ha).1, _, rfl, (GlobalTheory.T.inOpen_finite_inf_iff U S T).2 fun α hα => ?_⟩
    obtain ⟨-, V, hV, hi⟩ := h α hα
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact hi
  · rintro ⟨hQ, V, hV, hi⟩ α hα
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨hQ, _, rfl, (GlobalTheory.T.inOpen_finite_inf_iff U S T).1 hi α hα⟩

end St

theorem tens_congr {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] (G : C' ⥤ C) {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    {U₁ U₂ : ObjectProperty C} {V₁ V₂ : ObjectProperty C'} (e : U₁ = U₂) (e' : V₁ = V₂)
    (h₁ : ∀ T, V₁ T → U₁ (G.obj T)) (h₂ : ∀ T, V₂ T → U₂ (G.obj T)) (j : ℕ)
    (H : Tens R (N := N) (M := fun i => HU (F i) U₁ j) (M' := HU F' V₁ j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h₁).pull j x) :
    Tens R (N := N) (M := fun i => HU (F i) U₂ j) (M' := HU F' V₂ j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h₂).pull j x := by
  subst e e'
  exact H

theorem glob_st : (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {Λ : Type} [CommRing Λ]
    (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j < s, Subsingleton (HU F (St Q (Set.range U)) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j, Subsingleton (HU F (St Q (Set.range U)) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (St Q {⨅ α ∈ S, U α}) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (HU F (St Q (Set.range U)) j))) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {Λ : Type} [CommRing Λ]
    (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} (U : ι → X.Opens) (𝒮 : Serre.{1} Λ) (n : ℕ),
    (∀ a b, a + b = n → 𝒮.P ((cechH F (fun α => St Q {U α}) b).cx.H a)) → 𝒮.P (HU F (St Q (Set.range U)) n)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
    {O' : Type} [CommRing O'] {R' : Type} [CommRing R'] {I' : Ideal R'} {γ' : DividedPowers I'} {p' : ℕ}
    {X' : Scheme.{0}} {q' : X' ⟶ Spec (CommRingCat.of O')} {κ' : O' →+* R' ⧸ I'}
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {σ : Λ →+* Λ'}
    (G : Thick (nlFun γ' p' X' q' κ') ⥤ Thick (nlFun γ p X q κ)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module Λ (N i)] [∀ i, Module.Flat Λ (N i)]
    (F : ι → (Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} Λ)) (F' : Thick (nlFun γ' p' X' q' κ') ⥤ ModuleCat.{0} Λ')
    (τ : ∀ i, N i → ∀ T, (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : Λ) n T x, τ i (r • n) T x = σ r • τ i n T x)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p' X' q' κ')))
    {A : Type} [Fintype A] (U : A → X.Opens) (U' : A → X'.Opens) (h : ∀ α T, St Q' {U' α} T → St Q {U α} (G.obj T))
    (hS : ∀ (S : Finset A) T, St Q' {⨅ α ∈ S, U' α} T → St Q {⨅ α ∈ S, U α} (G.obj T))
    (hR : ∀ T, St Q' (Set.range U') T → St Q (Set.range U) (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens Λ (N := N) (M := fun i => HU (F i) (St Q {⨅ α ∈ S, U α}) j)
      (M' := HU F' (St Q' {⨅ α ∈ S, U' α}) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (hS S)).pull j x) →
    ∀ j, Tens Λ (N := N) (M := fun i => HU (F i) (St Q (Set.range U)) j) (M' := HU F' (St Q' (Set.range U')) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) hR).pull j x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro O _ R _ I γ p X q κ Λ _ F Q ι _ U s
    have key := GlobalTheory.CompanionTheory.GlobRel.glob_van_rel F (fun α => St Q {U α}) (st_single_rel Q U) s
    rw [st_single_union Q U] at key
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨fun H => k1 fun S hS => ?_, fun H => k2 fun S hS => ?_, fun H => k3 fun S hS => ?_⟩ <;>
      · rw [st_single_capS Q U S hS]
        exact H S hS
  · intro O _ R _ I γ p X q κ Λ _ F Q ι U 𝒮 n H
    have key := GlobalTheory.CompanionTheory.CosieveRel.serre_union F (fun α => St Q {U α}) (st_single_rel Q U) 𝒮 n H
    rw [st_single_union Q U] at key
    exact key
  · intro O _ R _ I γ p X q κ O' _ R' _ I' γ' p' X' q' κ' Λ Λ' _ _ σ G ι _ _ N _ _ _ F F' τ hτ hadd hsm Q Q' A _ U U' h hS hR H j
    refine tens_congr G N F F' τ hτ (st_single_union Q U) (st_single_union Q' U') (fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩) hR j
      (GlobalTheory.CompanionTheory.CosieveRel.base_change_rel G N F F' τ hτ hadd hsm (fun α => St Q {U α}) (fun α => St Q' {U' α})
        (st_single_rel Q U) (st_single_rel Q' U') h (fun S hne j => ?_) j)
    exact tens_congr G N F F' τ hτ (st_single_capS Q U S hne).symm (st_single_capS Q' U' S hne).symm (hS S) _ j (H S hne j)

end GlobalTheory.CompanionTheory.GlobSt
