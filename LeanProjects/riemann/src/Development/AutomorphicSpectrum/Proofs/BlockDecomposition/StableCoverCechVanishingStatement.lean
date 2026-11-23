import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIsoStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_cover_cech_vanishing : (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
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
  first | exact @GlobalTheory.CompanionTheory.GlobSt.glob_st | exact GlobalTheory.CompanionTheory.GlobSt.glob_st | (intros; apply GlobalTheory.CompanionTheory.GlobSt.glob_st <;> assumption)
