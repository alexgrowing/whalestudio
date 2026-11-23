import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatCompEnvelopeAlgebraMapStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA

namespace CrystallineSemistableComparison.Pb.Site

theorem polyT_mem {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} (hp : p ≠ 0)
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
    (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (h : Q₀ = ⊤ ∨ Q₀ = FlatT) (𝒱 : Set X.Opens)
    (T : (St Q₀ 𝒱).FullSubcategory) : St Q₀ 𝒱 (polyT T.obj hp) := by
  refine ⟨?_, ?_⟩
  · rcases h with rfl | rfl
    · trivial
    · exact GlobalTheory.T.flat_comp_envelope_algebraMap T.obj.i T.property.1
  · obtain ⟨V, hV, hT⟩ := T.property.2
    exact ⟨V, hV, inU_hom (polyJ T.obj hp) hT⟩

def polyDesc {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)) (hp : p ≠ 0)
    {T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (F : (pq T.B).P →+* T'.B)
    (hF : F.comp (algebraMap T.B (pq T.B).P) = φ.φ) (hFd : IsDPMorphism (eta T.δ) T'.δ F)
    (hle : (pq T.B).ext T.J ≤ T'.J.comap F) : polyT T hp ⟶ T' :=
  descOf φ F hF hFd hle

def polyAll {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} (hp : p ≠ 0)
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
    (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (h : Q₀ = ⊤ ∨ Q₀ = FlatT) (𝒱 : Set X.Opens) :
    Poly (sP (St Q₀ 𝒱)) where
  P T := ⟨polyT T.obj hp, polyT_mem hp Q₀ h 𝒱 T⟩
  j T := ObjectProperty.homMk (polyJ T.obj hp)
  X T := (pq T.obj.B).e 1
  X_mem T := Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
  univ {T T'} φ x hx := by
    obtain ⟨F, ⟨hF, hF1, hFd⟩, hFu⟩ := GlobalTheory.T.divided_power_envelope_universal T.obj.δ T'.obj.δ φ.hom.φ φ.hom.dp x hx
    have hle : (pq T.obj.B).ext T.obj.J ≤ T'.obj.J.comap F := Ideal.map_le_iff_le_comap.1 hFd.1
    refine ⟨ObjectProperty.homMk (polyDesc T.obj hp φ.hom F hF hFd hle), ?_, ?_⟩
    · refine And.intro ?_ ?_
      · ext1
        exact CrystallineSemistableComparison.Pb.hom_ext hF
      · exact hF1
    · rintro ψ ⟨h1, h2⟩
      ext1
      refine CrystallineSemistableComparison.Pb.hom_ext ?_
      refine hFu ψ.hom.φ ⟨?_, h2, ψ.hom.dp⟩
      exact congrArg (fun f => f.hom.φ) h1
  span T z := GlobalTheory.T.divided_power_envelope_expansion T.obj.δ z

theorem poly_all' : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (h : Q₀ = ⊤ ∨ Q₀ = FlatT)
    (𝒱 : Set X.Opens), ∃ Q : Poly (sP (St Q₀ 𝒱)), ∀ r : ℤ, Q.Crit (sFil _) r ∧ Q.Crit (fun _ => IdF.bot _) r ∧
      ∀ c : R, Q.Crit (fun r => stdI _ (some r) c) r ∧ Q.Crit (fun _ => stdI _ none c) r ∧ Q.Crit (fun _ => IdF.span _ c) r := by
  intro O R _ _ I γ p hp X q κ Q₀ h 𝒱
  refine ⟨polyAll hp Q₀ h 𝒱, fun r => ⟨?_, ?_, fun c => ⟨?_, ?_, ?_⟩⟩⟩
  · intro T b
    refine Iff.trans (GlobalTheory.T.divided_power_envelope_filtration T.obj.δ b r.toNat 0).1 (forall_congr' fun k => ?_)
    change _ ↔ b k ∈ fil T.obj.δ (r - k).toNat
    rw [show (r - k).toNat = r.toNat - k by omega]
    exact Iff.rfl
  · intro T b
    refine Iff.trans (GlobalTheory.T.divided_power_envelope_filtration T.obj.δ b 0 0).2.2.2 (forall_congr' fun k => ?_)
    change _ ↔ b k ∈ (⊥ : Ideal T.obj.B)
    rw [Ideal.mem_bot]
    exact Iff.rfl
  · intro T b
    refine Iff.trans (GlobalTheory.T.divided_power_envelope_filtration T.obj.δ b r.toNat (T.obj.i c)).2.1 (forall_congr' fun k => ?_)
    change _ ↔ b k ∈ fil T.obj.δ (r - k).toNat ⊔ Ideal.span {T.obj.i c}
    rw [show (r - k).toNat = r.toNat - k by omega]
    exact Iff.rfl
  · intro T b
    have e : ∀ (B : Type) [CommRing B] (a : B), (⊥ : Ideal B) ⊔ Ideal.span {a} = Ideal.span {a} := fun _ _ _ => bot_sup_eq _
    refine Iff.trans ?_ (Iff.trans (GlobalTheory.T.divided_power_envelope_filtration T.obj.δ b 0 (T.obj.i c)).2.2.1 (forall_congr' fun k => ?_))
    · change _ ∈ (⊥ : Ideal (pq T.obj.B).P) ⊔ Ideal.span {algebraMap T.obj.B (pq T.obj.B).P (T.obj.i c)} ↔ _
      rw [e]
      rfl
    · change _ ↔ b k ∈ (⊥ : Ideal T.obj.B) ⊔ Ideal.span {T.obj.i c}
      rw [e]
      exact Iff.rfl
  · intro T b
    exact (GlobalTheory.T.divided_power_envelope_filtration T.obj.δ b 0 (T.obj.i c)).2.2.1

end CrystallineSemistableComparison.Pb.Site
