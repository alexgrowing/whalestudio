import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

open PoitouTate

def PoitouTateDuality : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ), (l ≠ 2 ∨ IsTotallyComplex F) → 0 < r →
  ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
  ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      NineTermExact S Av μ (invAt S Av μ hμ inv) ρ hρ ∧ ShaDual S Av μ ρ ∧
        ∀ n, 3 ≤ n → Subsingleton (Hn ρ n)

def PoitouTateOdd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ), l ≠ 2 → 0 < r →
  ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
  ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      NineTermExact S Av μ (invAt S Av μ hμ inv) ρ hρ ∧ ShaDual S Av μ ρ ∧
        ∀ n, 3 ≤ n → Subsingleton (Hn ρ n)

theorem PoitouTateDuality.odd (h : PoitouTateDuality) : PoitouTateOdd :=
  fun F Ω _ _ _ _ _ l _ r hl => h F Ω l r (Or.inl hl)

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Published.PoitouTateDuality.totallyComplex (h : _root_.GlobalTheory.Published.PoitouTateDuality) :
    _root_.GlobalTheory.Published.PoitouTateTotallyComplex := by
  unfold _root_.GlobalTheory.Published.PoitouTateTotallyComplex
  intro F Ω _ _ _ _ _ _ l _ r hr ζ hζ
  obtain ⟨inv, hloc, hall⟩ := h F Ω l r (Or.inr inferInstance) hr ζ hζ
  exact ⟨inv, hloc, fun S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ =>
    ⟨(hall S hS Av hAv μ hμ M ρ hρ).1, (hall S hS Av hAv μ hμ M ρ hρ).2.1⟩⟩

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Published.exists_primitiveRoot_pow (F Ω : Type) [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Published.PoitouTateDuality.cohDimTwoGlobal
    (h : _root_.GlobalTheory.Published.PoitouTateDuality) : _root_.GlobalTheory.Published.CohDimTwoGlobal := by
  unfold _root_.GlobalTheory.Published.CohDimTwoGlobal
  intro F Ω _ _ _ _ _ _ l _ r M _ _ _ _ _ S rhoS hS hρ n hn
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    haveI : Subsingleton M := Module.subsingleton (ZMod (l ^ 0)) M
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [_root_.GlobalTheory.Published.subsingleton_Hn_succ_iff]
    intro f _ _
    exact ⟨0, continuous_zero, Subsingleton.elim _ _⟩
  · obtain ⟨ζ, hζ⟩ := _root_.GlobalTheory.Published.exists_primitiveRoot_pow F Ω l r
    obtain ⟨inv, _, hall⟩ := h F Ω l r (Or.inr inferInstance) hr ζ hζ
    obtain ⟨μ, hμ⟩ := _root_.GlobalTheory.Published.PoitouTate.exists_lift_cycMod (Ω := Ω) (r := r) hS
    exact (hall S hS (fun v => (_root_.ReciprocityTheory.Gal.exists_isPlaceOver Ω v.1).choose) (fun v => (_root_.ReciprocityTheory.Gal.exists_isPlaceOver Ω v.1).choose_spec)
      μ hμ M rhoS hρ).2.2 n hn

end GlobalTheory.Published
