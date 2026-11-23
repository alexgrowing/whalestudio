import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfPrincipalMod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KernelThickening

theorem exists_closed_equalizer {S : Scheme.{0}} (D : Over S) [IsSeparated D.hom] (n : ℕ) :
    ∀ (A : Over S) (x z : Fin n → (A ⟶ D)), ∃ (K : Over S) (k : K ⟶ A), IsClosedImmersion k.left ∧
      ∀ (T : Over S) (y : T ⟶ A), (∀ j, y ≫ x j = y ≫ z j) ↔ ∃ y' : T ⟶ K, y' ≫ k = y := by
  induction n with
  | zero =>
    intro A x z
    refine ⟨A, 𝟙 A, by rw [Over.id_left]; infer_instance, fun T y => ⟨fun _ => ⟨y, by simp⟩, fun _ j => j.elim0⟩⟩
  | succ n ih =>
    intro A x z
    obtain ⟨K, k, hk, hK⟩ := ih (equalizer (x 0) (z 0)) (fun j => equalizer.ι _ _ ≫ x j.succ)
      (fun j => equalizer.ι _ _ ≫ z j.succ)
    refine ⟨K, k ≫ equalizer.ι _ _, by rw [Over.comp_left]; infer_instance, fun T y => ⟨fun h => ?_, ?_⟩⟩
    · obtain ⟨y', hy'⟩ := (hK T (equalizer.lift y (h 0))).1 fun j => by
        simpa using h j.succ
      exact ⟨y', by rw [← Category.assoc, hy', equalizer.lift_ι]⟩
    · rintro ⟨y', rfl⟩ j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Category.assoc]
        rw [equalizer.condition (x 0) (z 0)]
      · simpa using (hK T (y' ≫ k)).2 ⟨y', rfl⟩ j

theorem mono_of_proper {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (hπ : Function.Surjective π)
    (N : ℕ) (hN : RingHom.ker π ^ N = ⊥) {H : Scheme.{0}} (f : H ⟶ Sp R) [IsProper f] (e : Sp R ⟶ H)
    (h : ∀ (T : Scheme.{0}) (d : T ⟶ H) (t : T ⟶ Sp R₀), d ≫ f = t ≫ spMap π → d = d ≫ f ≫ e) : Mono f := by
  have hnil : ∀ a ∈ RingHom.ker π, a ^ N = 0 := fun a ha => by
    have := Ideal.pow_mem_pow ha N
    rwa [hN, Ideal.mem_bot] at this
  have hinj : Function.Injective f := by
    refine Function.LeftInverse.injective (g := e) fun p => ?_
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (H.fromSpecResidueField p ≫ f)
    have hker : RingHom.ker π ≤ RingHom.ker φ.hom := fun a ha => by
      have : (φ.hom a) ^ N = 0 := by rw [← map_pow, hnil a ha, map_zero]
      exact IsNilpotent.eq_zero ⟨N, this⟩
    let ψ : CommRingCat.of R₀ ⟶ H.residueField p := CommRingCat.ofHom (π.liftOfSurjective hπ ⟨φ.hom, hker⟩)
    have hψ : CommRingCat.ofHom π ≫ ψ = φ := CommRingCat.hom_ext (π.liftOfRightInverse_comp _ _ ⟨φ.hom, hker⟩)
    have h₁ := h _ (H.fromSpecResidueField p) (Spec.map ψ) (by
      rw [← hφ, spMap, ← Spec.map_comp, hψ])
    obtain ⟨q, hq⟩ : ∃ q : Spec (H.residueField p), H.fromSpecResidueField p q = p :=
      ⟨IsLocalRing.closedPoint (H.residueField p), Scheme.fromSpecResidueField_apply _ _⟩
    have h₂ : H.fromSpecResidueField p q = (H.fromSpecResidueField p ≫ f ≫ e) q := congrArg (fun g => g q) h₁
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hq] at h₂
    exact h₂.symm
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_injective hinj
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  refine GlobalTheory.PrincipalModRadical.mono_of_section (RingHom.ker π) ?_ f e fun T d t hd => ?_
  · exact fun a ha => Ideal.radical_le_jacobson ⟨N, hnil a ha⟩
  · refine h T d (t ≫ spMap (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom) ?_
    rw [hd, Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    simp

theorem kernel_trivial_of_nilpotent :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
    (∃ N : ℕ, RingHom.ker π ^ N = ⊥) → ∀ (A : Over (Sp R)) [GrpObj A], IsProper A.hom →
    ∀ (n : ℕ) (D : Over (Sp R)) [GrpObj D], IsSeparated D.hom → ∀ (x : Fin n → (A ⟶ D)), (∀ j, IsMonHom (x j)) →
    (∀ (T₀ : Over (Sp R₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ A), (∀ j, y ≫ x j = 1) → y = 1) →
    ∀ (T : Over (Sp R)) (y : T ⟶ A), (∀ j, y ≫ x j = 1) → y = 1 := by
  intro R R₀ _ _ π hπ ⟨N, hN⟩ A _ hA n D _ hD x hx h₀
  obtain ⟨K, k, hk, hK⟩ := exists_closed_equalizer D n A x fun _ => 1
  simp only [MonObj.comp_one] at hK
  have : IsProper K.hom := by
    rw [← Over.w k]
    infer_instance
  have one : ∀ T : Over (Sp R), ∃ y : T ⟶ K, y ≫ k = 1 := fun T => (hK T 1).1 fun j => by
    have := hx j
    simp [Hom.one_def]
  have hkx := (hK K k).2 ⟨𝟙 K, Category.id_comp k⟩
  obtain ⟨e, he⟩ := one (𝟙_ _)
  have : Mono K.hom := mono_of_proper π hπ N hN K.hom e.left fun T d t hd => by
    let d' : Over.mk ((Over.mk t).hom ≫ spMap π) ⟶ K := Over.homMk d hd
    have h₁ : d' ≫ k = 1 := h₀ (Over.mk t) _ fun j => by rw [Category.assoc, hkx, MonObj.comp_one]
    have : d' ≫ k = d' ≫ toUnit K ≫ e ≫ k := by
      rw [h₁, he, MonObj.comp_one, MonObj.comp_one]
    rw [← cancel_mono k.left, Category.assoc, Category.assoc]
    exact congrArg (·.left) this
  intro T y hy
  obtain ⟨y₁, hy₁⟩ := (hK T y).1 hy
  obtain ⟨y₂, hy₂⟩ := one T
  rw [← hy₁, ← hy₂, Over.OverMorphism.ext ((cancel_mono K.hom).1 ((Over.w y₁).trans (Over.w y₂).symm))]

end GlobalTheory.KernelThickening
