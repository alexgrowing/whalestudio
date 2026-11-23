import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfComp

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.ThickLoc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}}
  {s : X ⟶ Sp R} (T : Thick κ s) (b : T.B)

abbrev locJ : Ideal (Localization.Away b) := T.J.map (algebraMap T.B (Localization.Away b))

def locφ₀ : T.B₀ →+* Localization.Away b ⧸ locJ T b :=
  T.π.liftOfSurjective T.surj
    ⟨(Ideal.Quotient.mk (locJ T b)).comp (algebraMap T.B (Localization.Away b)), fun x hx ↦ by
      rw [RingHom.mem_ker] at hx ⊢
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ((T.ker x).1 hx))⟩

theorem locφ₀_π (x : T.B) :
    locφ₀ T b (T.π x) = Ideal.Quotient.mk (locJ T b) (algebraMap T.B (Localization.Away b) x) := by
  unfold locφ₀
  exact RingHom.liftOfSurjective_comp_apply _ _ _ x

@[reducible] def loc : Thick κ s where
  B := Localization.Away b
  J := locJ T b
  δ := DPLoc.dp (Submonoid.powers b) T.δ
  nil := DPLoc.isNilDP _ _ T.nil
  dp := by
    rw [IsScalarTower.algebraMap_eq R T.B (Localization.Away b)]
    exact IsDPMorphism.comp _ (DPLoc.isDPMorphism _ T.δ) T.dp
  B₀ := Localization.Away b ⧸ locJ T b
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap (locφ₀ T b) ≫ T.x
  w := by
    rw [Category.assoc, T.w, ← Cris.spMap_comp]
    congr 1
    ext r
    simp only [RingHom.comp_apply, locφ₀_π]
    rw [← IsScalarTower.algebraMap_apply]

def toLoc : T ⟶ loc T b where
  φ := IsScalarTower.toAlgHom R T.B (Localization.Away b)
  φ₀ := locφ₀ T b
  comm := locφ₀_π T b
  dp := DPLoc.isDPMorphism (S := Localization.Away b) (Submonoid.powers b) T.δ
  pt := rfl

variable {T b} {S : Thick κ s} (u : T ⟶ S) (hu : IsUnit (u.φ b))

def liftφ : Localization.Away b →ₐ[R] S.B where
  toRingHom := IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R T.B (Localization.Away b)]
    exact (IsLocalization.Away.lift_eq b (g := (u.φ : T.B →+* S.B)) hu _).trans (u.φ.commutes r)

theorem liftφ_algebraMap (x : T.B) :
    liftφ u hu (algebraMap T.B (Localization.Away b) x) = u.φ x := by
  show IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
      (algebraMap T.B (Localization.Away b) x) = u.φ x
  exact IsLocalization.Away.lift_eq b hu x

theorem liftφ_dp : IsDPMorphism (DPLoc.dp (S := Localization.Away b) (Submonoid.powers b) T.δ) S.δ
    (liftφ u hu : Localization.Away b →+* S.B) := by
  have h : (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
      (u.φ : T.B →+* S.B) :=
    RingHom.ext fun x => liftφ_algebraMap u hu x
  exact DPLoc.isDPMorphism_of_comp (S := Localization.Away b) (Submonoid.powers b) T.δ S.δ _
    (by rw [h]; exact u.dp)

def liftφ₀ : Localization.Away b ⧸ locJ T b →+* S.B₀ :=
  Ideal.Quotient.lift _ (S.π.comp (liftφ u hu : Localization.Away b →+* S.B)) fun _ ha ↦
    (S.ker _).2 ((liftφ_dp u hu).1 (Ideal.mem_map_of_mem _ ha))

def lift : loc T b ⟶ S where
  φ := liftφ u hu
  φ₀ := liftφ₀ u hu
  comm _ := rfl
  dp := liftφ_dp u hu
  pt := by
    have : (liftφ₀ u hu).comp (locφ₀ T b) = u.φ₀ := RingHom.ext fun x ↦ by
      obtain ⟨x, rfl⟩ := T.surj x
      rw [RingHom.comp_apply, locφ₀_π, u.comm, ← liftφ_algebraMap u hu]
      rfl
    change spMap (liftφ₀ u hu) ≫ spMap (locφ₀ T b) ≫ T.x = S.x
    rw [← Category.assoc, ← Cris.spMap_comp, this, u.pt]

theorem exists_localization : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (s : X ⟶ Sp R) (T : Thick κ s) (b : T.B), ∃ (T' : Thick κ s) (l : T ⟶ T'), IsUnit (l.φ b) ∧ (∀ y : T'.B, ∃ (n : ℕ) (x : T.B), y * l.φ b ^ n = l.φ x) ∧ (∀ x : T.B, l.φ x = 0 → ∃ n : ℕ, b ^ n * x = 0) ∧ ∀ (S : Thick κ s) (u : T ⟶ S), IsUnit (u.φ b) → ∃! v : T' ⟶ S, l ≫ v = u := by
  intro R _ I κ X s T b
  refine ⟨loc T b, toLoc T b, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit b
  · intro y
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers b) y
    obtain ⟨n, hn⟩ := m.2
    refine ⟨n, a, ?_⟩
    change y * algebraMap T.B (Localization.Away b) b ^ n = algebraMap T.B (Localization.Away b) a
    rw [← map_pow, show b ^ n = ↑m from hn]
    exact hm
  · intro x hx
    change algebraMap T.B (Localization.Away b) x = 0 at hx
    obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) x).1 hx
    exact ⟨n, hm⟩
  · intro S u hu
    refine ⟨lift u hu, ?_, ?_⟩
    · ext c
      simp only [Thick.comp_φ]
      exact liftφ_algebraMap u hu c
    · intro v hv
      have h : (v.φ : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
          (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) := by
        ext c
        have hc : (toLoc T b ≫ v).φ c = u.φ c := by rw [hv]
        simp only [Thick.comp_φ] at hc
        show v.φ (algebraMap T.B (Localization.Away b) c) =
          liftφ u hu (algebraMap T.B (Localization.Away b) c)
        exact hc.trans (liftφ_algebraMap u hu c).symm
      ext y
      exact RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers b) h) y

end GlobalTheory.ThickLoc
