import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.NatGlue

variable (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D]

def locMap (s : D) : D →ₐ[R] Localization.Away s := IsScalarTower.toAlgHom R D _

theorem locMap_apply (s x : D) : locMap R s x = algebraMap D (Localization.Away s) x := rfl

def locR (a b : D) : Localization.Away a →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayRight a b, fun r ↦ by
    have := IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a) (P := Localization.Away (a * b))
      a b (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

def locL (a b : D) : Localization.Away b →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayLeft b a, fun r ↦ by
    have := IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away b) (P := Localization.Away (a * b))
      b a (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

theorem locR_apply (a b : D) (x : Localization.Away a) :
    locR R a b x = IsLocalization.Away.awayToAwayRight a b x := rfl

theorem locL_apply (a b : D) (x : Localization.Away b) :
    locL R a b x = IsLocalization.Away.awayToAwayLeft b a x := rfl

theorem locR_comp (a b : D) : (locR R a b).comp (locMap R a) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locR_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayRight_eq a b x

theorem locL_comp (a b : D) : (locL R a b).comp (locMap R b) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locL_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayLeft_eq b a x

theorem awayMap_comp {E : Type} [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (s : D) :
    (IsScalarTower.toAlgHom R E (Localization.Away (φ s))).comp φ = (Localization.awayMapₐ φ s).comp (locMap R s) := by
  ext x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, locMap_apply]
  first
    | exact (IsLocalization.Away.map_eq (S := Localization.Away s) (P := Localization.Away (φ s)) s x).symm
    | simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
    | (show _ = IsLocalization.map _ (φ : D →+* E) _ _; exact (IsLocalization.map_eq _ _).symm)

theorem sm_comp {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} (y : Pt X D) {E E' : Type} [CommRing E]
    [Algebra R E] [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E') (h : Sm W (spOver ψ ≫ y)) :
    Sm W (spOver (θ.comp ψ) ≫ y) := by
  obtain ⟨i, h⟩ := h
  refine ⟨i, ?_⟩
  rw [← spOver_comp, Category.assoc]
  intro p _
  exact h (Set.mem_univ _)

theorem existsUnique_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D)
    (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E)
      (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ y) → τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ y) → τ E ψ = ψ d := by
  intro R _ X K W hW D _ _ y τ hτ

  let S : Set D := {s | ∃ i, ∀ p : PrimeSpectrum D, p ∈ PrimeSpectrum.basicOpen s → y.left.base p ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff', eq_top_iff]
    intro p _
    have hp : y.left.base p ∈ ⨆ i, W i := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    obtain ⟨_, ⟨s, rfl⟩, hps, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (y.left ⁻¹ᵁ W i).carrier) hi (y.left ⁻¹ᵁ W i).isOpen
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨s, ⟨i, fun q hq ↦ hsub hq⟩, hps⟩
  have hψ : ∀ s ∈ S, Sm W (spOver (locMap R s) ≫ y) := by
    rintro s ⟨i, hi⟩
    refine ⟨i, fun q _ ↦ hi _ ?_⟩
    show PrimeSpectrum.comap (algebraMap D (Localization.Away s)) q ∈ PrimeSpectrum.basicOpen s
    rw [PrimeSpectrum.mem_basicOpen]
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  have hcomp : ∀ a b : S,
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.1 * b.1)) a.1 b.1 (τ (Localization.Away a.1) (locMap R a.1)) =
      IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a.1 * b.1)) b.1 a.1 (τ (Localization.Away b.1) (locMap R b.1)) := by
    intro a b
    have h1 := hτ _ _ (locMap R a.1) (locR R a.1 b.1) (hψ a.1 a.2)
    have h2 := hτ _ _ (locMap R b.1) (locL R a.1 b.1) (hψ b.1 b.2)
    rw [locR_comp] at h1
    rw [locL_comp] at h2
    rw [← locR_apply R, ← locL_apply R, ← h1, ← h2]
  obtain ⟨d, hd, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S hS
    (fun a ↦ τ (Localization.Away a.1) (locMap R a.1)) hcomp
  refine ⟨d, ?_, fun d' hd' ↦ hu d' fun a ↦ (hd' _ (locMap R a.1) (hψ a.1 a.2)).symm⟩
  intro E _ _ φ hφ
  have hS' : Ideal.span ((φ : D →+* E) '' S) = ⊤ := by
    rw [← Ideal.map_span, hS, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ hS'
  funext b
  obtain ⟨b, s, hs, rfl⟩ := b
  have h1 := hτ _ _ φ (IsScalarTower.toAlgHom R E (Localization.Away (φ s))) hφ
  have h2 := hτ _ _ (locMap R s) (Localization.awayMapₐ φ s) (hψ s hs)
  rw [awayMap_comp, h2, ← hd ⟨s, hs⟩, ← locMap_apply R, ← AlgHom.comp_apply, ← awayMap_comp] at h1
  exact h1.symm

end GlobalTheory.PtExt.NatGlue
