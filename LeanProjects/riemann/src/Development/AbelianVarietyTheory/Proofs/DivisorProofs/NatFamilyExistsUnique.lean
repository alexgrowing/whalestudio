import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

abbrev locAlg (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (s : D) :
    D →ₐ[R] Localization.Away s :=
  IsScalarTower.toAlgHom R D (Localization.Away s)

theorem sm_loc_of_mem {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} (W : K → X.left.Opens)
    (hW : ⨆ i, W i = ⊤) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (P : PrimeSpectrum D) :
    ∃ s : D, s ∉ P.asIdeal ∧ Sm W (spOver (locAlg R s) ≫ x) := by
  have h1 : x.left.base P ∈ (⨆ i, W i) := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp h1
  obtain ⟨V, ⟨s, rfl⟩, hPV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := P)
      (u := (x.left ⁻¹ᵁ W i).1) hi (x.left ⁻¹ᵁ W i).isOpen
  refine ⟨s, hPV, i, fun q _ ↦ ?_⟩
  have hq : (spMap (algebraMap D (Localization.Away s))).base q ∈ PrimeSpectrum.basicOpen s := by
    change s ∉ (PrimeSpectrum.comap (algebraMap D (Localization.Away s)) q).asIdeal
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  exact hVU hq

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

def awR (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away a →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b
  commutes' r := by
    change IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away a),
      IsLocalization.Away.awayToAwayRight_eq, ← IsScalarTower.algebraMap_apply]

def awL (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away b →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a
  commutes' r := by
    change IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away b),
      IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply]

theorem awR_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awR R a b).comp (locAlg R a) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayRight_eq (P := Localization.Away (a * b)) a b z

theorem awL_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awL R a b).comp (locAlg R b) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayLeft_eq (P := Localization.Away (a * b)) b a z

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem natFamily_existsUnique : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → τ E' (θ.comp ψ) = θ (τ E ψ)) → ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ x) → τ E ψ = ψ d := by
  intro R _ X K W hW D _ _ x τ hτ
  let S : Set D := {s | Sm W (spOver (locAlg R s) ≫ x)}
  have key : ∀ (s : D), s ∈ S → ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
      (θ : Localization.Away s →ₐ[R] E), θ.comp (locAlg R s) = ψ → θ (τ _ (locAlg R s)) = τ E ψ := by
    intro s hs E _ _ ψ θ h
    rw [← hτ _ _ _ θ hs, h]
  have span : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsM, hs⟩ := sm_loc_of_mem W hW x ⟨M, hM.isPrime⟩
    exact hsM (hSM (Ideal.subset_span hs))
  let v : ∀ a : S, Localization.Away a.1 := fun a ↦ τ _ (locAlg R a.1)
  obtain ⟨d, hd, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S span v (fun a b ↦ by
    have e1 := key a a.2 _ _ (awR R (a : D) b) (awR_comp R _ _)
    have e2 := key b b.2 _ _ (awL R (a : D) b) (awL_comp R _ _)
    exact e1.trans e2.symm)
  refine ⟨d, fun E _ _ ψ hψ ↦ ?_, fun d' hd' ↦ hu d' fun a ↦ (hd' _ (locAlg R a.1) a.2).symm⟩
  have spanE : Ideal.span (ψ '' S) = ⊤ := by
    rw [← Ideal.map_span, span, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ spanE
  funext ⟨t, s, hs, ht⟩
  subst ht
  let θ : E →ₐ[R] Localization.Away (ψ s) := locAlg R (ψ s)
  let θ' : Localization.Away s →ₐ[R] Localization.Away (ψ s) := Localization.awayMapₐ ψ s
  have hc : θ'.comp (locAlg R s) = θ.comp ψ := AlgHom.ext fun z ↦ by
    simp [θ', θ, Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
  change θ (τ E ψ) = θ (ψ d)
  have e : τ _ (locAlg R s) = algebraMap D _ d := (hd ⟨s, hs⟩).symm
  rw [← hτ E _ ψ θ hψ, ← hc, ← key s hs _ _ θ' rfl, e]
  exact DFunLike.congr_fun hc d

end GlobalTheory.PtExt
