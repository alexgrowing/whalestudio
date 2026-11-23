import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem isReduced_of_pReg_of_factor (p : ℕ) {Y₀ Y : Scheme.{0}} [IsReduced Y₀] (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0)
    (hfac : ∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) :
    IsReduced Y := by

  have haff : ∀ (V : Y.Opens), IsAffineOpen V → ∀ g : Γ(Y, V), IsNilpotent g → g = 0 := by
    intro V hV g hg
    let q : Γ(Y, V) := (p : Γ(Y, V))
    let O := Y.basicOpen q
    let ρ : Γ(Y, V) →+* Γ(Y, O) := (Y.presheaf.map (homOfLE (Y.basicOpen_le q)).op).hom
    letI : Algebra Γ(Y, V) Γ(Y, O) := ρ.toAlgebra
    haveI : IsLocalization.Away q Γ(Y, O) := hV.isLocalization_basicOpen q
    have hu : IsUnit ((p : ℕ) : Γ(O.toScheme, ⊤)) := by
      have h1 : IsUnit (algebraMap Γ(Y, V) Γ(Y, O) q) := IsLocalization.Away.algebraMap_isUnit q
      rw [map_natCast] at h1
      have := h1.map (O.topIso.inv.hom)
      rwa [map_natCast] at this
    obtain ⟨f₀, hf₀⟩ := hfac O.toScheme O.ι hu
    haveI : IsOpenImmersion (f₀ ≫ i) := hf₀ ▸ inferInstance
    haveI : IsOpenImmersion f₀ := IsOpenImmersion.of_comp f₀ i
    haveI : IsReduced O.toScheme := isReduced_of_isOpenImmersion f₀
    haveI : _root_.IsReduced Γ(Y, O) :=
      isReduced_of_injective (O.topIso.inv.hom) (O.topIso.commRingCatIsoToRingEquiv.symm.injective)
    have h0 : algebraMap Γ(Y, V) Γ(Y, O) g = 0 := (hg.map (algebraMap Γ(Y, V) Γ(Y, O))).eq_zero
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers q) _ g).1 h0
    have hk' : q ^ k * g = 0 := hk
    clear hk h0
    induction k with
    | zero => simpa using hk'
    | succ k ih => exact ih (hp V _ (by rw [pow_succ', _root_.mul_assoc] at hk'; exact hk'))
  refine ⟨fun U => ⟨fun f hf => ?_⟩⟩
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · rw [map_zero]
    exact haff V.1.1 V.1.2 _ (hf.map _)

theorem isReduced_normalModel_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ gs hgs _ Y s i _ _ hfl hfac
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsReduced Y₀ := GlobalTheory.isReduced_of_smooth_of_isReduced (gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s)
  have hR : ∀ a : R, (p : R) * a = 0 → a = 0 := fun a ha =>
    (mul_eq_zero.1 ha).resolve_left (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  haveI := hfl
  exact isReduced_of_pReg_of_factor p i (fun U f hf => pReg_of_flat (p := p) (s ≫ M.s) hR U f hf) hfac

end GlobalTheory.UPel.HT.ES
