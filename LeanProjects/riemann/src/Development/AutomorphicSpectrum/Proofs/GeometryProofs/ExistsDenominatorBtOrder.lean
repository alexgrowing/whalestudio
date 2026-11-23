import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegularStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_scalar {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of A))
    (x : Spec (CommRingCat.of B) ⟶ X) (φ : A →+* B) (hw : x ≫ π = Spec.map (CommRingCat.ofHom φ))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (hU : U ≤ π ⁻¹ᵁ ⊤) (b : A) :
    valAt x U h (π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) = φ b := by
  have h1 := Scheme.Hom.appLE_comp_appLE x π ⊤ U ⊤ hU h
  have h0 : ∀ (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (e : ⊤ ≤ q ⁻¹ᵁ ⊤),
      q = Spec.map (CommRingCat.ofHom φ) →
      q.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rintro q e rfl
    have : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [this]
    exact Scheme.ΓSpecIso_naturality _
  have h2 : (π.appLE ⊤ U hU ≫ x.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [h1]
    exact h0 _ _ hw
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) h2
  simpa [valAt] using h3

theorem QFGroup.regularAt_scalar_mul (Γ : QFGroup R T) {f : T → FractionRing R} {g : Γ.G.left} (b : R)
    (H : Γ.RegularAt f g) : Γ.RegularAt (fun t => algebraMap R (FractionRing R) b * f t) g := by
  obtain ⟨U, hg, s, hs⟩ := H
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have hU : U ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨U, hg, π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * s, fun t h => ?_⟩
  have hw : (Γ.pt t).left ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [hπ]; exact Over.w (Γ.pt t)
  have h1 := valAt_scalar π (Γ.pt t).left (algebraMap R (FractionRing R)) hw U h hU b
  have h2 := hs t h
  show _ = algebraMap R (FractionRing R) b * f t
  rw [← h1, ← h2]
  simp [valAt, map_mul]

theorem QFGroup.compactSpace (Γ : QFGroup R T) : CompactSpace Γ.G.left := by
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have : QuasiCompact π := hπ ▸ Γ.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace π

theorem QFGroup.exists_denom [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) :
    ∃ d : R, d ≠ 0 ∧ ∀ g, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g := by
  classical
  have := Γ.compactSpace
  have key : ∀ g : Γ.G.left, ∃ d : R, d ≠ 0 ∧ ∃ U : Γ.G.left.Opens, g ∈ U ∧
      ∀ g' ∈ U, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g' := by
    intro g
    obtain ⟨d, hd, U, hg, s, hs⟩ := GlobalTheory.T.exists_denominator_regular R T Γ f g
    exact ⟨d, hd, U, hg, fun g' hg' => ⟨U, hg', s, hs⟩⟩
  choose d hd U hgU hU using key
  obtain ⟨F, hF⟩ := CompactSpace.elim_nhds_subcover (fun g => (U g : Set Γ.G.left))
    (fun g => (U g).isOpen.mem_nhds (hgU g))
  refine ⟨∏ x ∈ F, d x, Finset.prod_ne_zero_iff.2 fun x _ => hd x, fun g => ?_⟩
  have hg : g ∈ ⋃ x ∈ F, (U x : Set Γ.G.left) := by rw [hF]; trivial
  simp only [Set.mem_iUnion] at hg
  obtain ⟨x, hx, hgx⟩ := hg
  have h1 := Γ.regularAt_scalar_mul (∏ y ∈ F.erase x, d y) (hU x g hgx)
  have h2 : (∏ y ∈ F, d y) = (∏ y ∈ F.erase x, d y) * d x := (Finset.prod_erase_mul F d hx).symm
  rw [h2]
  simpa [map_mul, _root_.mul_assoc] using h1

end GlobalTheory.CompanionTheory.Ar.BT

open Classical in

theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T), ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ
  have := Fintype.ofFinite T
  let δ : T → T → R := fun s h => if h = s then 1 else 0
  choose e he hreg using fun s : T =>
    Γ.exists_denom (fun h => algebraMap R (FractionRing R) (δ s h))
  have hmem : ∀ s, (∏ x, e x) • δ s ∈ Γ.btOrder ⊤ := by
    intro s
    refine Algebra.subset_adjoin ?_
    intro t g _
    have h1 := Γ.regularAt_scalar_mul (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) (hreg (t⁻¹ * s) g)
    have h2 : (∏ y, e y) = (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) * e (t⁻¹ * s) :=
      (Finset.prod_erase_mul _ e (Finset.mem_univ _)).symm
    have h3 : (fun h => algebraMap R (FractionRing R) (((∏ x, e x) • δ s) (t * h))) =
        fun h => algebraMap R (FractionRing R) (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) *
          (algebraMap R (FractionRing R) (e (t⁻¹ * s)) *
            algebraMap R (FractionRing R) (δ (t⁻¹ * s) h)) := by
      funext h
      have h4 : δ s (t * h) = δ (t⁻¹ * s) h := by
        have : t * h = s ↔ h = t⁻¹ * s := by
          constructor
          · rintro rfl; simp
          · rintro rfl; simp
        simp [δ, this]
      rw [Pi.smul_apply, h4, h2, smul_eq_mul, map_mul, map_mul, _root_.mul_assoc]
    rw [h3]
    exact h1
  refine ⟨∏ x, e x, Finset.prod_ne_zero_iff.2 fun x _ => he x, fun f => ?_⟩
  have hf : (∏ x, e x) • f = ∑ s, f s • ((∏ x, e x) • δ s) := by
    funext h
    simp [δ, Finset.sum_apply, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc, Finset.mul_sum]
  rw [hf]
  exact Subalgebra.sum_mem _ fun s _ => Subalgebra.smul_mem _ (hmem s) _
