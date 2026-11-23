import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocVal

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_mul {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_add {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq x U h, map_add]

theorem valR_pow {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) (n : ℕ) : valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_eq x U h, map_pow]

theorem valR_one {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR_eq x U h, map_one]

theorem valR_res {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  rw [valR_eq x V h, valR_eq x U (h.trans (x.preimage_mono e))]
  congr 1
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_field_of_le : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ Z),
    ⊤ ≤ ξ ⁻¹ᵁ U → ∀ (d : Fld Z), IsField U d → ∀ (D : F → F), (∀ x y, D (x + y) = D x + D y) →
    (∀ x y, D (x * y) = x * D y + y * D x) → (∀ f : Γ(Z, U), valR ξ U (d U f) = D (valR ξ U f)) →
    ∀ O : Z.Opens, O ≤ U → ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h : Γ(Z, O), valR ξ O (d O h) = D (valR ξ O h) := by
  intro Z U hU F _ ξ _ d hd D _ hDm hDU O hOU hξO h
  obtain ⟨p₀⟩ : Nonempty (Sp F) := inferInstance
  have hp₀ : ξ.base p₀ ∈ O := hξO (Set.mem_univ p₀)
  obtain ⟨g, hgO, hg⟩ := hU.exists_basicOpen_le (V := O) ⟨_, hp₀⟩ (hOU hp₀)
  set B := Z.basicOpen g
  have hBU : B ≤ U := hgO.trans hOU
  have hξB : ⊤ ≤ ξ ⁻¹ᵁ B := by
    intro p _
    have : p = p₀ := Subsingleton.elim _ _
    subst this
    exact hg
  have := hU.isLocalization_basicOpen g
  obtain ⟨m, f, hf⟩ := IsLocalization.Away.surj g (resG Z hgO h)
  have hf' : resG Z hgO h * resG Z hBU g ^ m = resG Z hBU f := hf

  have hgu : IsUnit (resG Z hBU g) := Z.toRingedSpace.isUnit_res_basicOpen g
  have hg0 : valR ξ U g ≠ 0 := by
    obtain ⟨u, hu⟩ := hgu
    intro h0
    have e1 := congrArg (valR ξ B) u.mul_inv
    rw [valR_mul ξ B hξB, valR_one ξ B hξB, hu, valR_res ξ hBU hξB, h0, zero_mul] at e1
    exact zero_ne_one e1

  have hL := congrArg (d B) hf'
  rw [hd.2.1 B hBU, ← map_pow, hd.2.2 U B hBU le_rfl, hd.2.2 U B hBU le_rfl, hd.2.2 O B hgO hOU] at hL
  have hV := congrArg (valR ξ B) hL
  rw [valR_add ξ B hξB, valR_mul ξ B hξB, valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB,
    valR_res ξ hBU hξB, valR_res ξ hBU hξB, hDU, hDU] at hV
  have hfv : valR ξ U f = valR ξ O h * valR ξ U g ^ m := by
    have := congrArg (valR ξ B) hf'
    rw [valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB, valR_pow ξ B hξB, valR_res ξ hBU hξB] at this
    exact this.symm
  rw [hfv, hDm, valR_pow ξ U (hξB.trans (ξ.preimage_mono hBU))] at hV
  have key : valR ξ U g ^ m * (valR ξ B (resG Z hgO (d O h)) - D (valR ξ O h)) = 0 := by
    linear_combination hV
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (pow_eq_zero_iff'.1 h1).1 hg0
  · rw [← valR_res ξ hgO hξB]
    exact sub_eq_zero.1 h1

end GlobalTheory.LocVal
