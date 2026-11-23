import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem norm_map_of_basis {A A' B B' : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (ρ : A →+* A') (ψ : B →+* B')
    (hc : ∀ a, ψ (algebraMap A B a) = algebraMap A' B' (ρ a)) {J : Type} [Fintype J] [DecidableEq J]
    (e : Module.Basis J A B) (e' : Module.Basis J A' B') (he : ∀ i, ψ (e i) = e' i) (f : B) :
    Algebra.norm A' (ψ f) = ρ (Algebra.norm A f) := by
  rw [Algebra.norm_eq_matrix_det e, Algebra.norm_eq_matrix_det e', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have h : ψ f * e' j = ∑ k, ρ (e.repr (f * e j) k) • e' k := by
    rw [← he j, ← map_mul]
    conv_lhs => rw [← e.sum_repr (f * e j)]
    simp only [map_sum, Algebra.smul_def, map_mul, hc, he]
  rw [h, e'.repr_sum_self]

theorem exists_basis_of_ringEquiv {S₀ A T₀ B : Type} [CommRing S₀] [CommRing A] [CommRing T₀]
    [CommRing B] [Algebra S₀ A] [Algebra S₀ T₀] [Algebra A B] {J : Type}
    (c : Module.Basis J S₀ T₀) (Φ : A ⊗[S₀] T₀ ≃+* B) (hΦ : ∀ a, Φ (a ⊗ₜ 1) = algebraMap A B a) :
    ∃ e : Module.Basis J A B, ∀ i, e i = Φ (1 ⊗ₜ c i) := by
  let L : A ⊗[S₀] T₀ ≃ₗ[A] B := Φ.toAddEquiv.toLinearEquiv (fun a x => by
    show Φ (a • x) = a • Φ x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← hΦ]
    rfl)
  exact ⟨(Algebra.TensorProduct.basis A c).map L, fun i => by
    simp [L, Algebra.TensorProduct.basis_apply]⟩

theorem exists_basis_Gamma {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁] {J : Type}
    [Fintype J] (c' : Module.Basis J R R₁) :
    letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
    Nonempty (Module.Basis J Γ(Sp R, ⊤) Γ(Sp R₁, ⊤)) := by
  letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  let σ : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let σ₁ : Γ(Sp R₁, ⊤) ≃+* R₁ := (Scheme.ΓSpecIso (CommRingCat.of R₁)).commRingCatIsoToRingEquiv
  have hnat : ∀ a, σ₁ (algebraMap Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) a) = algebraMap R R₁ (σ a) := fun a => by
    have h := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R₁)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [AffDesc.appTop_eq_appLE] at h
    exact h
  let E : Γ(Sp R₁, ⊤) ≃ₗ[Γ(Sp R, ⊤)] (J → Γ(Sp R, ⊤)) :=
    { toFun := fun y i => σ.symm (c'.repr (σ₁ y) i)
      invFun := fun g => σ₁.symm (∑ i, σ (g i) • c' i)
      map_add' := fun y y' => by funext i; simp
      map_smul' := fun a y => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def, map_mul, hnat, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
          smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
      left_inv := fun y => by
        simp only [RingEquiv.apply_symm_apply, c'.sum_repr, RingEquiv.symm_apply_apply]
      right_inv := fun g => by
        funext i
        simp only [RingEquiv.apply_symm_apply, c'.repr_sum_self, RingEquiv.symm_apply_apply] }
  exact ⟨Module.Basis.ofEquivFun E⟩

theorem mem_primeIdealOf_iff' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (s : Γ(X, U)) : s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by
  have h : (hU.primeIdealOf x : Spec Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s ↔
      x.1 ∈ X.basicOpen s := by
    conv_rhs => rw [← hU.fromSpec_primeIdealOf x]
    rfl
  rw [← h, hU.fromSpec_preimage_basicOpen]
  exact not_not.symm

end GlobalTheory.Mum.NormBC

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem exists_norm_basicOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁)
    (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → ∀ (V : X.Opens),
    IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ f : Γ(X₁, b ⁻¹ᵁ V), ∃ n : Γ(X, V),
    ∀ x : X, x ∈ X.basicOpen n ↔ x ∈ V ∧ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
  intro R R₁ _ _ _ _ _ X X₁ p p₁ b H V hVc hVq f
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨0, fun x => ?_⟩
    exact absurd (Subsingleton.elim _ _ : (p x).asIdeal = ⊤) (p x).isPrime.ne_top
  let c' := Module.Free.chooseBasis R R₁
  letI a0 : Algebra Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) :=
    ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  obtain ⟨c⟩ := exists_basis_Gamma c'
  letI aX : ∀ U : X.Opens, Algebra Γ(Sp R, ⊤) Γ(X, U) := fun U => (p.appLE ⊤ U le_top).hom.toAlgebra
  letI aB : ∀ U : X.Opens, Algebra Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) :=
    fun U => (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have key : ∀ U : X.Opens, IsIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
      (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)) →
      ∃ e : Module.Basis (Module.Free.ChooseBasisIndex R R₁) Γ(X, U) Γ(X₁, b ⁻¹ᵁ U),
        ∀ i, e i = (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom (c i) := by
    intro U hU
    let Φ := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(X, U) Γ(Sp R₁, ⊤)).isoPushout.hom ≫
      pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
        (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)
    have : IsIso Φ := by dsimp only [Φ]; infer_instance
    let Φe : Γ(X, U) ⊗[Γ(Sp R, ⊤)] Γ(Sp R₁, ⊤) ≃+* Γ(X₁, b ⁻¹ᵁ U) :=
      (asIso Φ).commRingCatIsoToRingEquiv
    have fΦ : ∀ a t, Φe (a ⊗ₜ t) =
        (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom a * (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom t :=
      fun a t => AffDesc.isoPushout_desc_tmul _ _ _ a t
    obtain ⟨e, he⟩ := exists_basis_of_ringEquiv c Φe (fun a => by rw [fΦ, map_one, _root_.mul_one]; rfl)
    exact ⟨e, fun i => by rw [he, fΦ, map_one, _root_.one_mul]⟩
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Flat (spMap (algebraMap R R₁)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  obtain ⟨e, he⟩ := key V (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hVc hVq)
  refine ⟨Algebra.norm Γ(X, V) f, fun x => ?_⟩
  by_cases hxV : x ∈ V
  swap
  · exact ⟨fun h => absurd (X.basicOpen_le _ h) hxV, fun h => absurd h.1 hxV⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ V := hUV
  haveI : IsAffineHom b := MorphismProperty.of_isPullback H.flip inferInstance
  have hU₁ : IsAffineOpen (b ⁻¹ᵁ U) := hU.preimage b
  obtain ⟨e', he'⟩ := key U (isIso_pushoutSection_of_isAffineOpen H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hUV₁ : b ⁻¹ᵁ U ≤ b ⁻¹ᵁ V := b.preimage_mono hUV'
  let ρ := X.presheaf.map (homOfLE hUV').op
  let ψ := X₁.presheaf.map (homOfLE hUV₁).op
  have hn : Algebra.norm Γ(X, U) (ψ.hom f) = ρ.hom (Algebra.norm Γ(X, V) f) := by
    refine norm_map_of_basis ρ.hom ψ.hom (fun a => ?_) e e' (fun i => ?_) f
    · change (b.appLE V _ le_rfl ≫ X₁.presheaf.map _).hom a = (X.presheaf.map _ ≫ b.appLE U _ le_rfl).hom a
      rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    · rw [he, he']
      exact congrArg (fun φ => CommRingCat.Hom.hom φ (c i)) (Scheme.Hom.appLE_map p₁ _ _)
  haveI : Module.Free Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Free.of_basis e'
  haveI : Module.Finite Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Finite.of_basis e'
  have I := GlobalTheory.T.norm_not_mem_iff_forall_over_not_mem Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) (ψ.hom f) (hU.primeIdealOf ⟨x, hxU⟩)
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec b hU hU₁ le_rfl
  have hpt : ∀ Q, b (hU₁.fromSpec Q) = hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) Q) :=
    fun Q => by rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have hfib : (∀ Q : PrimeSpectrum Γ(X₁, b ⁻¹ᵁ U),
      Q.asIdeal.comap (algebraMap Γ(X, U) Γ(X₁, b ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal →
        ψ.hom f ∉ Q.asIdeal) ↔ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
    constructor
    · intro h z hz
      have hzU : z ∈ b ⁻¹ᵁ U := by show b z ∈ U; rw [hz]; exact hxU
      have hzf : z ∈ X₁.basicOpen (ψ.hom f) := by
        by_contra hcon
        have hm := (mem_primeIdealOf_iff' hU₁ ⟨z, hzU⟩ (ψ.hom f)).2 hcon
        refine h _ ?_ hm
        have e1 : hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) (hU₁.primeIdealOf ⟨z, hzU⟩)) =
            hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) :=
          (hpt _).symm.trans (by rw [hU₁.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact hz)
        exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective e1)
      rw [Scheme.basicOpen_res] at hzf
      exact hzf.2
    · intro h Q hQ hfQ
      have hz := h (hU₁.fromSpec Q) ((hpt Q).trans ((congrArg hU.fromSpec (PrimeSpectrum.ext hQ)).trans
        (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)))
      have hzU : hU₁.fromSpec Q ∈ b ⁻¹ᵁ U := by
        have : hU₁.fromSpec Q ∈ Set.range hU₁.fromSpec := ⟨Q, rfl⟩
        rwa [hU₁.range_fromSpec] at this
      have hz' : hU₁.fromSpec Q ∈ X₁.basicOpen (ψ.hom f) := by
        rw [Scheme.basicOpen_res]; exact ⟨hzU, hz⟩
      have hz'' : Q ∈ hU₁.fromSpec ⁻¹ᵁ X₁.basicOpen (ψ.hom f) := hz'
      rw [hU₁.fromSpec_preimage_basicOpen] at hz''
      exact hz'' hfQ
  have hbx : x ∈ X.basicOpen (Algebra.norm Γ(X, V) f) ↔
      Algebra.norm Γ(X, U) (ψ.hom f) ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    rw [mem_primeIdealOf_iff', not_not, hn, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hxU, h⟩, fun h => h.2⟩
  rw [hbx, I, hfib]
  exact ⟨fun h => ⟨hxV, h⟩, fun h => h.2⟩

end GlobalTheory.Mum.NormBC
