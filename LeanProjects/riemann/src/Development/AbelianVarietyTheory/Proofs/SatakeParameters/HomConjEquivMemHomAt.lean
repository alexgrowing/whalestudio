import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory

theorem latSum_transport_equiv {E : Type} [Field E] [NumberField E] {H H₂ M : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] [AddCommMonoid M] (e : H ≃ₗ[𝓞 E] H₂) (A B : Submodule (𝓞 E) H)
    (A₂ B₂ : Submodule (𝓞 E) H₂) (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (hB : ∀ x, e x ∈ B₂ ↔ x ∈ B) (G : H → M) (F₂ : H₂ → M)
    (hG : ∀ x x', x - x' ∈ B → G x = G x') (hF : ∀ x, F₂ (e x) = G x) : latSum A₂ B₂ F₂ = latSum A B G := by
  have hAm : A.map (e : H →ₗ[𝓞 E] H₂) = A₂ := by
    ext y
    rw [Submodule.mem_map_equiv, ← hA, e.apply_symm_apply]
  let eA : ↥A ≃ₗ[𝓞 E] ↥A₂ := e.ofSubmodules A A₂ hAm
  have heA : ∀ x : A, ((eA x : A₂) : H₂) = e x := fun x => rfl
  have hBm : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥A₂) = B₂.comap A₂.subtype := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply, ← hB, ← heA, eA.apply_symm_apply]
  let q := Submodule.Quotient.equiv (B.comap A.subtype) (B₂.comap A₂.subtype) eA hBm
  unfold latSum
  rw [← finsum_comp_equiv q.toEquiv]
  refine finsum_congr fun z => ?_
  set r := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z with hr
  set r₂ := Function.surjInv (Submodule.Quotient.mk_surjective (B₂.comap A₂.subtype)) (q.toEquiv z) with hr₂
  have h1 : Submodule.Quotient.mk r = z := Function.surjInv_eq _ z
  have h2 : Submodule.Quotient.mk r₂ = q z := Function.surjInv_eq _ _
  have h3 : q z = Submodule.Quotient.mk (eA r) := by
    rw [← h1]; rfl
  rw [h3, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, heA] at h2
  have h4 : (r₂ : H₂) = e (e.symm r₂) := (e.apply_symm_apply _).symm
  rw [h4, hF]
  apply hG
  rw [← hB, map_sub, ← h4]
  exact h2

noncomputable def homConjEquiv {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[𝓞 E] HomE E a b where
  toFun x := γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap
  invFun x := γ'.symm.toLinearMap ∘ₗ x ∘ₗ γ.toLinearMap
  map_add' x y := by simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' r x := by
    ext y i
    simp [equiv_osmul]
  left_inv x := by ext y i; simp
  right_inv x := by ext y i; simp

theorem homConjEquiv_mem_homAt {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    homConjEquiv γ γ' x ∈ homAt S (gmap γ N) (gmap γ' N') ↔ x ∈ homAt S N N' := by
  show (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) ∈ homAt S (gmap γ N) (gmap γ' N') ↔ _
  constructor
  · intro h P hP y hy
    have h1 := h P hP (γ y) ((mem_localization_gmap P γ N _).2 (by simpa using hy))
    have h2 := (mem_localization_gmap P γ' N' _).1 h1
    simpa using h2
  · intro h P hP y hy
    have h1 := h P hP (γ.symm y) ((mem_localization_gmap P γ N _).1 hy)
    exact (mem_localization_gmap P γ' N' _).2 (by simpa using h1)

theorem mem_divLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ divLat c A₂ ↔ x ∈ divLat c A := by
  show ((c : 𝓞 E) • e x) ∈ A₂ ↔ ((c : 𝓞 E) • x) ∈ A
  rw [← map_smul, hA]

theorem mem_mulLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ mulLat c A₂ ↔ x ∈ mulLat c A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e.symm y, (hA _).1 (by rw [e.apply_symm_apply]; exact hy), ?_⟩
    apply e.injective
    rw [← hxy]
    show e ((c : 𝓞 E) • e.symm y) = (c : 𝓞 E) • y
    rw [map_smul, e.apply_symm_apply]
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e y, (hA _).2 hy, ?_⟩
    rw [← hxy]
    show (c : 𝓞 E) • e y = e ((c : 𝓞 E) • y)
    rw [map_smul]

theorem kerOf_gmap_frames : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (D cA cB : ℕ) (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (sS sT : SB → E → K), ThDist.Ok th Sa D rho rho' sS sT → ∀ (γ : UF E a) (γ' : UF E b) (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB) (κ : GLQ E a SB) (κ' : GLQ E b SB) (Ξ Ξ₂ : HomE E a b → K) (c : K), IsSdLat N → IsSdLat N' → (∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x) → (∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) * ∏ P : SB, (sS P ((LinearEquiv.det (κ P).1 : Eˣ) : E) * sT P ((LinearEquiv.det (κ' P).1 : Eˣ) : E)) = c * Ξ x) → kerOf th Sa cA cB (gmap γ.1 N) (fun P => γ.1 * (fr P * (κ P).1)) (gmap γ'.1 N') (fun P => γ'.1 * (fr' P * (κ' P).1)) Ξ₂ = c • ((rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  intro E K _ _ _ _ a b SB V V' _ _ _ _ th Sa D cA cB rho rho' sS sT hok γ γ' N fr N' fr' κ κ' Ξ Ξ₂ c hN hN' hΞ hΞ₂
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => c • φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = c • φ _
    unfold latSum
    rw [φ.map_finsum, smul_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hok.cong N fr N' fr' cB x x' hN hN' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = c • (rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹)
    rw [hok.equiv γ γ' N (fun P => fr P * (κ P).1) N' (fun P => fr' P * (κ' P).1) cB x hN hN',
      hok.det N fr N' fr' cB x κ κ' hN hN', LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp,
      LinearMap.comp_smul, smul_smul, smul_smul, hΞ₂]

end GlobalTheory
