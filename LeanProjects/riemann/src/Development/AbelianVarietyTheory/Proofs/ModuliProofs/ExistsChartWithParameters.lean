import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.RelChart

open GlobalTheory.TangentOrigin

theorem evalPt_appLE {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem top_le_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (v : Sp R ⟶ X) (φ : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage]
  exact fun _ hp => e (hV hp)

theorem dual_ext {P R : Type} [CommRing P] [CommRing R] (ψ : P →+* R) (hψ : ψ.Etale)
    (F F' : R →+* DualNumber ℂ) (h : ∀ a, F (ψ a) = F' (ψ a)) (h0 : ∀ r, fstC (F r) = fstC (F' r)) : F = F' := by
  let _ := ψ.toAlgebra
  let _ : Algebra P (DualNumber ℂ) := (F'.comp ψ).toAlgebra
  have _ : Algebra.Etale P R := hψ
  let G : R →ₐ[P] DualNumber ℂ := { F with commutes' := h }
  let G₀ : R →ₐ[P] DualNumber ℂ := { F' with commutes' := fun _ => rfl }
  have hnil : IsNilpotent (RingHom.ker fstC) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' fstC hnil G G₀ h0
  exact RingHom.ext fun r => AlgHom.congr_fun hG r

theorem exists_chart_with_parameters :
    (∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x) → (∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') := by
  classical
  intro hring m g Z X p B y b₀ z₀ hp hB hb₀ hy hz₀
  obtain ⟨V, hV, U, hU, hz, hle, hsm⟩ :=
    hp.exists_isStandardSmoothOfRelativeDimension (z₀ (default : PrimeSpectrum ℂ))
  obtain ⟨ψ, hψC, hψ⟩ := hsm.exists_etale_mvPolynomial
  have hC : ∀ a, ψ (MvPolynomial.C a) = (p.appLE V U hle).hom a := fun a => RingHom.congr_fun hψC a
  have hzU : ⊤ ≤ z₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem z₀ U).2 hz
  have hy₀ : ⊤ ≤ y b₀ ⁻¹ᵁ V := hz₀ ▸ top_le_comp z₀ p hle hzU
  let φ : (Fin m → ℂ) → (Γ(X, V) →+* ℂ) := fun b =>
    if h : ⊤ ≤ y b ⁻¹ᵁ V then evalPt (y b) V h else evalPt (y b₀) V hy₀
  have hφ : ∀ b, ⊤ ≤ y b ⁻¹ᵁ V → ∀ a, φ b a = valAt' (y b) V a := fun b h a => by
    simp only [φ, dif_pos h, valAt'_eq_evalPt _ _ h]
  have hover : ∀ b (x : Sp ℂ ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = y b →
      ∀ a, evalPt x U hx (ψ (MvPolynomial.C a)) = φ b a := fun b x hx hxb a => by
    rw [hφ b (hxb ▸ top_le_comp x p hle hx), hC, ← valAt'_eq_evalPt, valAt'_appLE _ _ _ _ _ _ hx, hxb]
  obtain ⟨N, σ, n, f, O, hN, hO, h₀, hσd, hσ, hrec⟩ := hring m g Γ(X, V) Γ(Z, U) ψ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ V} φ b₀
    (evalPt z₀ U hzU) hψ (hy V 0).1 ⟨hb₀, hy₀⟩
    (fun a => (hy V a).2.congr fun b hb => hφ b hb.2 a) (hover b₀ z₀ hzU hz₀)
  choose s hsU hs using fun q => exists_evalPt_eq hU (σ q)
  have hval : ∀ q a, valAt' (s q) U a = σ q a := fun q a => by
    rw [valAt'_eq_evalPt _ _ (hsU q), hs]
  refine ⟨U, fun i => ψ (MvPolynomial.X i), n, f, N, O, s, hN, hO, hzU, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [valAt'_eq_evalPt _ _ hzU] using h₀
  · intro W a
    refine holFamily_of_affine valAt'_rules N Z s (fun q _ => ⟨U, hU, hsU q, ?_, fun r => ?_⟩) W a
    · simp only [hsU, and_true]
      exact hN
    · simp only [hsU, and_true, hval]
      exact hσd r
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hσ q hq
    refine ⟨ext_evalPt hV (top_le_comp _ p hle (hsU q)) h1.2 (RingHom.ext fun a => ?_), hsU q,
      fun i => (hval _ _).trans (h3 i)⟩
    rw [← evalPt_appLE _ p V U hle a (hsU q), hs, ← hC, h2, hφ _ h1.2, valAt'_eq_evalPt]
  · intro b x hxb hx hxO
    simp only [valAt'_eq_evalPt _ _ hx] at hxO ⊢
    obtain ⟨h1, h2⟩ := hrec b (evalPt x U hx) (hover b x hx hxb) hxO
    exact ⟨h1, ext_evalPt hU (hsU _) hx ((hs _).trans h2)⟩
  · intro v v' h h' hvp hv0 hvt
    refine ext_evalPt hU h h' (dual_ext ψ hψ _ _ (fun a => ?_) fun r => ?_)
    · have : (evalPt v U h).comp ψ = (evalPt v' U h').comp ψ := by
        refine MvPolynomial.ringHom_ext (fun c => ?_) hvt
        simp only [RingHom.comp_apply, hC]
        rw [evalPt_appLE v p V U hle c h (top_le_comp v p hle h),
          evalPt_appLE v' p V U hle c h' (top_le_comp v' p hle h')]
        simp only [hvp]
      exact RingHom.congr_fun this a
    · rw [← evalPt_spMap_comp fstC v U h ((top_le_preimage_iff v U).1 h),
        ← evalPt_spMap_comp fstC v' U h' ((top_le_preimage_iff v' U).1 h')]
      have hv0' : spMap fstC ≫ v = spMap fstC ≫ v' := hv0
      simp only [hv0']

end GlobalTheory.RelChart
