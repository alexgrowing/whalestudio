import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.CoordUniq

section Lin

variable {K : Type} [Field K] {m n : ℕ}

theorem tri_of_mul {T₁ T₂ M : Fin m → Fin m → K} (h₁ : ∀ i k, i < k → T₁ i k = 0) (h₂ : ∀ i k, i < k → T₂ i k = 0)
    (hd : ∀ i, T₂ i i ≠ 0) (h : ∀ i k, T₁ i k = ∑ j, T₂ i j * M j k) (i : Fin m) : ∀ k, i < k → M i k = 0 := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro k hk
    have e := h i k
    rw [h₁ i k hk, Finset.sum_eq_single i (fun j _ hj => by
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [ih j hj k (hj.trans hk), mul_zero]
      · rw [h₂ i j hj, zero_mul]) (by simp)] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (hd i)

theorem diag_of_mul {T₂ M : Fin m → Fin m → K} (h₂ : ∀ i k, i < k → T₂ i k = 0) (hM : ∀ i k, i < k → M i k = 0)
    (i : Fin m) : ∑ j, T₂ i j * M j i = T₂ i i * M i i :=
  Finset.sum_eq_single i (fun j _ hj => by
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hM j i hj, mul_zero]
    · rw [h₂ i j hj, zero_mul]) (by simp)

theorem indep_of_tri {T : Fin m → Fin m → K} (h : ∀ i k, i < k → T i k = 0) (hd : ∀ i, T i i ≠ 0)
    {e : Fin m → Fin n → K} (hg : ∀ a : Fin m → K, ∑ i, a i • ∑ j, T i j • e j = 0 → a = 0)
    {b : Fin m → K} (hb : ∑ j, b j • e j = 0) : b = 0 := by
  have hdet : IsUnit (Matrix.of T).det := by
    rw [Matrix.det_of_isLowerTriangular (Matrix.of T) (fun i k hk => h i k hk)]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have e1 : Matrix.vecMul (Matrix.vecMul b (Matrix.of T)⁻¹) (Matrix.of T) = b := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have e2 := hg (Matrix.vecMul b (Matrix.of T)⁻¹) (by
    rw [← hb]
    conv_rhs => rw [← e1]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    rfl)
  rw [← e1, e2, Matrix.zero_vecMul]

end Lin

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_matrix {R : Type} [CommRing R] [IsLocalRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ f₂ : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ M : Fin (Dw.mult τ) → Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∃ T₁ T₂ : Fin (Dw.mult τ) → Fin (Dw.mult τ) → k,
        (∀ i, T₁ i i = t₁ τ i) ∧ (∀ i, T₂ i i = t₂ τ i) ∧ (∀ i k, i < k → T₁ i k = 0) ∧ (∀ i k, i < k → T₂ i k = 0) ∧
          ∀ i k, T₁ i k = ∑ j, T₂ i j * ψ (M j k) := by
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan τ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan τ i)
  choose M hM using fun i => (f₁.basis τ _ (f₂.tan τ i) (f₂.eig τ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v τ = fun j => vec Z.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  refine ⟨M, fun {k} _ ψ φ' x' g t₁ t₂ h₁ h₂ => ?_⟩
  obtain ⟨rfl, rfl, h₁⟩ := h₁
  obtain ⟨-, -, h₂⟩ := h₂
  choose T₁ a₁ b₁ c₁ using h₁ τ
  choose T₂ a₂ b₂ c₂ using h₂ τ
  letI : Algebra R k := ψ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  change ∀ cc, vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec Z.t x xc cc at hv
  choose G hG using fun i => vec_exists hx' _ (g.tan τ i)
  have d₁ : ∀ i, G i = ∑ j, T₁ i j • (ψ ∘ e₁ j) := fun i => by
    have := c₁ i
    simp only [he₁, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have d₂ : ∀ i, G i = ∑ j, T₂ i j • (ψ ∘ e₂ j) := fun i => by
    have := c₂ i
    simp only [he₂, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have hind : ∀ a : Fin (Dw.mult τ) → k, ∑ i, a i • G i = 0 → a = 0 := fun a ha => by
    have hb := g.basis τ _ (vec_tan hx' 0) ((vec_eig_iff hx' _ _).2 (Submodule.zero_mem _))
    rw [show g.v τ = fun j => vec Z.t _ xc' (G j) from funext hG] at hb
    exact hb.unique ((comb_iff hx' _ _ _).2 ha.symm) ((comb_iff hx' _ _ _).2 (by simp))
  refine ⟨T₁, T₂, a₁, a₂, b₁, b₂, fun i k' => ?_⟩
  have := indep_of_tri b₁ (fun i => a₁ i ▸ (t₁ τ i).ne_zero) (e := fun j => ψ ∘ e₁ j)
    (fun a ha => hind a (by simpa only [d₁] using ha))
    (b := fun k' => T₁ i k' - ∑ j, T₂ i j * ψ (M j k')) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← d₁, d₂, sub_eq_zero]
      funext q
      simp only [hM', Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm)
  exact sub_eq_zero.1 (congrFun this k')

theorem exists_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, (t₁ τ i : k) = t₂ τ i * ψ (u τ i) := by
  obtain rfl : φ₁ = φ₂ := RingHom.ext fun a => hι ((RingHom.congr_fun h₁.2.1 a).symm.trans (RingHom.congr_fun h₂.2.1 a))
  choose M hM using exists_matrix f₁ f₂
  have hT : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hk => by
    obtain ⟨T₁, T₂, -, a₂, b₁, b₂, h⟩ := hM τ ι f₀ t₁ t₂ h₁ h₂
    exact hι ((tri_of_mul (M := fun i k => ι (M τ i k)) b₁ b₂ (fun i => a₂ i ▸ (t₂ τ i).ne_zero) h i k hk).trans
      (map_zero ι).symm)
  refine ⟨fun τ i => M τ i i, fun {k} _ ψ φ' x' g s₁ s₂ g₁ g₂ τ i => ?_⟩
  obtain ⟨T₁, T₂, a₁, a₂, -, b₂, h⟩ := hM τ ψ g s₁ s₂ g₁ g₂
  rw [← a₁, ← a₂, h]
  exact diag_of_mul (M := fun i k => ψ (M τ i k)) b₂ (fun i k hk => by simp only [hT τ i k hk, map_zero]) i

theorem exists_unit_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Rˣ, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, t₁ τ i = t₂ τ i * Units.map (ψ : R →* k) (u τ i) := by
  obtain ⟨u, hu⟩ := exists_ratio f₁ f₂ hι h₁ h₂
  obtain ⟨v, hv⟩ := exists_ratio f₂ f₁ hι h₂ h₁
  have huv : ∀ τ i, u τ i * v τ i = 1 := fun τ i => hι (by
    have a := hu ι f₀ _ _ h₁ h₂ τ i
    have b := hv ι f₀ _ _ h₂ h₁ τ i
    rw [a, mul_assoc] at b
    rw [map_mul, map_one]
    exact (mul_left_cancel₀ (t₂ τ i).ne_zero ((mul_one _).trans b)).symm)
  exact ⟨fun τ i => Units.mkOfMulEqOne _ _ (huv τ i), fun ψ _ _ g s₁ s₂ g₁ g₂ τ i =>
    Units.ext (hu ψ g s₁ s₂ g₁ g₂ τ i)⟩

end Frames

theorem isLocalHom_of_algebraic {R F k : Type} [CommRing R] [IsLocalRing R] [Field F] [CharZero F] (φ : F →+* R)
    [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (ψ : R →+* k) : IsLocalHom ψ := by
  letI : Algebra ℚ R := (φ.comp (algebraMap ℚ F)).toAlgebra
  let ψ' : R →ₐ[ℚ] k := { ψ with commutes' := fun q => by simp }
  refine ⟨fun a ha => ?_⟩
  have h0 : ψ a ≠ 0 := ha.ne_zero
  have hi : IsIntegral ℚ (ψ a) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hc := minpoly.coeff_zero_ne_zero hi h0
  have h1 : ψ (Polynomial.aeval a (minpoly ℚ (ψ a))) = 0 :=
    (Polynomial.aeval_algHom_apply ψ' a _).symm.trans (minpoly.aeval ℚ (ψ a))
  have h2 : ¬ IsUnit (Polynomial.aeval a (minpoly ℚ (ψ a))) := fun h => (h.map ψ).ne_zero h1
  by_contra hna
  rw [← Polynomial.X_mul_divX_add (minpoly ℚ (ψ a)), map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  have h3 : algebraMap ℚ R ((minpoly ℚ (ψ a)).coeff 0) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem (IsLocalRing.maximalIdeal R) h2
      (Ideal.mul_mem_right (Polynomial.aeval a (minpoly ℚ (ψ a)).divX) _ hna)
    rwa [add_sub_cancel_left] at this
  exact h3 (hc.isUnit.map _)

theorem stalk_ext {X : Scheme.{0}} {k : Type} [Field k] {y y' : X} {ψ : X.presheaf.stalk y →+* k}
    {ψ' : X.presheaf.stalk y' →+* k} (h : IsLocalHom ψ) (h' : IsLocalHom ψ')
    (e : spMap ψ ≫ X.fromSpecStalk y = spMap ψ' ≫ X.fromSpecStalk y') : y = y' ∧ HEq ψ ψ' := by
  have := (SpecToEquivOfLocalRing X (.of k)).symm.injective (a₁ := ⟨y, CommRingCat.ofHom ψ, h⟩)
    (a₂ := ⟨y', CommRingCat.ofHom ψ', h'⟩) e
  obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 this
  exact ⟨rfl, heq_of_eq (congrArg (fun f => f.1.hom) (eq_of_heq e'))⟩

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

theorem exists_isCoord (hσ : ∀ y, (divOf Y n).RegularAt y σ) (h : Y.Carries p g) : ∃ a, IsCoord Y p g n σ a := by
  obtain ⟨y, ψ, φ₁, f, t, t', h₁, h₂, h₃⟩ := h
  obtain ⟨φ₂, f₂, t₂, hT, ht⟩ := Y.gr_spec y
  obtain ⟨u, hu⟩ := exists_unit_ratio f f₂ (IsFractionRing.injective (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) h₂ hT
  have ht' : ∀ τ i, (Y.gr τ i).IsEqn y (t τ i) := fun τ i => (ht τ i).iff_unitAt.2
    ⟨u τ i, (u τ i).isUnit, by
      rw [hu _ _ _ _ h₂ hT τ i, Units.val_mul, mul_div_cancel_left₀ _ (Units.ne_zero _)]; rfl⟩
  have hE : ∀ s : Finset (Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ n z) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht' _ _).zsmul _).add ih
  obtain ⟨r, hr⟩ := (hE Finset.univ).regularAt_iff.1 (hσ y)
  exact ⟨_, y, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, hr, rfl⟩

end Coord

end GlobalTheory.ShFam.CoordUniq
