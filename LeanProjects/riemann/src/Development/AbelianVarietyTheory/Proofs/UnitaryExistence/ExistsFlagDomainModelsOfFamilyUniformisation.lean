import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticeModelOfSameSignatureHasseNormStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatumStatement

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ModelsExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {r : ℕ}

theorem rt0_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0 ≠ 0 := by
  intro h
  have h1 := H.sqrt_neg_disc_sq
  rw [h] at h1
  have h2 : (H.d : ℂ) = 0 := by simpa using h1
  exact H.d_prime.ne_zero (by exact_mod_cast h2)

theorem rt0_conj_neg_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h1 : (starRingEnd ℂ H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [pow_two, him] at h2
    nlinarith [mul_self_nonneg H.rt0.re]
  · exact h

theorem emb_rt_eq_or (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  have h : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [← map_pow, h, H.sqrt_neg_disc_sq]; simp

theorem cm_type (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ↔ ¬ ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hne : -H.rt0 ≠ H.rt0 := fun h => rt0_ne_zero H (by linear_combination (-1 / 2 : ℂ) * h)
  rcases emb_rt_eq_or H τ with h | h
  · rw [h, rt0_conj_neg_ne_zero]; simp [hne]
  · rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]; simp [hne]

theorem exists_emb (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0
  · exact ⟨_, h⟩
  · exact ⟨τ, (cm_type H τ).2 h⟩

def dataOf (l : Level H) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (ξ₀ : E) (q : ℕ)
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (hherm : ∀ a b, cc (Gm a b) = Gm b a) (hdet : Gm.det ≠ 0) (hq : q ≤ r)
    (hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ))
    (hξ : cc ξ₀ = -ξ₀) (hξ0 : ξ₀ ≠ 0) (hκ : ∀ τ : Ψ, (τ.1 (2 * ξ₀)).im < 0)
    (Di : Datum H) (hL : LatModel l Ψ Gm ξ₀ q Di) : Data E r where
  Ψ := Ψ
  cmType := hΨ
  Gm := Gm
  Gm_herm := hherm
  Gm_det := hdet
  p0 := q
  p0_le := hq
  signature := hsig
  Λ := LinearMap.range hL.choose
  Λ_fg := by
    have := Di.fin
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  Λ_span := hL.choose_spec.2.2.1
  den := hL.choose_spec.2.2.2.1.choose
  den_ne := hL.choose_spec.2.2.2.1.choose_spec.1
  Λ_int := hL.choose_spec.2.2.2.1.choose_spec.2
  Γ := GlobalTheory.FrameUnif.princ l Gm Di hL.choose
  Γ_stab := fun _ hγ => hγ.1
  Γ_index := hL.choose_spec.2.2.2.2.1
  Γ_free := hL.choose_spec.2.2.2.2.2.1
  χ := fun _ _ => 1
  χ_mul := fun _ _ _ _ _ => (mul_one 1).symm
  χ_add := fun _ _ _ _ => (mul_one 1).symm
  χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩
  ξ0 := ξ₀
  ξ0_im := hξ
  ξ0_ne := hξ0
  κ0 := 2 * ξ₀
  κ0_xi := Or.inl rfl
  κ0_sign := hκ
  m := hL.choose_spec.2.2.2.2.2.2.choose
  m_pos := hL.choose_spec.2.2.2.2.2.2.choose_spec.1
  transv := fun ξ hξ h0 s hs hsi =>
    hL.choose_spec.2.2.2.2.2.2.choose_spec.2 _ (Or.inl rfl) ξ hξ h0 s hs hsi

theorem exists_modelsOf : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ M : ModelsOf F r, ModelBase M ∧ NegXi M ∧ ∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀ := by
  classical
  intro hN E _ _ _ H Dw l Xo σ' g ty F r ξ₀ Gm φ hξ hneg hφ
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0
  have hmem : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => by simp [Ψ]
  have hξ' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hξ ⊢
    rw [map_neg, hξ]
  have hrk : r = Dw.p + Dw.q := (GlobalTheory.HermModel.rank_integral_selfDual E H Dw r (-ξ₀) Gm φ hξ' hφ).1
  have hq : Dw.q ≤ r := by omega
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := fun τ => by
    rw [hmem, hmem]; exact cm_type H τ
  have hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ) := fun τ => by
    have hτ := (hmem τ.1).1 τ.2
    refine (GlobalTheory.T.signature_hermitian_model_of_datum E H Dw r (-ξ₀) Gm φ hξ' hφ τ.1 hτ).1 ?_
    have := hneg τ.1 hτ
    rw [map_neg, Complex.neg_im]
    linarith
  have hξ0 : ξ₀ ≠ 0 := by
    rintro rfl
    obtain ⟨τ, hτ⟩ := exists_emb H
    simpa using hneg τ hτ
  have hκ : ∀ τ : Ψ, (τ.1 (2 * ξ₀)).im < 0 := fun τ => by
    have := hneg τ.1 ((hmem τ.1).1 τ.2)
    rw [two_mul, map_add, Complex.add_im]
    linarith
  have hL : ∀ i, LatModel l Ψ Gm ξ₀ Dw.q (F.Di i) := fun i =>
    GlobalTheory.T.latticeModel_of_same_signature_hasseNorm hN E H l Dw (F.Di i) r Ψ ξ₀ Gm φ (F.sig i).1 (F.sig i).2 hmem hξ hφ
  refine ⟨⟨fun i => dataOf l Ψ Gm ξ₀ Dw.q hΨ hφ.2.2.1 hφ.2.2.2.1 hq hsig hξ hξ0 hκ (F.Di i) (hL i),
    fun i => LinearEquiv.ofInjective (hL i).choose (hL i).choose_spec.1⟩, ?_,
    fun k τ hτ => hneg τ ((hmem τ).1 hτ), fun k => ⟨rfl, rfl⟩⟩
  exact
    { rank := hrk
      type := fun k => ⟨rfl, hmem⟩
      chi := fun _ _ _ => rfl
      ef := fun k a b => (hL k).choose_spec.2.1 a b
      gam := fun k γ => Iff.rfl
      domStab := fun k x hx => ⟨fun b hb => dom_rmul _ hx hb, fun γ hγ => dom_lact _ hx hγ.1⟩ }

end GlobalTheory.ModelsExist
