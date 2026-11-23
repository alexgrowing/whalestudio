import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCMPairingFamilyOfPolarisationDiagonalComplexStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem two_mul_sub_one_sq_of_ringHom (τ : OK H →+* ℂ) : (2 * τ (wK H) - 1) ^ 2 = -(H.d : ℂ) := by
  have h : (2 * wK H - 1) ^ 2 = -(H.d : OK H) := by
    apply Subtype.ext
    have e : 2 * H.w0 - 1 = H.rt := by rw [H.two_weight_eq_one_add_root]; ring
    have := H.rt_sq
    rw [← e] at this
    have e2 : ((2 : OK H) : 𝓞 E) = 2 := rfl
    simpa [wK, e2] using this
  have := congrArg τ h
  simpa [map_ofNat] using this

theorem exists_hermitianPairing_eq_im_mul_pureType {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) {ω : ℂ} {x : D.La} (hx : x ∈ PureType.lat hP (2 * ω - 1)) (h0 : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ω.im * r := by
  obtain ⟨Hm, hH, hpos, hEF⟩ := hP.2.2.2.2
  have hw0 : Pe (H.w0 • x) = ω • Pe x := by
    have e : (2 : ℂ) • Pe (H.w0 • x) = (2 : ℂ) • ω • Pe x := by
      rw [two_smul, ← map_add, ← add_smul, ← two_mul, H.two_weight_eq_one_add_root, add_smul, one_smul, map_add,
        PureType.period_rt_smul hP hx]
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact smul_right_injective _ two_ne_zero e
  have hne : Pe x ≠ 0 := fun h => h0 (hP.2.1 (by rw [h, map_zero]))
  refine ⟨_, hpos _ hne, ?_⟩
  have := PureTypeVector.hermForm_smul_smul Hm ω 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [← hEF, hw0, this]
  simp [PureTypeVector.hermForm_self_im hH]

theorem exists_isFam_complex : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (ω : ℂ) (C : Ell H ℂ ω) (u₀ : HolUnif C.P.A C.P.L C.P.g) (c : ℂ) (T : PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t (FU.u i Pe)) (ε : ℤˣ) (h : (FU.Di i).La → (FU.Di i).La → OK H), PureType.IsThetaUnif u₀ → c ≠ 0 → PureType.IsQuadLattice u₀.Λ H.d c → 0 < ((ε : ℤ) : ℝ) * ω.im → IsKForm (FU.Di i) ε h →
  ∃ ψ : PureType.lat hP (2 * ω - 1) → (C.P.A ⟶ T.t.G), IsFam C T h _ ψ ∧ ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  intro hT hL E _ _ _ H D l Xo g ty FU i Pe hP ω C u₀ c T m ε h hu hc hΛ hε hh
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.cmCurve_lie_character_of_adjoinGenerator E H ℂ ω C
  have hρ : (2 * ω - 1) ^ 2 = -(H.d : ℂ) := hτ ▸ two_mul_sub_one_sq_of_ringHom τ
  obtain ⟨φ, hφ, hφe⟩ := PureType.exists_isHomFamily_complex hT hL.weil FU i hP m u₀ C.dim hu hc hΛ hρ
  refine ⟨φ, GlobalTheory.T.isCMPairingFamily_of_polarisationDiagonal_complex hT hL E H ω C _ ε h T _ φ hh (fun x hx h0 => ?_) (hφ _ (C.basis.1 0)), fun a z => ?_⟩
  · obtain ⟨r, hr, e⟩ := exists_hermitianPairing_eq_im_mul_pureType hP hx h0
    have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((FU.Di i).EF (H.w0 • x) x : ℤ) := by
      rw [e, ← _root_.mul_assoc]
      exact mul_pos hε hr
    exact_mod_cast this
  · rw [Over.comp_left, Category.assoc]
    exact hφe a z

end GlobalTheory.CM
