import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

section Scale

variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X}

theorem res_constFn {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem constFn_mul (U : X.Opens) (a b : R) : constFn p U (a * b) = constFn p U a * constFn p U b := by
  rw [constFn, constFn, constFn, map_mul, map_mul]

theorem constFn_one (U : X.Opens) : constFn p U (1 : R) = 1 := by
  rw [constFn, map_one, map_one]

theorem exists_sec_div {a b : R} (h : a * b = 1) (s : L.Sec) :
    ∃ t : L.Sec, (∀ i, t.f i = constFn p _ b * s.f i) ∧ (∀ i, s.f i = constFn p _ a * t.f i) ∧
      Out.nonzeroLocus s ≤ Out.nonzeroLocus t := by
  have e : ∀ i, s.f i = constFn p _ a * (constFn p _ b * s.f i) := fun i => by
    rw [← _root_.mul_assoc, ← constFn_mul, h, constFn_one, _root_.one_mul]
  refine ⟨⟨fun i => constFn p _ b * s.f i, fun i j => ?_⟩, fun _ => rfl, e, iSup_mono fun i => ?_⟩
  · rw [map_mul, map_mul, res_constFn, res_constFn, s.compat i j, mul_left_comm]
  · conv_lhs => rw [e i, Scheme.basicOpen_mul]
    exact inf_le_right

end Scale

theorem value_at_normalForm :
    ∀ (N : ℕ → ℕ) (g₀ : ℕ) (κ : KeyIn ℂ → ℂˣ) (g : ℕ) (a b : Fin g → ℂ), g₀ ≤ g → GlobalTheory.KeyPow.ClauseH ℂ N g₀ κ → (∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 → κ x = 1) → ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 → M.det ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c → (κ x : ℂ) = (M.det ^ 4 / c ^ 8) ^ N g := by
  intro N g₀ κ g a b hg₀ hH hN x h τ M c hc hM hx
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  dsimp only at h τ M
  subst h
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hx
  haveI := P.isAb.comm
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v₀ hb₀.1
  have hMv : ∀ i, IsLieComb (M i) v₀ (v i) := fun i => by
    obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
    have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
    have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
      rw [← Matrix.vecMul_eq_sum]
      refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
      simpa using smul_one_row (1 : ℂ) i
    rw [e] at h1
    rwa [(ex _).unique (sgl i) h1]
  obtain ⟨th₀, e₀, e₁, hle⟩ := exists_sec_div P.A.hom (mul_inv_cancel₀ hc) th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (hth s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  have h0 : κ ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ = 1 := by
    refine hN ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ rfl τ ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (e₀ i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (c⁻¹ * ·) e).trans ?_
      beta_reduce
      rw [_root_.one_mul, ← _root_.mul_assoc, inv_mul_cancel_left₀ hc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hv₀ i)
      have e : ∑ j, M⁻¹ i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin P.g) (Fin P.g) ℂ) i := by
        simp only [smul_comm (M⁻¹ i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum, ← Matrix.nonsing_inv_mul M hM.isUnit]
        rfl
      rwa [e] at h1
  have h1 := hH P hg rig hr _ hth₀ v₀ hb₀ th hth v hv c M hg₀ e₁ hMv
  rw [h0, Units.val_one, _root_.mul_one] at h1
  rw [div_pow, ← pow_mul, ← pow_mul, eq_div_iff (pow_ne_zero _ hc), mul_comm]
  exact h1

end GlobalTheory.KeyPow
end
