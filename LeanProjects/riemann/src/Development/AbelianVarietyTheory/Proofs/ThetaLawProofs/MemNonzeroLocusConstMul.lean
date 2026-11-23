import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyNormalExists

def constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f j := constFn p _ a * s.f j
  compat j k := by
    rw [map_mul, map_mul, ThetaOnto.res_constFn, ThetaOnto.res_constFn, s.compat j k]
    ring

theorem mem_nonzeroLocus_constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : L.Sec) {z : X} (hz : z ∈ Out.nonzeroLocus s) : z ∈ Out.nonzeroLocus (constMul p a s) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have hu : IsUnit (constFn p (L.U i) a) := (ha.map _).map _
  change z ∈ X.basicOpen (constFn p (L.U i) a * s.f i)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
  exact ⟨X.basicOpen_le _ hi, hi⟩

theorem isFn_constMul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a : ℂ) {s : L.Sec}
    {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsFn (constMul A.hom a s) (fun z => a * θ z) := by
  intro i z hz
  change valAt' _ _ (constFn A.hom (L.U i) a * s.f i) = _
  rw [valAt'_mul, valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz, h i z hz, _root_.mul_assoc]

theorem exists_normalAt_one (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) :
    ∃ th hth v hv, KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (M⁻¹ i)).exists
  refine ⟨constMul x.P.A.hom c⁻¹ x.th, fun s => ?_, v,
    (hb M⁻¹ v x.basis hv).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit), u, h₁, h₂, h₃, h₄, ?_, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, mem_nonzeroLocus_constMul _ (inv_ne_zero hc).isUnit _ hz'⟩
  · have := isFn_constMul u c⁻¹ h₅
    simpa only [inv_mul_cancel_left₀ hc, _root_.one_mul] using this
  · have := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (M⁻¹ i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, M⁻¹ i j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) i := by
      rw [← Matrix.nonsing_inv_mul M hM.isUnit]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    exact this

theorem exists_normalAt :
    ThetaUnifAV → ∀ x : KeyIn ℂ, (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ c ≠ 0 ∧ M.det ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ M a b c) ∧ ∃ (th : x.P.L.Sec) (hth : _) (v : _) (hv : _) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ GlobalTheory.KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  intro hU x
  obtain ⟨u, Hm, χ, -, hA, hR, hd, -⟩ := hU x.P x.rig x.rig_gen
  choose W hW using fun i => (hd _ (x.basis.1 i)).exists
  obtain ⟨θ, hθ⟩ := KeyPow.exists_isFn x.P.isLB u x.th
  obtain ⟨Fd, hF⟩ := KeyPow.exists_isAddFundamentalDomain u
  obtain ⟨u', τ, M, a, b, c, h₁, h₂, ha, hb, h₃, h₄, hc, h₅, hM, h₆, -⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd _ _ hA hR hθ hW hF rfl rfl
  have hN : KeyPow.NormalAt x τ M a b c := ⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨th, hth, v, hv, h⟩ := exists_normalAt_one x hc hM hN
  exact ⟨⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hM, hN⟩, th, hth, v, hv, τ, a, b, ⟨ha, hb⟩, h⟩

end GlobalTheory.KeyNormalExists
