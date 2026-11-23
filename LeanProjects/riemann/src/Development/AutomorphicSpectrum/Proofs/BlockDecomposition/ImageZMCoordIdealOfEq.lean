import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  {Ω₀ Ω : Type*} [Field Ω₀] [Field Ω]

def scaleT (c : K → Ω) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω :=
  aeval fun k => C (c k) * X k

theorem scaleT_injective (c : K → Ω) (hc : ∀ k, c k ≠ 0) : Function.Injective (scaleT c) := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleT fun k => (c k)⁻¹) fun f => by
    simpa using congrArg (fun g => g f) h

theorem imageZ_mCoordIdeal_of_eq (κ : K → K') (hκ : Function.Injective κ) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (hv : ∀ p, (v p).1 = κ p.1) (φ : Ω₀ →+* Ω) (b : K → Ω) (hb : ∀ k, b k ≠ 0)
    (y₀ : (Σ k, ι k) → Ω₀) (y : (Σ k', ι' k') → Ω) (h : ∀ p, φ (y₀ p) = b p.1 * y (v p)) :
    imageZ v (Geo.mCoordIdeal y) = Geo.mCoordIdeal y₀ := by
  let ψ : MvPolynomial K Ω₀ →+* MvPolynomial K' Ω :=
    ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).toRingHom.comp
      (scaleT fun k => (b k)⁻¹).toRingHom).comp (MvPolynomial.map φ)
  have hψ : Function.Injective ψ :=
    (rename_injective κ hκ).comp ((scaleT_injective _ fun k => inv_ne_zero (hb k)).comp
      (map_injective φ φ.injective))
  have key : ∀ f : Geo.MRing ι, ψ (Geo.mConeMap y₀ f) = Geo.mConeMap y (rename v f) := by
    intro f
    have e : ψ.comp (Geo.mConeMap y₀ : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω₀).toRingHom =
        ((Geo.mConeMap y : Geo.MRing ι' →ₐ[ℤ] MvPolynomial K' Ω).toRingHom.comp
          (rename v : Geo.MRing ι →ₐ[ℤ] Geo.MRing ι').toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
      · simp
      · simp only [ψ, Geo.mConeMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
          rename_X, map_mul, map_C, map_X, scaleT, algHom_C, rename_C]
        rw [hv p, h p]
        simp only [MvPolynomial.algebraMap_eq, rename_C]
        rw [← mul_assoc, ← C_mul, mul_comm (b p.1), mul_assoc, mul_inv_cancel₀ (hb p.1), mul_one]
    exact congrArg (fun g => g f) e
  ext f
  simp only [imageZ, Geo.mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← key, map_eq_zero_iff ψ hψ]

end Alg

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem evaluation_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.evaluation V x hx (resG X h s) = X.evaluation U x (h hx) s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem ptCoord_qpSnd (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (k : Fin (m + 1)) :
    ∃ b : (MP ℤ (m + 1) (consN n' n)).residueField x, b ≠ 0 ∧ ∀ i : Bk n k,
      (qpSnd n' m n).residueFieldMap x (ptCoord (qpSnd n' m n x) ⟨k, i⟩) = b * ptCoord x ⟨k.succ, i⟩ := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  let P : MP ℤ (m + 1) (consN n' n) ⟶ PSpace ℤ (n k) := prB (consN n' n) k.succ
  have hP : F ≫ prB n k = P := rfl
  let c₀ := ptChart (F x) k
  let c₁ := ptChart x k.succ
  have hx₀ : F x ∈ blockChart n k c₀ := mem_ptChart _ _
  have hx₁ : x ∈ blockChart (consN n' n) k.succ c₁ := mem_ptChart _ _
  let W₀ : (MP ℤ (m + 1) (consN n' n)).Opens := F ⁻¹ᵁ blockChart n k c₀
  let W₁ : (MP ℤ (m + 1) (consN n' n)).Opens := blockChart (consN n' n) k.succ c₁
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := le_rfl
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := inf_le_right.trans h₁
  have e₀ : ∀ i : Bk n k, F.residueFieldMap x (ptCoord (F x) ⟨k, i⟩) =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ i) := by
    intro i
    show F.residueFieldMap x ((MP ℤ m n).evaluation (blockChart n k c₀) (F x) hx₀
      (pullRatio (prB n k) _ c₀ le_rfl i)) = _
    rw [Scheme.evaluation_naturality_apply, Scheme.Hom.app_eq_appLE, appLE_pullRatio,
      ← evaluation_resG (inf_le_left : V ≤ W₀) x hxV, resG_pullRatio]
    rfl
  have e₁ : ∀ i : Bk n k, ptCoord x ⟨k.succ, i⟩ =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₁ hV₁ i) := by
    intro i
    show (MP ℤ (m + 1) (consN n' n)).evaluation W₁ x hx₁ (pullRatio P W₁ c₁ h₁ i) = _
    rw [← evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  refine ⟨(MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ c₁), ?_, fun i => ?_⟩
  · intro h0
    have e := congrArg ((MP ℤ (m + 1) (consN n' n)).evaluation V x hxV)
      ((pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := c₀)).trans pullRatio_self)
    rw [map_mul, h0, zero_mul, map_one] at e
    exact zero_ne_one e
  · refine (e₀ i).trans ?_
    rw [e₁ i, ← map_mul]
    exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := i)).symm

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem imageZ_ptIdeal (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) :
    imageZ (sv n' n) (ptIdeal x) = ptIdeal (qpSnd n' m n x) := by
  choose b hb h using ptCoord_qpSnd n' m n x
  exact imageZ_mCoordIdeal_of_eq Fin.succ (Fin.succ_injective _) (sv n' n) (fun _ => rfl)
    ((qpSnd n' m n).residueFieldMap x).hom b hb (ptCoord (qpSnd n' m n x)) (ptCoord x) fun p => h p.1 p.2

end GlobalTheory.CompanionTheory.MPDict.ProjImage
