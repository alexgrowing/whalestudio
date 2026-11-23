import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.FnForm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG_apply {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

def chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (mchart c) x hx).hom
    (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2))

theorem ptCoord_eq_mul_chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    ptCoord x p = ptCoord x ⟨p.1, c p.1⟩ * chartCoord c x hx p := by
  obtain ⟨k, j⟩ := p
  let P : MP ℤ m n ⟶ PSpace ℤ (n k) := prB n k
  let W₀ : (MP ℤ m n).Opens := blockChart n k (ptChart x k)
  let W₁ : (MP ℤ m n).Opens := blockChart n k (c k)
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := le_rfl
  have hx₀ : x ∈ W₀ := mem_ptChart x k
  have hx₁ : x ∈ W₁ := mchart_le c k hx
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right.trans h₁
  have e₀ : ∀ l : Bk n k, ptCoord x ⟨k, l⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (ptChart x k) hV₀ l) := by
    intro l
    show ((MP ℤ m n).evaluation W₀ x hx₀).hom (pullRatio P W₀ (ptChart x k) h₀ l) = _
    rw [← evaluation_resG_apply (inf_le_left : V ≤ W₀) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₀) inf_le_left)
  have e₁ : chartCoord c x hx ⟨k, j⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (c k) hV₁ j) := by
    show ((MP ℤ m n).evaluation (mchart c) x hx).hom (resG _ (mchart_le c k) (pullRatio P W₁ (c k) h₁ j)) = _
    rw [evaluation_resG_apply, ← evaluation_resG_apply (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  show ptCoord x ⟨k, j⟩ = ptCoord x ⟨k, c k⟩ * chartCoord c x hx ⟨k, j⟩
  rw [e₀ j, e₀ (c k), e₁, ← map_mul]
  exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := j)).symm

theorem evaluation_dehomog (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (f : Pol n) :
    ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) = aeval (chartCoord c x hx) f := by
  have e : ((MP ℤ m n).evaluation (mchart c) x hx).hom.comp (dehomog c) =
      (aeval (chartCoord c x hx) : Pol n →ₐ[ℤ] _).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp [dehomog, chartCoord])
  exact congrArg (fun φ => φ f) e

theorem aeval_ptCoord_eq_mul (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) {f : Pol n}
    {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    aeval (ptCoord x) f = (∏ k, ptCoord x ⟨k, c k⟩ ^ a k) *
      ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) := by
  rw [evaluation_dehomog, ← GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.aeval_smul hf]
  exact congrArg (fun v => aeval v f) (funext (ptCoord_eq_mul_chartCoord c x hx))

theorem fnAt_ne_zero_of_notMem_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  intro m n X _ i _ c h f a hf hnot h0
  refine hnot ((mem_ptIdeal_iff_aeval_ptCoord m n _ f a hf).2 ?_)
  have hx : i (genericPoint X) ∈ mchart c := h
  have h1 : i.app (mchart c) (dehomog c f) = 0 :=
    fnOf_injective _ h (h0.trans (map_zero _).symm)
  have h2 : ((MP ℤ m n).evaluation (mchart c) _ hx).hom (dehomog c f) = 0 := by
    apply (i.residueFieldMap (genericPoint X)).hom.injective
    rw [map_zero]
    refine (Scheme.evaluation_naturality_apply i (genericPoint X) hx _).trans ?_
    rw [h1, map_zero]
  rw [aeval_ptCoord_eq_mul c _ hx hf, h2, mul_zero]

end GlobalTheory.CompanionTheory.MixZ.FnForm
