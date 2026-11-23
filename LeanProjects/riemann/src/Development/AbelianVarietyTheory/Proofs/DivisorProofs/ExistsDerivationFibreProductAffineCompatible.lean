import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreDer

theorem exists_der_fibre : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (O : Z.affineOpens) (hO : O.1 ≤ p ⁻¹ᵁ U.1) (δ : Derivation ℤ Γ(Z, O.1) Γ(Z, O.1)), (∀ r, δ ((p.appLE U.1 O.1 hO).hom r) = (p.appLE U.1 O.1 hO).hom (D r)) → ∃ δ' : Derivation ℤ Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1), (∀ r, δ' ((p'.appLE U'.1 _ inf_le_right).hom r) = (p'.appLE U'.1 _ inf_le_right).hom (D' r)) ∧ ∀ f, δ' ((φ.appLE O.1 _ inf_le_left).hom f) = (φ.appLE O.1 _ inf_le_left).hom (δ f) := by
  intro Z Z' X X' p p' φ g H U U' hU D D' hD' O hO δ hδ
  have P := (isIso_pushoutSection_iff H (US := U.1) (UT := U'.1) (UX := O.1)
    (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) hU hO rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hU hO rfl U.2 U'.2 O.2)
  set α := φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left with hα
  set β := p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right with hβ
  let a : Γ(Z, O.1) →+* DualNumber Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) :=
    { toFun := fun f => TrivSqZeroExt.inl (α.hom f) + TrivSqZeroExt.inr (α.hom (δ f))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp <;> ring
      map_mul' := fun x y => by ext <;> simp [Derivation.leibniz] <;> ring }
  let b : Γ(X', U'.1) →+* DualNumber Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) :=
    { toFun := fun r => TrivSqZeroExt.inl (β.hom r) + TrivSqZeroExt.inr (β.hom (D' r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp <;> ring
      map_mul' := fun x y => by ext <;> simp [Derivation.leibniz] <;> ring }
  have hw0 : ∀ s, α.hom ((p.appLE U.1 O.1 hO).hom s) = β.hom ((g.appLE U.1 U'.1 hU).hom s) :=
    fun s => congr($(P.w).hom s)
  have hw : p.appLE U.1 O.1 hO ≫ CommRingCat.ofHom a = g.appLE U.1 U'.1 hU ≫ CommRingCat.ofHom b := by
    ext s
    · simp [a, b, hw0]
    · simp [a, b, hδ, hD', hw0]
  let σ := P.desc (CommRingCat.ofHom a) (CommRingCat.ofHom b) hw
  have hσl : ∀ f, σ.hom (α.hom f) = a f := fun f => congr($(P.inl_desc _ _ hw).hom f)
  have hσr : ∀ r, σ.hom (β.hom r) = b r := fun r => congr($(P.inr_desc _ _ hw).hom r)
  have hfst0 : σ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom ℤ _ _).toRingHom = 𝟙 _ := by
    refine P.hom_ext ?_ ?_
    · ext f
      simp [hσl, a]
    · ext r
      simp [hσr, b]
  have hfst : ∀ x, (σ.hom x).fst = x := fun x => congr($(hfst0).hom x)
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun x => (σ.hom x).snd, map_zero' := by simp, map_add' := fun x y => by rw [map_add]; rfl })
    fun x y => ?_, fun r => ?_, fun f => ?_⟩
  · change (σ.hom (x * y)).snd = x • (σ.hom y).snd + y • (σ.hom x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [smul_eq_mul, mul_comm]
  · change (σ.hom (β.hom r)).snd = _
    rw [hσr]
    simp [b]
  · change (σ.hom (α.hom f)).snd = _
    rw [hσl]
    simp [a]

end GlobalTheory.FibreDer
