import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam.Pad GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

namespace GlobalTheory.BdFib

attribute [local instance] Over.cartesianMonoidalCategory

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def FibAt {k : Type} [Field k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G) : Prop :=
  IsGrpPullback φ.G t.G x m.F ∧ m.e = x ∧ m.IsPullCubical φ.cub t.cub

def IsCochFrame {R : Type} [CommRing R] (x : Sp R ⟶ X) {r : ℕ} (ε : Fin r → TanM x t.G) : Prop :=
  ∃ u : torus R r ⟶ (Over.pullback x).obj t.G, IsMonHom u ∧ IsClosedImmersion u.left ∧
    ∀ i, ∃ e : LieG (torus R r), lieCoord e = Pi.single i 1 ∧
      (tv (ε i)).left = e.1.left ≫ u.left ≫ pullback.fst t.G.hom x

def TorRk {k : Type} [Field k] (x : Sp k ⟶ X) (r : ℕ) : Prop :=
  ∀ T : TorusExtension ((Over.pullback x).obj t.G), @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ = r

variable {t}

def IsAbMap {k : Type} [Field k] {x : Sp k ⟶ X} (φ : Fib k) (m : CubeMap φ.G t.G) {n : ℕ} (v : Fin n → (epsR k ⟶ φ.P.A))
    (q : TanM x t.G →ₗ[k] (Fin n → k)) : Prop :=
  ∀ w : TanM x t.G, ∃ w' : epsR k ⟶ φ.G, w'.left ≫ m.F = (tv w).left ∧ IsLieComb (q w) v (w' ≫ φ.q)

def AbLe {z : Sp ℂ ⟶ X} (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ (φ : Fib ℂ) (m : CubeMap φ.G t.G), FibAt t z φ m → ∀ (n : ℕ), φ.P.g = n → ∀ (u : HolUnif φ.P.A φ.P.L n)
    (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    ∀ (v : TanM z t.G) (v' : epsR ℂ ⟶ φ.G) (W : Fin n → ℂ), v'.left ≫ m.F = (tv v).left → u.IsDiff W (v' ≫ φ.q) →
      Real.pi * (hermForm Hm W W).re ≤ C * (g v v).re

theorem AbLe.mono {z : Sp ℂ ⟶ X} {g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ} (hg : IsBlockMetric g) {C C' : ℝ}
    (h : AbLe g C) (hC : C ≤ C') : AbLe g C' := fun φ m hφ n e u Hm χ hA v v' W h₁ h₂ => by
  refine (h φ m hφ n e u Hm χ hA v v' W h₁ h₂).trans (mul_le_mul_of_nonneg_right hC ?_)
  by_cases hv : v = 0
  · simp [hv]
  · exact (hg.2.1 v hv).le

end Fibre

def HasModel {K : Type} [Field K] [NumberField K] (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (G : Over (Sp (𝓞 K))) (_ : GrpObj G) (θ : A.left ⟶ G.left), IsSemiAbelian G ∧
    IsGrpPullback A G (spMap (algebraMap (𝓞 K) K)) θ

section Large

variable {Y : Scheme.{0}}

def Large (y : Sp Qb ⟶ Y) (Q : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop) : Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb),
    ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ →
      ∀ yK : Sp K ⟶ Y, spMap io ≫ yK = y → Q K yK

theorem exists_common {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] (i₁ : K₁ →+* Qb)
    (i₂ : K₂ →+* Qb) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (i : K →+* Qb) (j₁ : K₁ →+* K) (j₂ : K₂ →+* K),
      i.comp j₁ = i₁ ∧ i.comp j₂ = i₂ := by
  let a₁ : K₁ →ₐ[ℚ] Qb := i₁.toRatAlgHom
  let a₂ : K₂ →ₐ[ℚ] Qb := i₂.toRatAlgHom
  haveI : FiniteDimensional ℚ a₁.fieldRange := a₁.toLinearMap.finiteDimensional_range
  haveI : FiniteDimensional ℚ a₂.fieldRange := a₂.toLinearMap.finiteDimensional_range
  let K : IntermediateField ℚ Qb := a₁.fieldRange ⊔ a₂.fieldRange
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField K := ⟨⟩
  refine ⟨K, inferInstance, inferInstance, algebraMap K Qb,
    i₁.codRestrict K.toSubfield fun a => (le_sup_left : a₁.fieldRange ≤ K) ⟨a, rfl⟩,
    i₂.codRestrict K.toSubfield fun a => (le_sup_right : a₂.fieldRange ≤ K) ⟨a, rfl⟩, rfl, rfl⟩

variable {y : Sp Qb ⟶ Y} {Q Q' : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop}

theorem Large.and (h : Large y Q) (h' : Large y Q') : Large y fun K _ _ yK => Q K yK ∧ Q' K yK := by
  obtain ⟨K₁, _, _, i₁, h₁⟩ := h
  obtain ⟨K₂, _, _, i₂, h₂⟩ := h'
  obtain ⟨K₀, _, _, i, j₁, j₂, e₁, e₂⟩ := exists_common i₁ i₂
  refine ⟨K₀, _, inferInstance, i, fun K _ _ io j hj yK hy => ⟨h₁ K io (j.comp j₁) ?_ yK hy, h₂ K io (j.comp j₂) ?_ yK hy⟩⟩
  · rw [← RingHom.comp_assoc, hj, e₁]
  · rw [← RingHom.comp_assoc, hj, e₂]

theorem epi_spMap {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  have h₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact inferInstanceAs (Module.Flat K L)
  have h₂ : Surjective (spMap f) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem Large.of_point {K₀ : Type} [Field K₀] [NumberField K₀] (io₀ : K₀ →+* Qb) (y₀ : Sp K₀ ⟶ Y)
    (hy : spMap io₀ ≫ y₀ = y)
    (h : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ → Q K (spMap j ≫ y₀)) :
    Large y Q := by
  refine ⟨K₀, _, inferInstance, io₀, fun K _ _ io j hj yK hK => ?_⟩
  have := epi_spMap io
  have e : yK = spMap j ≫ y₀ := by
    rw [← cancel_epi (spMap io), hK, ← hy, ← hj, ← Category.assoc, ← Spec.map_comp]
    rfl
  exact e ▸ h K io j hj

end Large

end GlobalTheory.BdFib

end
