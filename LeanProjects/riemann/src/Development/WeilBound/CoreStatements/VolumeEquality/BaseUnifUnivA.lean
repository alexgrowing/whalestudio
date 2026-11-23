import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ

theorem imH_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    ((z + z') ⬝ᵥ M *ᵥ star w).im = (z ⬝ᵥ M *ᵥ star w).im + (z' ⬝ᵥ M *ᵥ star w).im := by
  rw [add_dotProduct, Complex.add_im]

theorem imH_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    ((r • z) ⬝ᵥ M *ᵥ star w).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  rw [smul_dotProduct, Complex.smul_im, smul_eq_mul]

theorem imH_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (w + w')).im = (z ⬝ᵥ M *ᵥ star w).im + (z ⬝ᵥ M *ᵥ star w').im := by
  rw [star_add, mulVec_add, dotProduct_add, Complex.add_im]

theorem imH_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (r • w)).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  have h : star (r • w) = (r : ℂ) • star w := by
    ext i
    simp
  rw [h, mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.im_ofReal_mul]

theorem exists_realExt {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (hf : R'.form = R.form) :
    ∃ L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ x, L (R.P x) = R'.P x) ∧
      (∀ z w, (L z ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (z ⬝ᵥ R.Hm *ᵥ star w).im) ∧
      ∀ a z, L (R.B a z) = R'.B a (L z) := by
  classical
  haveI := R.free
  haveI := R.fin
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (SheetDecomposition.riemBasic E g Λ Unit R).2.1
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ R.rank
  let v : Fin (2 * g) → Fin g → ℂ := fun k => R.P (b k)
  have hsum : ∀ (Q : Λ →+ (Fin g → ℂ)) (x : Λ), Q x = ∑ k, (b.repr x k : ℝ) • Q (b k) := by
    intro Q x
    conv_lhs => rw [← b.sum_repr x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hv : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hsum R.P x]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  let c : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ) := basisOfTopLeSpanOfCardEqFinrank v hv hcard
  have hc : ∀ k, c k = R.P (b k) := fun k => by
    simp [c, v, coe_basisOfTopLeSpanOfCardEqFinrank]
  let L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := c.constr ℝ fun k => R'.P (b k)
  have hLb : ∀ k, L (R.P (b k)) = R'.P (b k) := fun k => by
    rw [← hc k]
    exact c.constr_basis ℝ _ k
  have hL : ∀ x, L (R.P x) = R'.P x := by
    intro x
    rw [hsum R.P x, hsum R'.P x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hLb]
  have hall : ∀ z : Fin g → ℂ, z ∈ Submodule.span ℝ (Set.range R.P) := fun z => hspan ▸ Submodule.mem_top
  refine ⟨L, hL, ?_, ?_⟩
  · have h1 : ∀ (x : Λ) (w : Fin g → ℂ),
        (L (R.P x) ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (R.P x ⬝ᵥ R.Hm *ᵥ star w).im := by
      intro x w
      induction hall w using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨y, rfl⟩ := hw
        rw [hL, hL, R'.im, R.im, hf]
      | zero => simp
      | add w w' _ _ h h' => rw [map_add, imH_add_right, imH_add_right, h, h']
      | smul r w _ h => rw [map_smul, imH_smul_right, imH_smul_right, h]
    intro z w
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact h1 x w
    | zero => simp
    | add z z' _ _ h h' => rw [map_add, imH_add_left, imH_add_left, h, h']
    | smul r z _ h => rw [map_smul, imH_smul_left, imH_smul_left, h]
  · intro a z
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← R.act, hL, hL, R'.act]
    | zero => simp
    | add z z' _ _ h h' => simp only [map_add, h, h']
    | smul r z _ h =>
      rw [LinearMap.map_smul_of_tower, map_smul, h, map_smul, LinearMap.map_smul_of_tower]

end SheetDecomposition.Univ
