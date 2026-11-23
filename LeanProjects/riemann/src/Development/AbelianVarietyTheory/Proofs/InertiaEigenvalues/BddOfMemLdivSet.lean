import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff (l * n + i) z

theorem coeff_frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) (n : ℕ) :
    coeff n (frobSlice l i z) = coeff (l * n + i) z := by
  simp [frobSlice]

namespace Hom

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

def rdivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ F.mat τ * Y = h • (1 : Matrix κ κ K⟦X⟧)}

def ldivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ Y * F.mat τ = h • (1 : Matrix ι ι K⟦X⟧)}

theorem bdd_mul {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f * g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  exact ⟨a * b, fun n => by
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0 hb0
      (f := f) (g := g) (by simpa using ha) (by simpa using hb) n⟩

theorem bdd_add {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f + g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨max a b, fun n => by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha n) (hb n))⟩

theorem bdd_smul_matrix {μ ν : Type} {b : K⟦X⟧} {Y : Matrix μ ν K⟦X⟧} (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c)
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n ((b • Y) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨c, hc⟩ := hY
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  refine ⟨a * max c 0, fun i j n => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0
    (le_max_right c 0) (f := b) (g := Y i j) (by simpa using ha)
    (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _)) n

theorem rdivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (hy : y ∈ F.rdivSet τ) :
    x + y ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.mul_add, h₁, h₂, add_smul]

theorem ldivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (hy : y ∈ F.ldivSet τ) :
    x + y ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.add_mul, h₁, h₂, add_smul]

theorem rdivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.mul_smul, h, smul_smul]

theorem ldivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.smul_mul, h, smul_smul]

end Hom

end GlobalTheory.BK
