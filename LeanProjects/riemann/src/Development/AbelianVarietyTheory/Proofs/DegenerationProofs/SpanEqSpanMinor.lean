import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open Matrix

noncomputable section
namespace GlobalTheory.ZH.DualLattice

section Algebra

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type} [Fintype J]

def dotDual (N : Submodule S (J → Ω)) : Submodule S (J → Ω) where
  carrier := {v | ∀ w ∈ N, w ⬝ᵥ v ∈ S}
  add_mem' ha hb w hw := by
    rw [dotProduct_add]
    exact add_mem (ha w hw) (hb w hw)
  zero_mem' w _ := by
    rw [dotProduct_zero]
    exact zero_mem _
  smul_mem' c v hv w hw := by
    rw [dotProduct_smul, Subalgebra.smul_def, smul_eq_mul]
    exact mul_mem c.2 (hv w hw)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
open Matrix in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type}
  [Fintype J] in
private theorem mem_dotDual_iff' (N : Submodule S (J → Ω)) (v : J → Ω) :
    v ∈ _root_.GlobalTheory.ZH.DualLattice.dotDual S N ↔ ∀ w ∈ N, w ⬝ᵥ v ∈ S :=
  Iff.rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
open Matrix in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type}
  [Fintype J] in

theorem _root_.GlobalTheory.ZH.DualLattice.mem_dotDual_span {I : Type} (a : I → J → Ω) (v : J → Ω) :
    v ∈ _root_.GlobalTheory.ZH.DualLattice.dotDual S (Submodule.span S (Set.range a)) ↔ ∀ i, a i ⬝ᵥ v ∈ S := by
  rw [mem_dotDual_iff']
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h i
    | zero =>
      rw [zero_dotProduct]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [add_dotProduct]
      exact add_mem hx hy
    | smul c x _ hx =>
      rw [smul_dotProduct, Subalgebra.smul_def, smul_eq_mul]
      exact mul_mem c.2 hx

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
open Matrix in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type}
  [Fintype J] in

theorem _root_.GlobalTheory.ZH.DualLattice.mem_span_rows (B : Matrix J J Ω) (v : J → Ω) :
    v ∈ Submodule.span S (Set.range B) ↔ ∃ c : J → Ω, (∀ i, c i ∈ S) ∧ c ᵥ* B = v := by
  change v ∈ Submodule.span S (Set.range fun i => B i) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => c i, fun i => (c i).2, ?_⟩
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => ⟨c i, hc i⟩, ?_⟩
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]

variable [DecidableEq J]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
open Matrix in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type}
  [Fintype J] in
variable [DecidableEq J] in

theorem _root_.GlobalTheory.ZH.DualLattice.dotDual_span_rows {A B : Matrix J J Ω} (h : A * Bᵀ = 1) :
    _root_.GlobalTheory.ZH.DualLattice.dotDual S (Submodule.span S (Set.range A)) =
      Submodule.span S (Set.range B) := by
  ext v
  refine (_root_.GlobalTheory.ZH.DualLattice.mem_dotDual_span S (fun i => A i) v).trans
    ((?_ : _ ↔ _).trans (_root_.GlobalTheory.ZH.DualLattice.mem_span_rows S B v).symm)
  have hBA : Bᵀ * A = 1 := mul_eq_one_comm.mp h
  constructor
  · intro hv
    refine ⟨A *ᵥ v, fun i => hv i, ?_⟩
    rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  · rintro ⟨c, hc, rfl⟩ i
    have hAc : A *ᵥ (c ᵥ* B) = c := by
      rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    show (A *ᵥ (c ᵥ* B)) i ∈ S
    rw [hAc]
    exact hc i

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
open Matrix in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type}
  [Fintype J] in
variable [DecidableEq J] in

theorem _root_.GlobalTheory.ZH.DualLattice.span_eq_span_minor {n : ℕ} (g : Fin n → J → Ω) (k : J → Fin n)
    (h0 : (Matrix.of fun i j => g (k i) j).det ≠ 0)
    (hd : ∀ l : J → Fin n, (Matrix.of fun i j => g (l i) j).det /
      (Matrix.of fun i j => g (k i) j).det ∈ S)
    {s t : Ω} (hs : s ≠ 0) (ht : t ≠ 0) (hst : s / t ∈ S) (hts : t / s ∈ S) :
    Submodule.span S (Set.range fun m j => g m j / s) =
      Submodule.span S (Set.range (t⁻¹ • Matrix.of fun i j => g (k i) j : Matrix J J Ω)) := by
  set G : Matrix J J Ω := Matrix.of fun i j => g (k i) j with hG
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    rw [SetLike.mem_coe, _root_.GlobalTheory.ZH.DualLattice.mem_span_rows]
    refine ⟨(t / s) • G.det⁻¹ • Gᵀ.cramer (g m), fun i => ?_, ?_⟩
    · have hc : Gᵀ.cramer (g m) i =
          (Matrix.of fun i' j => g (Function.update k i m i') j).det := by
        rw [Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]
        congr 1
        ext i' j
        by_cases hi : i' = i
        · subst hi
          simp [Matrix.updateRow_apply]
        · simp [Matrix.updateRow_apply, Function.update_apply, hi, hG]
      have hmem := mul_mem hts (hd (Function.update k i m))
      simp only [Pi.smul_apply, smul_eq_mul, hc]
      convert hmem using 1
      rw [div_eq_mul_inv _ G.det]
      ring
    · rw [Matrix.smul_vecMul, Matrix.vecMul_smul, Matrix.smul_vecMul, ← Matrix.mulVec_transpose,
        Matrix.mulVec_cramer, Matrix.det_transpose]
      ext j
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hrow : (t⁻¹ • G) i = (s / t) • (fun j => g (k i) j / s) := by
      ext j
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, hG, Matrix.of_apply]
      field_simp
    rw [SetLike.mem_coe, hrow]
    have hmem := Submodule.smul_mem (Submodule.span S (Set.range fun m j => g m j / s))
      (⟨s / t, hst⟩ : S) (Submodule.subset_span ⟨k i, rfl⟩)
    rwa [Subalgebra.smul_def] at hmem

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
open Matrix in
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type}
  [Fintype J] in
variable [DecidableEq J] in

theorem _root_.GlobalTheory.ZH.DualLattice.smul_mul_smul_inv {G : Matrix J J Ω} (h0 : G.det ≠ 0) {t : Ω}
    (ht : t ≠ 0) : (t⁻¹ • G) * (t • G⁻¹ᵀ)ᵀ = 1 := by
  rw [Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h0), smul_smul, inv_mul_cancel₀ ht,
    one_smul]

end Algebra

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
open Matrix in

theorem _root_.GlobalTheory.ZH.DualLattice.exists_lat_dual : ∀ (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] (M : _root_.GlobalTheory.ZH.RatModel o Ω) (J : Type) [Fintype J]
    [DecidableEq J] (n : ℕ) (g : Fin n → J → Ω) (θ : M.Z → Ω),
    (∀ z, θ z ≠ 0 ∧ ∃ W : M.Z.Opens, z ∈ W ∧ ∀ x ∈ W,
      θ z / θ x ∈ M.O x ∧
        θ x / θ z ∈ M.O x) →
    M.HasDiv
      (fun k : J → Fin n => Matrix.det (Matrix.of fun i j => g (k i) j)) →
    ∃ EE : M.Lat J, ∀ z (w : J → Ω),
      w ∈ Submodule.span (M.O z)
          (Set.range fun k j => g k j / θ z) ↔
        ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z := by
  intro o Ω _ _ _ M J _ _ n g θ hθ hdiv
  have key : ∀ (z x : M.Z) (k : J → Fin n),
      M.Div
        (fun k : J → Fin n => Matrix.det (Matrix.of fun i j => g (k i) j)) k x →
      θ z / θ x ∈ M.O x →
      θ x / θ z ∈ M.O x →
      Submodule.span (M.O x) (Set.range fun m j => g m j / θ x) =
          Submodule.span (M.O x)
            (Set.range ((θ z)⁻¹ • Matrix.of fun i j => g (k i) j : Matrix J J Ω)) ∧
        _root_.GlobalTheory.ZH.DualLattice.dotDual (M.O x)
            (Submodule.span (M.O x)
              (Set.range fun m j => g m j / θ x)) =
          Submodule.span (M.O x)
            (Set.range (θ z • (Matrix.of fun i j => g (k i) j : Matrix J J Ω)⁻¹ᵀ)) := by
    intro z x k hk hzx hxz
    have hspan := _root_.GlobalTheory.ZH.DualLattice.span_eq_span_minor (M.O x) g k
      hk.1 hk.2 (hθ x).1 (hθ z).1 hxz hzx
    refine ⟨hspan, ?_⟩
    rw [hspan]
    exact _root_.GlobalTheory.ZH.DualLattice.dotDual_span_rows _
      (_root_.GlobalTheory.ZH.DualLattice.smul_mul_smul_inv hk.1 (hθ z).1)
  let E : ∀ z : M.Z, Submodule (M.O z) (J → Ω) :=
    fun z => _root_.GlobalTheory.ZH.DualLattice.dotDual (M.O z)
      (Submodule.span (M.O z) (Set.range fun m j => g m j / θ z))
  refine ⟨⟨E, ?_⟩, ?_⟩
  · intro z
    obtain ⟨k, hk⟩ := hdiv z
    obtain ⟨W, hzW, hW⟩ := (hθ z).2
    let V : M.Z.Opens :=
      ⟨{x | M.Div
          (fun k : J → Fin n => Matrix.det (Matrix.of fun i j => g (k i) j)) k x},
        M.isOpen_setOf_div _ k⟩
    refine ⟨W ⊓ V, θ z • (Matrix.of fun i j => g (k i) j : Matrix J J Ω)⁻¹ᵀ, ⟨hzW, hk⟩, ?_,
      fun x hx => (key z x k hx.2 (hW x hx.1).1 (hW x hx.1).2).2⟩
    simp [Matrix.det_smul, Matrix.det_nonsing_inv, hk.1, (hθ z).1]
  · intro z w
    obtain ⟨k, hk⟩ := hdiv z
    have hone : θ z / θ z ∈ M.O z := by
      rw [div_self (hθ z).1]
      exact one_mem _
    obtain ⟨hN, hE⟩ := key z z k hk hone hone
    have hAB := _root_.GlobalTheory.ZH.DualLattice.smul_mul_smul_inv
      (J := J) (G := (Matrix.of fun i j => g (k i) j : Matrix J J Ω)) hk.1 (hθ z).1
    have hBA := congrArg Matrix.transpose hAB
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at hBA
    show _ ↔ ∀ v ∈ _root_.GlobalTheory.ZH.DualLattice.dotDual _ _, _
    rw [hE, hN, ← _root_.GlobalTheory.ZH.DualLattice.dotDual_span_rows _ hBA,
      mem_dotDual_iff']
    constructor
    · intro h v hv
      rw [dotProduct_comm]
      exact h v hv
    · intro h v hv
      rw [dotProduct_comm]
      exact h v hv

end GlobalTheory.ZH.DualLattice
end
