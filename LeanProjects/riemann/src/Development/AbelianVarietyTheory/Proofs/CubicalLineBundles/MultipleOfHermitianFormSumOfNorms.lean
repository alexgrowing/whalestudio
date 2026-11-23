import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.HermSq

section general

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (br : R →+* R)

def IsSumOfNorms (B : M → M → R) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (l : J → M →ₗ[R] R), ∀ x y, B x y = ∑ k, l k x * br (l k y)

variable {br}

theorem IsSumOfNorms.congr {B B' : M → M → R} (h : IsSumOfNorms br B) (e : ∀ x y, B' x y = B x y) : IsSumOfNorms br B' := by
  obtain ⟨J, _, l, hl⟩ := h
  exact ⟨J, inferInstance, l, fun x y => (e x y).trans (hl x y)⟩

theorem IsSumOfNorms.zero : IsSumOfNorms br (fun (_ _ : M) => (0 : R)) :=
  ⟨Empty, inferInstance, fun e => e.elim, fun x y => by simp⟩

theorem IsSumOfNorms.one (f : M →ₗ[R] R) : IsSumOfNorms br (fun x y => f x * br (f y)) :=
  ⟨Unit, inferInstance, fun _ => f, fun x y => by simp⟩

theorem IsSumOfNorms.add {B B' : M → M → R} (h : IsSumOfNorms br B) (h' : IsSumOfNorms br B') :
    IsSumOfNorms br (fun x y => B x y + B' x y) := by
  obtain ⟨J, _, l, hl⟩ := h
  obtain ⟨J', _, l', hl'⟩ := h'
  refine ⟨J ⊕ J', inferInstance, Sum.elim l l', fun x y => ?_⟩
  simp [Fintype.sum_sum_type, hl, hl']

theorem IsSumOfNorms.nsmul {B : M → M → R} (h : IsSumOfNorms br B) (n : ℕ) :
    IsSumOfNorms br (fun x y => (n : R) * B x y) := by
  induction n with
  | zero => exact IsSumOfNorms.zero.congr fun x y => by simp
  | succ n ih => exact (ih.add h).congr fun x y => by push_cast; ring

theorem IsSumOfNorms.comp {B : M → M → R} (h : IsSumOfNorms br B) (Z : M →ₗ[R] M) :
    IsSumOfNorms br (fun x y => B (Z x) (Z y)) := by
  obtain ⟨J, _, l, hl⟩ := h
  exact ⟨J, inferInstance, fun k => l k ∘ₗ Z, fun x y => hl _ _⟩

theorem IsSumOfNorms.sum {κ : Type} (s : Finset κ) {B : κ → M → M → R} (h : ∀ i, IsSumOfNorms br (B i)) :
    IsSumOfNorms br (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsSumOfNorms.zero.congr fun x y => by simp
  | insert a s ha ih => exact ((h a).add ih).congr fun x y => by rw [Finset.sum_insert ha]

variable (g : M → M →ₗ[R] R) (herm : ∀ x y, g x y = br (g y x))

include herm in

theorem exists_step (e : M) (q : ℕ) (hq : g e e = q) :
    ∃ Z : M →ₗ[R] M, Z e = 0 ∧
      ∀ x y, g (Z y) (Z x) = (q : R) ^ 2 * g y x - q * (g e x * br (g e y)) := by
  refine ⟨(q : R) • LinearMap.id - (g e).smulRight e, by simp [hq], fun x y => ?_⟩
  have h1 : ∀ a, g (((q : R) • LinearMap.id - (g e).smulRight e : M →ₗ[R] M) y) a
      = q * g y a - br (g e y) * g e a := by
    intro a
    rw [herm]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      map_sub, map_smul, smul_eq_mul, map_mul, map_natCast]
    rw [← herm, ← herm e a]
  rw [h1]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      map_sub, map_smul, smul_eq_mul, hq]
  rw [herm y e]
  ring

variable (pos : ∀ x, x ≠ 0 → ∃ q : ℕ, 1 ≤ q ∧ g x x = q)

include herm pos in
theorem exists_kill {κ : Type} (v : κ → M) (s : Finset κ) :
    ∃ (N : ℕ) (Z : M →ₗ[R] M), 1 ≤ N ∧ (∀ i ∈ s, Z (v i) = 0) ∧
      IsSumOfNorms br (fun x y => (N : R) * g y x - g (Z y) (Z x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, LinearMap.id, le_rfl, by simp, IsSumOfNorms.zero.congr fun x y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨N, Z, hN, hZ, hB⟩ := ih
    by_cases he : Z (v a) = 0
    · refine ⟨N, Z, hN, fun i hi => ?_, hB⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      exacts [he, hZ i hi]
    · obtain ⟨q, hq1, hq⟩ := pos _ he
      obtain ⟨Y, hY, hY'⟩ := exists_step g herm _ q hq
      refine ⟨q ^ 2 * N, Y ∘ₗ Z, Nat.mul_pos (pow_pos hq1 2) hN, fun i hi => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hY
        · simp [hZ i hi]
      · refine ((hB.nsmul (q ^ 2)).add (((IsSumOfNorms.one (g (Z (v a)))).comp Z).nsmul q)).congr fun x y => ?_
        simp only [LinearMap.comp_apply, hY']
        push_cast
        ring

include herm pos in

theorem exists_split {n : ℕ} (u w : Fin n → M) (fr : ∀ a, a = ∑ i, g (w i) a • u i) :
    ∃ (N m : ℕ) (l : M →ₗ[R] (Fin m → R)) (r : (Fin m → R) →ₗ[R] M), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧
      ∀ x y, (N : R) * g y x = ∑ k, l x k * br (l y k) := by
  classical
  obtain ⟨N, Z, hN, hZ, hB⟩ := exists_kill g herm pos u Finset.univ
  have hZ0 : ∀ a, Z a = 0 := fun a => by
    rw [fr a, map_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [map_smul, hZ i hi, smul_zero]
  have hB' : IsSumOfNorms br (fun x y => (N : R) * g y x) := hB.congr fun x y => by simp [hZ0]
  have key : ∀ e : M, ∃ K : ℕ, IsSumOfNorms br (fun x y => (K : R) * g y x - g e x * br (g e y)) := by
    intro e
    by_cases he : e = 0
    · refine ⟨0, IsSumOfNorms.zero.congr fun x y => ?_⟩
      subst he
      rw [herm 0 x]; simp
    · obtain ⟨q, hq1, hq⟩ := pos _ he
      obtain ⟨Y, -, hY'⟩ := exists_step g herm _ q hq
      obtain ⟨c, hc⟩ : ∃ c : ℕ, N * q = c + 1 := ⟨N * q - 1, by have := Nat.mul_pos hN hq1; omega⟩
      have hc' : (N : R) * q = c + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → R) hc
      refine ⟨N * q ^ 2, ((hB'.comp Y).add ((IsSumOfNorms.one (g e)).nsmul c)).congr fun x y => ?_⟩
      simp only [hY']
      push_cast
      linear_combination (g e x * br (g e y)) * hc'
  choose K hK using key
  obtain ⟨J, _, l, hl⟩ := hB'.add (IsSumOfNorms.sum Finset.univ fun i => hK (w i))
  let eqv := Fintype.equivFin (Fin n ⊕ J)
  refine ⟨N + ∑ i, K (w i), Fintype.card (Fin n ⊕ J),
    LinearMap.pi fun k => Sum.elim (fun i => g (w i)) l (eqv.symm k),
    ∑ i, (LinearMap.proj (eqv (Sum.inl i)) : (Fin _ → R) →ₗ[R] R).smulRight (u i), by omega, ?_, fun x y => ?_⟩
  · ext a
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      LinearMap.pi_apply, Equiv.symm_apply_apply, Sum.elim_inl, LinearMap.id_apply]
    exact (fr a).symm
  · simp only [LinearMap.pi_apply]
    rw [eqv.symm.sum_comp (fun k => Sum.elim (fun i => g (w i)) l k x * br (Sum.elim (fun i => g (w i)) l k y)),
      Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← hl x y]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
    push_cast
    ring

end general

theorem kForm_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (N m : ℕ) (l : D.La →ₗ[OK H] (Fin m → OK H)) (r : (Fin m → OK H) →ₗ[OK H] D.La), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧ ∀ x y, (N : 𝓞 E) * (h x y : OK H) = ∑ k, ((l x k : OK H) : 𝓞 E) * H.bar (l y k : OK H) := by
  intro E _ _ _ H D ε h hh hpos
  obtain ⟨h₀, -, huniq, hherm, -, hdiag, -, n, u, w, fr⟩ := GlobalTheory.CM.exists_kForm E H D ε
  obtain ⟨-, -, ⟨br, hbr, -⟩, -⟩ := GlobalTheory.CM.OK_isDedekindDomain_and_projective E H
  obtain rfl := huniq h hh
  let g : D.La → D.La →ₗ[OK H] OK H := fun y =>
    { toFun := fun x => h₀ x y
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun c a => by rw [map_smul]; rfl }
  obtain ⟨N, m, l, r, hN, hr, hl⟩ := exists_split (br := br.toRingHom) g
    (fun x y => Subtype.ext ((hherm x y).trans (hbr _).symm))
    (fun x hx => by
      have h1 := hpos x hx
      refine ⟨((ε : ℤ) * D.EF (H.w0 • x) x).toNat, by omega, Subtype.ext ?_⟩
      refine (hdiag x).trans ?_
      conv_lhs => rw [← Int.toNat_of_nonneg h1.le]
      rw [Int.cast_natCast, SubringClass.coe_natCast]) u w fr
  refine ⟨N, m, l, r, hN, hr, fun x y => ?_⟩
  have := congrArg (OK H).val (hl x y)
  simp only [map_mul, map_sum, map_natCast, Subalgebra.coe_val] at this
  simp only [← hbr]
  exact this

end GlobalTheory.CM.HermSq
