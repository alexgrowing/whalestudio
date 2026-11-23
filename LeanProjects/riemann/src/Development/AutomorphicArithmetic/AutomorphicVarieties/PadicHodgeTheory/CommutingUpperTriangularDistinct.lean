import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ScalarMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalizeThreeByThree
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

namespace UpperTheory.V.Loc

private theorem commuting_upper_triangular_distinct {K : Type} [Field K] (d : Fin 3 → K) (hd : Function.Injective d)
    (A k B : Matrix (Fin 3) (Fin 3) K) (h : A * k = k * B)
    (hA : ∀ a b, wt a b < 0 → A a b = 0) (hB : ∀ a b, wt a b < 0 → B a b = 0)
    (hA' : ∀ a, A a a = d a) (hB' : ∀ a, B a a = d a) : ∀ a b, wt a b < 0 → k a b = 0 := by
  have a10 := hA 1 0 (by decide)
  have a20 := hA 2 0 (by decide)
  have a21 := hA 2 1 (by decide)
  have b10 := hB 1 0 (by decide)
  have b20 := hB 2 0 (by decide)
  have b21 := hB 2 1 (by decide)
  have d01 : d 0 - d 1 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d02 : d 0 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d12 : d 1 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21, hA', hB'] at e20 e21 e10
  have k20 : k 2 0 = 0 := (mul_eq_zero.1 (show (d 0 - d 2) * k 2 0 = 0 by linear_combination -e20)).resolve_left d02
  rw [k20] at e21 e10
  have k21 : k 2 1 = 0 := (mul_eq_zero.1 (show (d 1 - d 2) * k 2 1 = 0 by linear_combination -e21)).resolve_left d12
  have k10 : k 1 0 = 0 := (mul_eq_zero.1 (show (d 0 - d 1) * k 1 0 = 0 by linear_combination -e10)).resolve_left d01
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | assumption

private theorem diagonalize_three_by_three_split {K : Type} [Field K] (d : Fin 3 → K) (hd : Function.Injective d)
    (M : Matrix (Fin 3) (Fin 3) K) (hM : M.charpoly = ∏ a, (X - C (d a))) :
    ∃ h : GL (Fin 3) K, ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M * h = Matrix.diagonal d :=
  _root_.UpperTheory.Reformulated.B.DiagonalizeThreeByThree.diagonalize_three_by_three_split d hd M hM

private theorem three_eigenvalue_product_zero {K : Type} [Field K] (d p : Fin 3 → K) (hd : Function.Injective d)
    (N : Matrix (Fin 3) (Fin 3) K)
    (h0 : (N - Matrix.scalar _ (p 0)) * (Matrix.diagonal d - Matrix.scalar _ (d 1)) *
      (Matrix.diagonal d - Matrix.scalar _ (d 2)) = 0)
    (h1 : (Matrix.diagonal d - Matrix.scalar _ (d 0)) * (N - Matrix.scalar _ (p 1)) *
      (Matrix.diagonal d - Matrix.scalar _ (d 2)) = 0)
    (h2 : (Matrix.diagonal d - Matrix.scalar _ (d 0)) * (Matrix.diagonal d - Matrix.scalar _ (d 1)) *
      (N - Matrix.scalar _ (p 2)) = 0) :
    (∀ a b, wt a b < 0 → N a b = 0) ∧ ∀ a, N a a = p a := by
  have d01 : d 0 - d 1 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d02 : d 0 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d12 : d 1 - d 2 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d10 : d 1 - d 0 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d20 : d 2 - d 0 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have d21 : d 2 - d 1 ≠ 0 := sub_ne_zero.2 (hd.ne (by decide))
  have hs : ∀ c : K, Matrix.diagonal d - Matrix.scalar (Fin 3) c = Matrix.diagonal fun i => d i - c := fun c => by
    rw [Matrix.scalar_apply, Matrix.diagonal_sub]
  simp only [hs, Matrix.diagonal_mul_diagonal] at h0 h1 h2
  have e00 := congrFun (congrFun h0 0) 0
  have e10 := congrFun (congrFun h0 1) 0
  have e20 := congrFun (congrFun h0 2) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e21 := congrFun (congrFun h2 2) 1
  have e22 := congrFun (congrFun h2 2) 2
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, d01, d02, d12, d10, d20, d21, sub_eq_zero] at e00 e10 e20 e11 e21 e22
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | assumption
  · intro a
    fin_cases a <;> assumption

private theorem conjugate_representation_mat {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) (h : GL (Fin 3) R) (g : D)
    (hg : (r g).right = 1) : (conjBy h⁻¹ r g).mat =
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem padic_int_ringHom_injective {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [CharZero K] (φ : ℤ_[l] →+* K) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) hx

private theorem exists_inertia_distinct_characters {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) (K : Type) [Field K] [CharZero K] [Algebra O K] :
    ∃ s ∈ Iq l, Function.Injective fun a => algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s) := by
  obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((cycInertia l).2 D.τ.ker D.τ_open).2
  refine ⟨s, hs2, ?_⟩
  let φ : ℤ_[l] →+* K := (algebraMap O K).comp (algebraMap ℤ_[l] O)
  let t : Kˣ := Units.map (algebraMap O K : O →* K) (D.Ψ s)
  have ht : t = Units.map (φ : ℤ_[l] →* K) (cyc l l s) ^ D.e := by
    have h1 : D.τ s = 1 := hs1
    simp only [t]
    rw [D.Ψ_I s hs2, h1, mul_one, map_pow]
    rfl
  have hinf : ¬ IsOfFinOrder t := by
    rw [ht]
    intro h
    have h2 := h.of_pow (by have := D.e_pos; omega)
    exact hs ((Function.Injective.isOfFinOrder_iff (f := Units.map (φ : ℤ_[l] →* K))
      (Units.map_injective (padic_int_ringHom_injective φ))).1 h2)
  have e : ∀ a, algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s) = ((t ^ wt1 a : Kˣ) : K) := fun a =>
    congrArg Units.val (map_zpow (Units.map (algebraMap O K : O →* K)) (D.Ψ s) (wt1 a))
  intro a b hab
  simp only [e] at hab
  have h3 := injective_zpow_iff_not_isOfFinOrder.2 hinf (Units.ext hab)
  simp only [wt1] at h3
  exact Fin.ext (by omega)

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.lemma2b :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (K : Type) [Field K] [CharZero K] [Algebra O K] (r : GQ l →* GG 3 K), D.On U r → (∃ h, UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) r h) ∧ ∀ h h', UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) r h → UpperTheory.V.UnitaryThreeInertia.TriIn D.η D.Ψ (Iq l) r h' → ∀ a b, wt a b < 0 → ((h⁻¹ * h' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
  intro hP l _ O _ _ _ _ _ _ _ D U K _ _ _ r hr
  obtain ⟨hch, hpr⟩ := UpperTheory.V.Loc.lemma2a hP D U K r hr
  have hm : ∀ g, D.η g = 1 → (r g).right = 1 := by
    obtain ⟨f, rfl, -⟩ := hr
    exact fun g hg => (U.r.hasMult g).trans hg
  obtain ⟨s, hs, hd⟩ := exists_inertia_distinct_characters D K
  have hηs := D.η_unr s hs
  constructor
  · obtain ⟨h, hh⟩ := diagonalize_three_by_three_split _ hd _ (hch s hs)
    have hc : ∀ (A : Matrix (Fin 3) (Fin 3) K) (c : K),
        ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (h : Matrix (Fin 3) (Fin 3) K) - Matrix.scalar _ c =
          ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A - Matrix.scalar _ c) * (h : Matrix (Fin 3) (Fin 3) K) := by
      intro A c
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc _ (Matrix.scalar _ c),
        Matrix.scalar_commute c (fun _ => Commute.all _ _), ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hc3 : ∀ A B C : Matrix (Fin 3) (Fin 3) K, A * B * C = 0 →
        (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A * (h : Matrix (Fin 3) (Fin 3) K)) *
          (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B * (h : Matrix (Fin 3) (Fin 3) K)) *
          (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * C * (h : Matrix (Fin 3) (Fin 3) K)) = 0 := by
      intro A B C h0
      have : ∀ Y : Matrix (Fin 3) (Fin 3) K,
          (h : Matrix (Fin 3) (Fin 3) K) * (((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Y) = Y :=
        fun Y => by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      simp only [Matrix.mul_assoc, this]
      rw [← Matrix.mul_assoc B, ← Matrix.mul_assoc A, ← Matrix.mul_assoc A, h0, Matrix.zero_mul, Matrix.mul_zero]
    have hI : ∀ x ∈ Iq l, (∀ a b, wt a b < 0 → (conjBy h⁻¹ r x).mat a b = 0) ∧
        ∀ a, (conjBy h⁻¹ r x).mat a a = algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a x) := by
      intro x hx
      rw [conjugate_representation_mat r h x (hm x (D.η_unr x hx))]
      refine three_eigenvalue_product_zero _ (fun a => algebraMap O K (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a x)) hd _ ?_ ?_ ?_
      · rw [← hh, hc, hc, hc]
        exact hc3 _ _ _ (hpr ![x, s, s] fun a => by fin_cases a <;> assumption)
      · rw [← hh, hc, hc, hc]
        exact hc3 _ _ _ (hpr ![s, x, s] fun a => by fin_cases a <;> assumption)
      · rw [← hh, hc, hc, hc]
        exact hc3 _ _ _ (hpr ![s, s, x] fun a => by fin_cases a <;> assumption)
    refine ⟨h, fun g hg => ?_, fun x hx _ => (hI x hx).2⟩
    have hx : g * s * g⁻¹ ∈ Iq l := (iqBasic l).1.conj_mem s hs g
    have hr1 : ∀ x, D.η x = 1 → (conjBy h⁻¹ r x).right = 1 := fun x hx => by simp [conjBy, hm x hx]
    have hmul : ∀ x y, D.η x = 1 →
        (conjBy h⁻¹ r (x * y)).mat = (conjBy h⁻¹ r x).mat * (conjBy h⁻¹ r y).mat := fun x y hx => by
      rw [map_mul]
      simp only [GG.mat, SemidirectProduct.mul_left, hr1 x hx, sgnAct_one, Units.val_mul]
    refine commuting_upper_triangular_distinct _ hd (conjBy h⁻¹ r (g * s * g⁻¹)).mat _ (conjBy h⁻¹ r s).mat ?_ (hI _ hx).1 (hI s hs).1
      (fun a => ?_) (hI s hs).2
    · rw [← hmul _ _ (D.η_unr _ hx), ← hmul _ _ hg, inv_mul_cancel_right]
    · rw [(hI _ hx).2]
      simp only [UpperTheory.V.UnitaryThreeInertia.psi, map_mul, map_inv, mul_inv_cancel_comm]
  · intro h h' H H'
    refine commuting_upper_triangular_distinct _ hd (conjBy h⁻¹ r s).mat _ (conjBy h'⁻¹ r s).mat ?_ (H.tri s hηs) (H'.tri s hηs)
      (H.ine s hs hηs) (H'.ine s hs hηs)
    rw [conjugate_representation_mat r h s (hm s hηs), conjugate_representation_mat r h' s (hm s hηs), Units.val_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
