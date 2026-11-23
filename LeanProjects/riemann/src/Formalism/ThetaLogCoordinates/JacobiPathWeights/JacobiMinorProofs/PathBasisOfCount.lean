import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathProductHighestWeight

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace MinorDeterminantBasis

section Abstract

variable {σ X : Type} [Fintype X] [DecidableEq X]

def cmat (m : X → σ →₀ ℕ) (F : X → MvPolynomial σ ℤ) : Matrix X X ℤ :=
  Matrix.of fun x y => coeff (m y) (F x)

theorem expand (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S] (x : X) :
    MvPolynomial.map (Int.castRingHom S) (F x) =
      ∑ y, ((cmat m F).map (Int.castRingHom S)) x y • monomial (m y) (1 : S) := by
  classical
  ext d
  rw [coeff_map, MvPolynomial.coeff_sum]
  simp only [coeff_smul, coeff_monomial, Matrix.map_apply, cmat, Matrix.of_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hd : d ∈ Set.range m
  · obtain ⟨y₀, rfl⟩ := hd
    rw [Finset.sum_eq_single y₀]
    · simp
    · intro y _ hy
      rw [if_neg (hm.ne hy)]
    · simp
  · have h0 : coeff d (F x) = 0 := by
      by_contra h
      exact hd (hF x d (mem_support_iff.mpr h))
    rw [h0, map_zero, Finset.sum_eq_zero]
    intro y _
    rw [if_neg]
    rintro rfl
    exact hd ⟨y, rfl⟩

private theorem sum_smul_sum_smul_eq_sum_mul_smul {S : Type} [CommRing S] (M : Matrix X X S) (e : X → MvPolynomial σ S)
    (g : X → S) : ∑ x, g x • ∑ y, M x y • e y = ∑ y, (∑ x, g x * M x y) • e y := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem rows_indep (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S]
    (h : LinearIndependent S fun x => MvPolynomial.map (Int.castRingHom S) (F x)) :
    LinearIndependent S ((cmat m F).map (Int.castRingHom S)).row := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  apply h g
  simp only [expand m hm F hF S, sum_smul_sum_smul_eq_sum_mul_smul]
  have hy : ∀ y, ∑ x, g x * ((cmat m F).map (Int.castRingHom S)) x y = 0 := by
    intro y
    have := congrFun hg y
    simpa [Finset.sum_apply, Matrix.row] using this
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [hy y, zero_smul]

theorem det_unit (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x)) :
    IsUnit (cmat m F).det := by
  rw [Int.isUnit_iff_natAbs_eq]
  by_contra hne
  obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hpp⟩
  have hrows := rows_indep m hm F hF (ZMod p) (hp p ⟨hpp⟩)
  have hu : IsUnit ((cmat m F).map (Int.castRingHom (ZMod p))) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (by simpa [Matrix.row] using hrows)
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  apply hu
  have hdet : ((cmat m F).map (Int.castRingHom (ZMod p))).det = Int.castRingHom (ZMod p) (cmat m F).det :=
    (RingHom.map_det _ _).symm
  rw [hdet, eq_intCast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.ofNat_dvd_left.mpr hpd)

theorem basis_of (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x))
    (R : Type) [CommRing R] :
    LinearIndependent R (fun x => MvPolynomial.map (Int.castRingHom R) (F x)) ∧
    Submodule.span R (Set.range fun x => MvPolynomial.map (Int.castRingHom R) (F x)) =
      Submodule.span R (Set.range fun y => monomial (m y) (1 : R)) := by
  classical
  set M := (cmat m F).map (Int.castRingHom R) with hM
  have hdet : IsUnit M.det := by
    have h1 := (det_unit m hm F hF hp).map (Int.castRingHom R)
    rw [RingHom.map_det] at h1
    exact h1
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have he : LinearIndependent R fun y => (monomial (m y) (1 : R) : MvPolynomial σ R) := by
    have h1 := (MvPolynomial.basisMonomials σ R).linearIndependent.comp m hm
    simpa [Function.comp_def, MvPolynomial.coe_basisMonomials] using h1
  have hexp : ∀ x, MvPolynomial.map (Int.castRingHom R) (F x) =
      ∑ y, M x y • (monomial (m y) (1 : R) : MvPolynomial σ R) := expand m hm F hF R
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp he _ hg
    have hv : Matrix.vecMul g M = 0 := funext fun y => by
      simpa [Matrix.vecMul, dotProduct] using h0 y
    have h2 := congrArg (fun v => Matrix.vecMul v M⁻¹) hv
    simp only [Matrix.vecMul_vecMul, hMN, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
    exact congrFun h2
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      dsimp only
      rw [hexp]
      exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      have key : ∑ x, M⁻¹ y x • MvPolynomial.map (Int.castRingHom R) (F x) =
          (monomial (m y) (1 : R) : MvPolynomial σ R) := by
        simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul]
        have h1 : ∀ z, ∑ x, M⁻¹ y x * M x z = (1 : Matrix X X R) y z := fun z => by
          rw [← hNM, Matrix.mul_apply]
        simp only [h1, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      dsimp only
      rw [← key]
      exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

end Abstract

def expSet (n N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0}

theorem psi_map (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    psiPath R isVec μ N I = MvPolynomial.map (Int.castRingHom R) (psiPath ℤ isVec μ N I) := by
  have hfin := (pathProductDegrees ℤ n N isVec B μ I hμ hI).1
  have h := (MvPolynomial.map (Int.castRingHom R) :
    MvPolynomial (ℕ × Fin n) ℤ →+* MvPolynomial (ℕ × Fin n) R).toMonoidHom.map_finprod hfin
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h
  unfold psiPath
  rw [h]
  congr 1
  funext c
  rw [A1hw.map_pathWord]
  simp [map_X]

private theorem weight_indicator_fst_eq_sum {n : ℕ} (i : ℕ) (d : ℕ × Fin n →₀ ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) d = ∑ a, d (i, a) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ =>
    rw [map_add, h₁, h₂]
    simp [Finset.sum_add_distrib]
  | single x k =>
    obtain ⟨j, b⟩ := x
    rw [Finsupp.weight_single]
    by_cases hj : j = i
    · subst hj
      simp [Finsupp.single_apply, Prod.ext_iff]
    · simp [Finsupp.single_apply, Prod.ext_iff, hj]

theorem psi_support (hr : PolBRank) {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    ∀ d ∈ (psiPath ℤ isVec μ N I).support, d ∈ expSet n N B := by
  intro d hd i
  rw [← weight_indicator_fst_eq_sum]
  exact (pathProductDegrees ℤ n N isVec B μ I hμ hI).2 i (mem_support_iff.mp hd)

end MinorDeterminantBasis

open MinorDeterminantBasis

theorem path_basis_of_count : LemmaA2indep → PathIdxFinite → PolBRank → PathBasisOfCount := by
  classical
  intro hA hF hR n N isVec B hC R _
  haveI := hF n N isVec B
  letI := Fintype.ofFinite (PathIdx n N isVec B)
  obtain ⟨hcard, hfin, hspan⟩ := hR n N B
  haveI : Finite (expSet n N B) := hfin.to_subtype
  have hce : Nat.card (PathIdx n N isVec B) = Nat.card (expSet n N B) := by
    rw [hC, Nat.card_coe_set_eq, ← hcard]
    rfl
  obtain ⟨e⟩ := Finite.card_eq.mp hce
  let m : PathIdx n N isVec B → ℕ × Fin n →₀ ℕ := fun x => (e x : ℕ × Fin n →₀ ℕ)
  have hm : Function.Injective m := Subtype.val_injective.comp e.injective
  have hFs : ∀ x : PathIdx n N isVec B, ∀ d ∈ (psiPath ℤ isVec x.1.1 N x.1.2).support,
      d ∈ Set.range m := by
    intro x d hd
    have h1 := psi_support hR x.2.1 x.2.2.2.1 d hd
    exact ⟨e.symm ⟨d, h1⟩, by simp [m]⟩
  have hfun : ∀ (S : Type) [CommRing S], (fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom S) (psiPath ℤ isVec x.1.1 N x.1.2)) =
      fun x => psiPath S isVec x.1.1 N x.1.2 := fun S _ =>
    funext fun x => (psi_map S x.2.1 x.2.2.2.1).symm
  have hp : ∀ p : ℕ, ∀ _ : Fact p.Prime, LinearIndependent (ZMod p) fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom (ZMod p)) (psiPath ℤ isVec x.1.1 N x.1.2) := by
    intro p hpp
    rw [hfun]
    exact hA (ZMod p) n N isVec B
  obtain ⟨h1, h2⟩ := basis_of m hm (fun x => psiPath ℤ isVec x.1.1 N x.1.2) hFs hp R
  rw [hfun] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  rw [hspan R]
  congr 1
  ext f
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨m y, (e y).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨e.symm ⟨d, hd⟩, by simp [m]⟩

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
