import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitOfForallMaximal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq.Arch

theorem isUnit_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (c : Coef l) (n : ℕ) : IsUnit (2 : Qn c n) := by
  have hodd : Odd (l ^ n) := ((Fact.out : l.Prime).odd_of_ne_two hl).pow
  obtain ⟨k, hk⟩ := hodd
  have h0 : ((l ^ n : ℕ) : Qn c n) = 0 := by
    have := kill c n (1 : Qn c n)
    rwa [nsmul_eq_mul, mul_one] at this
  have e : (2 : Qn c n) * ((k + 1 : ℕ) : Qn c n) = ((l ^ n : ℕ) : Qn c n) + 1 := by
    rw [hk]; push_cast; ring
  rw [h0, zero_add] at e
  exact isUnit_iff_exists_inv.mpr ⟨_, e⟩

theorem trace_eq_zero {R : Type} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) (hXX : X * X = 1)
    (hdet : X.det = -1) : X.trace = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  have e00 := congrFun (congrFun hXX 0) 0
  have e10 := congrFun (congrFun hXX 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  linear_combination (X 0 0 - (X 0 0 + X 1 1)) * e00 + X 0 0 * hdet + X 0 1 * e10

theorem card_fixed_cc (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (n : ℕ) (w : InfinitePlace ℚ) (s : G ℚ Ω) (hs : IsCCAt w s) :
    Nat.card {v : Mn c n // matQ c n W hint s *ᵥ v = v} = Nat.card (Qn c n) := by
  obtain ⟨j, hj, -⟩ := hs
  have hss : s * s = 1 := by
    ext x
    apply j.injective
    show j (s (s x)) = j x
    rw [hj, hj]; simp
  have hXX : matQ c n W hint s * matQ c n W hint s = 1 := by
    rw [← matQ_mul, hss, matQ_one]
  have hd : (mat W s).det = -1 := by
    have h := hW.odd s ⟨j, hj⟩
    have h2 : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
      simp [dt, mat, Matrix.GeneralLinearGroup.val_det_apply]
    rw [← h2, h]; simp
  have hdet : (matQ c n W hint s).det = -1 := by
    rw [Matrix.det_fin_two] at hd ⊢
    simp only [matQ_apply]
    rw [← map_mul, ← map_mul, ← map_sub, ← map_one (red c n), ← map_neg]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_one]
    exact hd
  exact GlobalTheory.OddInvolution.card_fixed l (Qn c n) _ (isUnit_two l hW.l_odd c n) hXX hdet
    (trace_eq_zero _ hXX hdet)

theorem archimedean_h0_card_eq : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ cc : InfinitePlace ℚ → G ℚ Ω, (∀ w, w.IsReal → IsCCAt w (cc w)) → archH0Card S (rhoS c n W hint S hN) cc = Nat.card (Qn c n) := by
  intro l _ Ω _ _ _ e S A W hW c hint hN n _ cc hcc
  classical
  unfold archH0Card
  have hfil : (Finset.univ.filter (fun w : InfinitePlace ℚ => w.IsReal)) = {Rat.infinitePlace} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ Rat.isReal_infinitePlace⟩
  rw [IsTotallyReal.nrComplexPlaces_eq_zero ℚ, pow_zero, mul_one]
  convert Finset.prod_singleton (fun w : InfinitePlace ℚ =>
    Nat.card {m : Mn c n // rhoS c n W hint S hN (toGS Ω _ (cc w)) m = m}) Rat.infinitePlace using 1
  · rw [hfil]
  · exact (card_fixed_cc l Ω e S A W hW c hint n _ _ (hcc _ Rat.isReal_infinitePlace)).symm

end GlobalTheory.Ord2.GwIneq.Arch
