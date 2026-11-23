import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaCohen
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace ExtRobba

open IsLocalRing WittVector Ideal TensorProduct

section WittInt

variable (p : ℕ) [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]

def wittInt : Subring (WittVector p L) := (WittVector.map (normInteger L).subtype).range

theorem mem_wittInt_iff {w : WittVector p L} : w ∈ wittInt p ↔ ∀ n, ‖w.coeff n‖ ≤ 1 := by
  constructor
  · rintro ⟨v, rfl⟩ n
    rw [WittVector.map_coeff]
    exact mem_normInteger.1 (v.coeff n).2
  · intro h
    refine ⟨WittVector.mk p fun n => ⟨w.coeff n, mem_normInteger.2 (h n)⟩, ?_⟩
    ext n
    simp [WittVector.map_coeff]

theorem teichmuller_mem_wittInt {a : L} (ha : ‖a‖ ≤ 1) : teichmuller p a ∈ wittInt p := by
  rw [mem_wittInt_iff]
  intro n
  cases n with
  | zero => simpa using ha
  | succ n => simp [teichmuller_coeff_pos]

variable [CharP L p] [PerfectRing L p]

theorem exists_mem_wittInt_eq_mul_p {w : WittVector p L} (hw : w ∈ wittInt p) (h0 : w.coeff 0 = 0) :
    ∃ v ∈ wittInt p, w = v * (p : WittVector p L) := by
  obtain ⟨v, hv⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero w).2 h0)
  refine ⟨v, ?_, hv.symm⟩
  rw [mem_wittInt_iff] at hw ⊢
  intro n
  have h1 := hw (n + 1)
  rw [← hv, mul_charP_coeff_succ, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h1

theorem coeff_eq_of_sub_mem {a b : WittVector p L} {m : ℕ}
    (h : a - b ∈ span {(p : WittVector p L) ^ m}) {i : ℕ} (hi : i < m) : a.coeff i = b.coeff i :=
  le_coeff_eq_iff_le_sub_coeff_eq_zero.2 ((mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 h) i hi

end WittInt

section Gamma

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]

set_option linter.unusedVariables false in

def WittOver (ι : ResidueField (normInteger K) →+* L) : Type _ := WittVector p L

variable (ι : ResidueField (normInteger K) →+* L)

instance : CommRing (WittOver p ι) := inferInstanceAs (CommRing (WittVector p L))

instance : Algebra (WittVector p (ResidueField (normInteger K))) (WittOver p ι) :=
  (WittVector.map ι).toAlgebra

def WittOver.equiv : WittOver p ι ≃+* WittVector p L := RingEquiv.refl _

theorem algebraMap_wittOver (w : WittVector p (ResidueField (normInteger K))) :
    WittOver.equiv p ι (algebraMap _ (WittOver p ι) w) = WittVector.map ι w := rfl

abbrev Gamma := WittOver p ι ⊗[WittVector p (ResidueField (normInteger K))] normInteger K

def gammaOfInt : normInteger K →+* Gamma p ι :=
  (Algebra.TensorProduct.includeRight :
    normInteger K →ₐ[WittVector p (ResidueField (normInteger K))] Gamma p ι).toRingHom

@[simp]
theorem gammaOfInt_apply (o : normInteger K) : gammaOfInt p ι o = 1 ⊗ₜ o := rfl

instance gammaAlgebraInt : Algebra (normInteger K) (Gamma p ι) := (gammaOfInt p ι).toAlgebra

theorem algebraMap_gamma (o : normInteger K) : algebraMap (normInteger K) (Gamma p ι) o = 1 ⊗ₜ o :=
  rfl

def gammaPi (ϖ : normInteger K) : Gamma p ι := 1 ⊗ₜ ϖ

abbrev redAlgebra : Algebra (WittVector p (ResidueField (normInteger K))) L :=
  (ι.comp WittVector.constantCoeff).toAlgebra

def gammaRed : Gamma p ι →+* L :=
  letI := redAlgebra p ι
  (Algebra.TensorProduct.lift
    ({ toRingHom := WittVector.constantCoeff.comp (WittOver.equiv p ι).toRingHom
       commutes' := fun r => by
        change (WittVector.map ι r).coeff 0 = ι (r.coeff 0)
        rw [WittVector.map_coeff] } : WittOver p ι →ₐ[WittVector p (ResidueField (normInteger K))] L)
    ({ toRingHom := ι.comp (residue (normInteger K))
       commutes' := fun r => by
        change ι (residue _ (cohenMap K p r)) = ι (r.coeff 0)
        rw [residue_cohenMap] } : normInteger K →ₐ[WittVector p (ResidueField (normInteger K))] L)
    (fun _ _ => Commute.all _ _)).toRingHom

@[simp]
theorem gammaRed_tmul (w : WittOver p ι) (o : normInteger K) :
    gammaRed p ι (w ⊗ₜ o) = (WittOver.equiv p ι w).coeff 0 * ι (residue _ o) := by
  let _ := redAlgebra p ι
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem gammaRed_surjective : Function.Surjective (gammaRed p ι) := by
  intro a
  refine ⟨(WittOver.equiv p ι).symm (teichmuller p a) ⊗ₜ 1, ?_⟩
  rw [gammaRed_tmul, map_one, map_one, mul_one]
  exact teichmuller_coeff_zero p a

def wittOverInt : Subring (WittOver p ι) := (wittInt p).comap (WittOver.equiv p ι).toRingHom

theorem mem_wittOverInt_iff {w : WittOver p ι} :
    w ∈ wittOverInt p ι ↔ ∀ n, ‖(WittOver.equiv p ι w).coeff n‖ ≤ 1 := by
  rw [wittOverInt, Subring.mem_comap]; exact mem_wittInt_iff p

theorem algebraMap_mem_wittOverInt (hι : ∀ a, ‖ι a‖ ≤ 1)
    (c : WittVector p (ResidueField (normInteger K))) :
    algebraMap _ (WittOver p ι) c ∈ wittOverInt p ι := by
  rw [mem_wittOverInt_iff]
  intro n
  rw [algebraMap_wittOver, WittVector.map_coeff]
  exact hι _

def gammaInt : Subring (Gamma p ι) :=
  Subring.closure {x | ∃ w ∈ wittOverInt p ι, ∃ o : normInteger K, x = w ⊗ₜ o}

theorem tmul_mem_gammaInt {w : WittOver p ι} (hw : w ∈ wittOverInt p ι) (o : normInteger K) :
    w ⊗ₜ o ∈ gammaInt p ι :=
  Subring.subset_closure ⟨w, hw, o, rfl⟩

theorem gammaPi_eq (ϖ : normInteger K) : gammaPi p ι ϖ = 1 ⊗ₜ ϖ := rfl

theorem natCast_eq_tmul_left (n : ℕ) : (n : Gamma p ι) = (n : WittOver p ι) ⊗ₜ (1 : normInteger K) := by
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom
    (R := WittVector p (ResidueField (normInteger K))) (A := WittOver p ι) (B := normInteger K))]
  rfl

theorem natCast_eq_tmul_right (n : ℕ) : (n : Gamma p ι) = (1 : WittOver p ι) ⊗ₜ (n : normInteger K) := by
  rw [← map_natCast (gammaOfInt p ι)]
  rfl

theorem wittOver_equiv_natCast (n : ℕ) : WittOver.equiv p ι (n : WittOver p ι) = (n : WittVector p L) :=
  map_natCast _ n

theorem exists_mem_gammaInt_gammaRed_eq {a : L} (ha : ‖a‖ ≤ 1) :
    ∃ x ∈ gammaInt p ι, gammaRed p ι x = a := by
  refine ⟨(WittOver.equiv p ι).symm (teichmuller p a) ⊗ₜ 1, tmul_mem_gammaInt p ι ?_ 1, ?_⟩
  · rw [mem_wittOverInt_iff, RingEquiv.apply_symm_apply]
    exact (mem_wittInt_iff p).1 (teichmuller_mem_wittInt p ha)
  · rw [gammaRed_tmul, map_one, map_one, mul_one, RingEquiv.apply_symm_apply]
    exact teichmuller_coeff_zero p a

theorem mul_natCast_tmul (a : WittOver p ι) (o : normInteger K) (n : ℕ) :
    (a * (n : WittOver p ι)) ⊗ₜ o = a ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((n : normInteger K) * o) := by
  calc (a * (n : WittOver p ι)) ⊗ₜ o
      = (a ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] o) * ((n : WittOver p ι) ⊗ₜ (1 : normInteger K)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    _ = (a ⊗ₜ o) * (n : Gamma p ι) := by rw [natCast_eq_tmul_left]
    _ = (a ⊗ₜ o) * ((1 : WittOver p ι) ⊗ₜ (n : normInteger K)) := by rw [natCast_eq_tmul_right]
    _ = a ⊗ₜ ((n : normInteger K) * o) := by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm]

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)
include hϖ
include hϖ

def gammaBasis : Module.Basis (Fin (ramIdx p hϖ)) (WittOver p ι) (Gamma p ι) :=
  Algebra.TensorProduct.basis (WittOver p ι) (cohenBasis p hϖ)

@[simp]
theorem gammaBasis_apply (j : Fin (ramIdx p hϖ)) : gammaBasis p ι hϖ j = 1 ⊗ₜ (ϖ ^ (j : ℕ)) := by
  simp [gammaBasis]

theorem gammaBasis_repr_tmul (w : WittOver p ι) (o : normInteger K) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr (w ⊗ₜ o) j =
      w * algebraMap _ (WittOver p ι) ((cohenBasis p hϖ).repr o j) := by
  simp [gammaBasis, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (x : Gamma p ι) :
    x = ∑ j, (gammaBasis p ι hϖ).repr x j ⊗ₜ (ϖ ^ (j : ℕ)) := by
  conv_lhs => rw [← (gammaBasis p ι hϖ).sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gammaBasis, Algebra.TensorProduct.basis_repr_symm_apply', cohenBasis_apply]

theorem gammaRed_tmul_unif_pow (w : WittOver p ι) {j : ℕ} (hj : j ≠ 0) :
    gammaRed p ι (w ⊗ₜ (ϖ ^ j)) = 0 := by
  rw [gammaRed_tmul, map_pow]
  have : residue (normInteger K) ϖ = 0 :=
    (residue_eq_zero_iff _).2 hϖ.not_isUnit
  rw [this, zero_pow hj, map_zero, mul_zero]

def fin0 : Fin (ramIdx p hϖ) := ⟨0, ramIdx_pos p hϖ⟩

theorem gammaRed_eq_coeff (x : Gamma p ι) :
    gammaRed p ι x = (WittOver.equiv p ι ((gammaBasis p ι hϖ).repr x (fin0 p hϖ))).coeff 0 := by
  conv_lhs => rw [eq_sum_tmul p ι hϖ x]
  rw [map_sum, Finset.sum_eq_single (fin0 p hϖ)]
  · simp [fin0]
  · intro j _ hj
    exact gammaRed_tmul_unif_pow p ι hϖ _ fun h => hj (Fin.ext h)
  · simp

theorem repr_mem_wittOverInt_of_tmul (hι : ∀ a, ‖ι a‖ ≤ 1) {w : WittOver p ι}
    (hw : w ∈ wittOverInt p ι) (o : normInteger K) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr (w ⊗ₜ o) j ∈ wittOverInt p ι := by
  rw [gammaBasis_repr_tmul]
  exact mul_mem hw (algebraMap_mem_wittOverInt p ι hι _)

theorem mem_gammaInt_iff (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι} :
    x ∈ gammaInt p ι ↔ ∀ j, (gammaBasis p ι hϖ).repr x j ∈ wittOverInt p ι := by
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, o, rfl⟩ := hx
      exact repr_mem_wittOverInt_of_tmul p ι hϖ hι hw o
    | zero => simp
    | one =>
      intro j
      rw [Algebra.TensorProduct.one_def]
      exact repr_mem_wittOverInt_of_tmul p ι hϖ hι (one_mem _) 1 j
    | add x y _ _ hx hy =>
      intro j; rw [map_add, Finsupp.add_apply]; exact add_mem (hx j) (hy j)
    | neg x _ hx =>
      intro j; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx j)
    | mul x y _ _ hx hy =>
      intro j
      rw [eq_sum_tmul p ι hϖ x, eq_sum_tmul p ι hϖ y, Finset.sum_mul_sum, map_sum,
        Finsupp.finsetSum_apply]
      refine Subring.sum_mem _ fun a _ => ?_
      rw [map_sum, Finsupp.finsetSum_apply]
      refine Subring.sum_mem _ fun b _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact repr_mem_wittOverInt_of_tmul p ι hϖ hι (mul_mem (hx a) (hy b)) _ j
  · intro h
    rw [eq_sum_tmul p ι hϖ x]
    exact Subring.sum_mem _ fun j _ => tmul_mem_gammaInt p ι (h j) _

theorem norm_gammaRed_le_one (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι} (hx : x ∈ gammaInt p ι) :
    ‖gammaRed p ι x‖ ≤ 1 := by
  rw [gammaRed_eq_coeff p ι hϖ]
  exact (mem_wittOverInt_iff p ι).1 ((mem_gammaInt_iff p ι hϖ hι).1 hx _) 0

theorem repr_sum_tmul (a : Fin (ramIdx p hϖ) → WittOver p ι) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr (∑ i, a i ⊗ₜ (ϖ ^ (i : ℕ))) j = a j := by
  have : ∑ i, a i ⊗ₜ (ϖ ^ (i : ℕ)) = ∑ i, a i • gammaBasis p ι hϖ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gammaBasis, Algebra.TensorProduct.basis_repr_symm_apply', cohenBasis_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem exists_gammaPi_pow_ramIdx :
    ∃ v : (Gamma p ι)ˣ, gammaPi p ι ϖ ^ ramIdx p hϖ = (p : Gamma p ι) * v := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  refine ⟨Units.map (gammaOfInt p ι).toMonoidHom u⁻¹, ?_⟩
  rw [gammaPi_eq, Algebra.TensorProduct.tmul_pow, one_pow, natCast_eq_tmul_right,
    Units.coe_map]
  change _ = _ * (gammaOfInt p ι) _
  rw [gammaOfInt_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hu, mul_assoc, Units.mul_inv,
    mul_one]

theorem span_gammaPi_pow_eq (m : ℕ) :
    span {gammaPi p ι ϖ ^ (ramIdx p hϖ * m)} = span {(p : Gamma p ι) ^ m} := by
  obtain ⟨v, hv⟩ := exists_gammaPi_pow_ramIdx p ι hϖ
  rw [pow_mul, hv, mul_pow, ← Units.val_pow_eq_pow_val]
  exact span_singleton_mul_right_unit (v ^ m).isUnit _

theorem repr_natCast_pow_mul (m : ℕ) (z : Gamma p ι) (j : Fin (ramIdx p hϖ)) :
    (gammaBasis p ι hϖ).repr ((p : Gamma p ι) ^ m * z) j =
      (p : WittOver p ι) ^ m * (gammaBasis p ι hϖ).repr z j := by
  have : (p : Gamma p ι) ^ m * z = ((p : WittOver p ι) ^ m) • z := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_mem_span_of_mem_span {x : Gamma p ι} {m : ℕ}
    (hx : x ∈ span {(p : Gamma p ι) ^ m}) (j : Fin (ramIdx p hϖ)) :
    WittOver.equiv p ι ((gammaBasis p ι hϖ).repr x j) ∈ span {(p : WittVector p L) ^ m} := by
  obtain ⟨z, rfl⟩ := mem_span_singleton'.1 hx
  rw [mul_comm, repr_natCast_pow_mul p ι hϖ, map_mul, map_pow, wittOver_equiv_natCast]
  exact mem_span_singleton.2 ⟨_, rfl⟩

theorem mem_span_of_repr_mem_span {x : Gamma p ι} {m : ℕ}
    (h : ∀ j, WittOver.equiv p ι ((gammaBasis p ι hϖ).repr x j) ∈ span {(p : WittVector p L) ^ m}) :
    x ∈ span {(p : Gamma p ι) ^ m} := by
  choose c hc using fun j => mem_span_singleton.1 (h j)
  set z : Gamma p ι := ∑ j, (WittOver.equiv p ι).symm (c j) ⊗ₜ (ϖ ^ (j : ℕ))
  have hx : x = (p : Gamma p ι) ^ m * z := by
    apply (gammaBasis p ι hϖ).repr.injective
    ext j
    rw [repr_natCast_pow_mul p ι hϖ, repr_sum_tmul p ι hϖ]
    apply (WittOver.equiv p ι).injective
    rw [hc j, map_mul, map_pow, wittOver_equiv_natCast, RingEquiv.apply_symm_apply]
  exact mem_span_singleton'.2 ⟨z, by rw [hx, mul_comm]⟩

theorem exists_eq_gammaPi_mul {x : Gamma p ι} (hx : gammaRed p ι x = 0) :
    ∃ y, x = gammaPi p ι ϖ * y ∧
      ((∀ a, ‖ι a‖ ≤ 1) → x ∈ gammaInt p ι → y ∈ gammaInt p ι) := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_prime_eq p hϖ
  have he := ramIdx_pos p hϖ
  set c := (gammaBasis p ι hϖ).repr x with hc_def
  have hc0 : (WittOver.equiv p ι (c (fin0 p hϖ))).coeff 0 = 0 := by
    rw [← gammaRed_eq_coeff p ι hϖ]; exact hx

  obtain ⟨v, hv⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero _).2 hc0)
  have hvint : c (fin0 p hϖ) ∈ wittOverInt p ι → (WittOver.equiv p ι).symm v ∈ wittOverInt p ι := by
    intro hint
    rw [mem_wittOverInt_iff] at hint ⊢
    intro n
    have h1 := hint (n + 1)
    rw [← hv, mul_charP_coeff_succ, norm_pow] at h1
    rw [RingEquiv.apply_symm_apply]
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h1
  set y0 : Gamma p ι := (WittOver.equiv p ι).symm v ⊗ₜ (ϖ ^ (ramIdx p hϖ - 1) * u)
  set yj : Fin (ramIdx p hϖ) → Gamma p ι := fun j =>
    if (j : ℕ) = 0 then y0 else c j ⊗ₜ (ϖ ^ ((j : ℕ) - 1))
  have hterm : ∀ j, c j ⊗ₜ (ϖ ^ (j : ℕ)) = gammaPi p ι ϖ * yj j := by
    intro j
    by_cases hj : (j : ℕ) = 0
    · have hj' : j = fin0 p hϖ := Fin.ext hj
      have hcv : c j = (WittOver.equiv p ι).symm v * (p : WittOver p ι) := by
        rw [hj']
        apply (WittOver.equiv p ι).injective
        rw [map_mul, RingEquiv.apply_symm_apply, wittOver_equiv_natCast, ← hv]
      simp only [yj, if_pos hj, y0, gammaPi_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hcv, hj, pow_zero, mul_natCast_tmul, mul_one, hu]
      congr 1
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]
    · simp only [yj, if_neg hj, gammaPi_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj)]
  refine ⟨∑ j, yj j, ?_, ?_⟩
  · conv_lhs => rw [eq_sum_tmul p ι hϖ x]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hterm j
  · intro hι hxint
    have hci := (mem_gammaInt_iff p ι hϖ hι).1 hxint
    refine Subring.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) = 0
    · simp only [yj, if_pos hj, y0]
      exact tmul_mem_gammaInt p ι (hvint (hci _)) _
    · simp only [yj, if_neg hj]
      exact tmul_mem_gammaInt p ι (hci j) _

theorem gammaRed_gammaPi : gammaRed p ι (gammaPi p ι ϖ) = 0 := by
  rw [gammaPi_eq, ← pow_one ϖ]
  exact gammaRed_tmul_unif_pow p ι hϖ 1 one_ne_zero

theorem ker_gammaRed : RingHom.ker (gammaRed p ι) = span {gammaPi p ι ϖ} := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    obtain ⟨y, rfl, -⟩ := exists_eq_gammaPi_mul p ι hϖ hx
    exact mem_span_singleton'.2 ⟨y, mul_comm _ _⟩
  · intro hx
    obtain ⟨y, rfl⟩ := mem_span_singleton'.1 hx
    rw [map_mul, gammaRed_gammaPi p ι hϖ, mul_zero]

theorem exists_mem_gammaInt_eq_gammaPi_mul (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι}
    (hx : x ∈ gammaInt p ι) (h0 : gammaRed p ι x = 0) :
    ∃ y ∈ gammaInt p ι, x = gammaPi p ι ϖ * y := by
  obtain ⟨y, hy, hint⟩ := exists_eq_gammaPi_mul p ι hϖ h0
  exact ⟨y, hint hι hx, hy⟩

theorem eq_zero_of_natCast_mul_eq_zero {x : Gamma p ι} (hx : (p : Gamma p ι) * x = 0) : x = 0 := by
  apply (gammaBasis p ι hϖ).repr.injective
  ext j
  have h := congrArg (fun z => (gammaBasis p ι hϖ).repr z j) hx
  rw [← pow_one (p : Gamma p ι), repr_natCast_pow_mul p ι hϖ, pow_one, map_zero, Finsupp.zero_apply] at h
  rw [map_zero, Finsupp.zero_apply]
  apply (WittOver.equiv p ι).injective
  have h2 := congrArg (WittOver.equiv p ι) h
  rw [map_mul, wittOver_equiv_natCast, map_zero] at h2
  rw [map_zero]
  exact (mul_eq_zero.1 h2).resolve_left (WittVector.p_nonzero p L)

theorem gammaPi_mem_nonZeroDivisors : gammaPi p ι ϖ ∈ nonZeroDivisors (Gamma p ι) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨v, hv⟩ := exists_gammaPi_pow_ramIdx p ι hϖ
  have he := ramIdx_pos p hϖ
  have h1 : gammaPi p ι ϖ ^ ramIdx p hϖ * x = 0 := by
    rw [← Nat.sub_add_cancel he, pow_succ, mul_assoc, mul_comm (gammaPi p ι ϖ) x, hx, mul_zero]
  rw [hv, mul_assoc] at h1
  have h2 := eq_zero_of_natCast_mul_eq_zero p ι hϖ h1
  have := congrArg (fun z => (↑v⁻¹ : Gamma p ι) * z) h2
  simpa [← mul_assoc] using this

theorem isAdicComplete_gammaPi : IsAdicComplete (span {gammaPi p ι ϖ}) (Gamma p ι) := by
  have he := ramIdx_pos p hϖ
  have hmem : ∀ (n : ℕ) (x y : Gamma p ι),
      x ≡ y [SMOD (span {gammaPi p ι ϖ} ^ n • ⊤ : Submodule (Gamma p ι) (Gamma p ι))] ↔
        x - y ∈ span {gammaPi p ι ϖ ^ n} := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, span_singleton_pow]
  have hle : ∀ n m, n ≤ m → span {gammaPi p ι ϖ ^ m} ≤ span {gammaPi p ι ϖ ^ n} := fun n m h =>
    span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    simp only [hmem, sub_zero] at hx
    have hc : ∀ j, (gammaBasis p ι hϖ).repr x j = 0 := by
      intro j
      apply (WittOver.equiv p ι).injective
      rw [map_zero]
      apply WittLift.eq_zero_of_forall_mem
      intro m
      apply repr_mem_span_of_mem_span p ι hϖ _ j
      rw [← span_gammaPi_pow_eq p ι hϖ]
      exact hx _
    rw [eq_sum_tmul p ι hϖ x]
    simp [hc]
  · intro f hf
    simp only [hmem] at hf
    set a : Fin (ramIdx p hϖ) → ℕ → WittVector p L :=
      fun j n => WittOver.equiv p ι ((gammaBasis p ι hϖ).repr (f (ramIdx p hϖ * n)) j) with ha_def
    have ha : ∀ j n, a j (n + 1) - a j n ∈ span {(p : WittVector p L) ^ n} := by
      intro j n
      have h1 : f (ramIdx p hϖ * n) - f (ramIdx p hϖ * (n + 1)) ∈ span {(p : Gamma p ι) ^ n} := by
        rw [← span_gammaPi_pow_eq p ι hϖ]
        exact hf (Nat.mul_le_mul_left _ (Nat.le_succ n))
      have h2 := repr_mem_span_of_mem_span p ι hϖ h1 j
      rw [map_sub, Finsupp.sub_apply, map_sub] at h2
      rw [← neg_sub]
      exact neg_mem h2
    choose W hW using fun j => WittLift.exists_limit (a j) (ha j)
    refine ⟨∑ j, (WittOver.equiv p ι).symm (W j) ⊗ₜ (ϖ ^ (j : ℕ)), fun n => ?_⟩
    rw [hmem]
    have h1 : f n - f (ramIdx p hϖ * n) ∈ span {gammaPi p ι ϖ ^ n} :=
      hf (Nat.le_mul_of_pos_left n he)
    have h2 : f (ramIdx p hϖ * n) - ∑ j, (WittOver.equiv p ι).symm (W j) ⊗ₜ (ϖ ^ (j : ℕ)) ∈
        span {gammaPi p ι ϖ ^ n} := by
      apply hle n (ramIdx p hϖ * n) (Nat.le_mul_of_pos_left n he)
      rw [span_gammaPi_pow_eq p ι hϖ]
      apply mem_span_of_repr_mem_span p ι hϖ
      intro j
      rw [map_sub, Finsupp.sub_apply, repr_sum_tmul p ι hϖ, map_sub, RingEquiv.apply_symm_apply]
      rw [← neg_sub]
      exact neg_mem (hW j n)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel] at this

theorem mem_gammaInt_of_forall (hι : ∀ a, ‖ι a‖ ≤ 1) {x : Gamma p ι}
    (h : ∀ N : ℕ, ∃ y ∈ gammaInt p ι, x - y ∈ span {gammaPi p ι ϖ ^ N}) : x ∈ gammaInt p ι := by
  rw [mem_gammaInt_iff p ι hϖ hι]
  intro j
  rw [mem_wittOverInt_iff]
  intro n
  obtain ⟨y, hy, hxy⟩ := h (ramIdx p hϖ * (n + 1))
  rw [span_gammaPi_pow_eq p ι hϖ] at hxy
  have h1 := repr_mem_span_of_mem_span p ι hϖ hxy j
  rw [map_sub, Finsupp.sub_apply, map_sub] at h1
  rw [coeff_eq_of_sub_mem p h1 (Nat.lt_succ_self n)]
  exact (mem_wittOverInt_iff p ι).1 ((mem_gammaInt_iff p ι hϖ hι).1 hy j) n

end Gamma

section Frobenius

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : ResidueField (normInteger K) →+* L)

def wittOverFrob (a : ℕ) : WittOver p ι →+* WittOver p ι :=
  (WittOver.equiv p ι).symm.toRingHom.comp
    ((WittVector.map (iterateFrobenius L p a)).comp (WittOver.equiv p ι).toRingHom)

theorem wittOverFrob_coeff (a : ℕ) (w : WittOver p ι) (n : ℕ) :
    (WittOver.equiv p ι (wittOverFrob p ι a w)).coeff n = (WittOver.equiv p ι w).coeff n ^ p ^ a := by
  change (WittVector.map (iterateFrobenius L p a) (WittOver.equiv p ι w)).coeff n = _
  rw [WittVector.map_coeff, iterateFrobenius_def]

theorem wittOverFrob_bijective (a : ℕ) : Function.Bijective (wittOverFrob p ι a) := by
  have hb : Function.Bijective (iterateFrobenius L p a) := by
    rw [← coe_iterateFrobeniusEquiv]; exact (iterateFrobeniusEquiv L p a).bijective
  have hm : Function.Bijective (WittVector.map (iterateFrobenius L p a) : WittVector p L → WittVector p L) :=
    ⟨WittVector.map_injective _ hb.1, WittVector.map_surjective _ hb.2⟩
  exact (WittOver.equiv p ι).symm.bijective.comp (hm.comp (WittOver.equiv p ι).bijective)

theorem wittOverFrob_mem_wittOverInt (a : ℕ) {w : WittOver p ι} (hw : w ∈ wittOverInt p ι) :
    wittOverFrob p ι a w ∈ wittOverInt p ι := by
  rw [mem_wittOverInt_iff] at hw ⊢
  intro n
  rw [wittOverFrob_coeff, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hw n)

set_option linter.unusedVariables false in

def TwistedGamma (a : ℕ) : Type _ := Gamma p ι

instance (a : ℕ) : CommRing (TwistedGamma p ι a) := inferInstanceAs (CommRing (Gamma p ι))

instance (a : ℕ) : Algebra (WittVector p (ResidueField (normInteger K))) (TwistedGamma p ι a) :=
  @RingHom.toAlgebra _ (TwistedGamma p ι a) _ _
    ((algebraMap (WittVector p (ResidueField (normInteger K))) (Gamma p ι)).comp
      (WittVector.map (iterateFrobenius (ResidueField (normInteger K)) p a)))

variable (a : ℕ) (σ : normInteger K →+* normInteger K)

def gammaPhiLeft : WittOver p ι →ₐ[WittVector p (ResidueField (normInteger K))] TwistedGamma p ι a where
  toRingHom := (Algebra.TensorProduct.includeLeftRingHom (R := WittVector p (ResidueField (normInteger K)))
    (A := WittOver p ι) (B := normInteger K)).comp (wittOverFrob p ι a)
  commutes' := fun c => by
    change wittOverFrob p ι a (algebraMap _ (WittOver p ι) c) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] (1 : normInteger K) =
      algebraMap _ (Gamma p ι) (WittVector.map (iterateFrobenius _ p a) c)
    rw [Algebra.TensorProduct.algebraMap_apply]
    congr 1
    apply (WittOver.equiv p ι).injective
    ext n
    rw [wittOverFrob_coeff, algebraMap_wittOver, algebraMap_wittOver, WittVector.map_coeff,
      WittVector.map_coeff, WittVector.map_coeff, iterateFrobenius_def, map_pow]

def gammaPhiRight (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) :
    normInteger K →ₐ[WittVector p (ResidueField (normInteger K))] TwistedGamma p ι a where
  toRingHom := (gammaOfInt p ι).comp σ
  commutes' := fun c => by
    change (1 : WittOver p ι) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] σ (cohenMap K p c) =
      algebraMap _ (Gamma p ι) (WittVector.map (iterateFrobenius _ p a) c)
    have := congrArg (fun f => f c) (comp_cohenMap_of_residue p σ a hσ)
    simp only [RingHom.comp_apply] at this
    rw [this, Algebra.TensorProduct.algebraMap_apply']
    rfl

def gammaPhi (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) : Gamma p ι →+* Gamma p ι :=
  (Algebra.TensorProduct.lift (gammaPhiLeft p ι a) (gammaPhiRight p ι a σ hσ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem gammaPhi_tmul (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (w : WittOver p ι) (o : normInteger K) :
    gammaPhi p ι a σ hσ (w ⊗ₜ o) = wittOverFrob p ι a w ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] σ o := by
  have h := Algebra.TensorProduct.lift_tmul (gammaPhiLeft p ι a) (gammaPhiRight p ι a σ hσ)
    (fun _ _ => Commute.all _ _) w o
  refine h.trans ?_
  change ((wittOverFrob p ι a w ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] (1 : normInteger K) : Gamma p ι) *
    ((1 : WittOver p ι) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] σ o : Gamma p ι)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gammaRed_gammaPhi (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (x : Gamma p ι) :
    gammaRed p ι (gammaPhi p ι a σ hσ x) = gammaRed p ι x ^ p ^ a := by
  induction x using TensorProduct.induction_on with
  | zero => simp [zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  | tmul w o =>
    rw [gammaPhi_tmul p ι a σ hσ, gammaRed_tmul, gammaRed_tmul, wittOverFrob_coeff, hσ, map_pow, mul_pow]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    exact (add_pow_expChar_pow _ _ p a).symm

theorem gammaPhi_mem_gammaInt (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) {x : Gamma p ι} (hx : x ∈ gammaInt p ι) :
    gammaPhi p ι a σ hσ x ∈ gammaInt p ι := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, o, rfl⟩ := hx
    rw [gammaPhi_tmul]
    exact tmul_mem_gammaInt p ι (wittOverFrob_mem_wittOverInt p ι a hw) _
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem gammaPhi_gammaPi (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (ϖ : normInteger K) : gammaPhi p ι a σ hσ (gammaPi p ι ϖ) = gammaPi p ι (σ ϖ) := by
  rw [gammaPi_eq, gammaPhi_tmul, map_one, gammaPi_eq]

theorem gammaPhi_bijective (hσ : ∀ x, residue (normInteger K) (σ x) = residue (normInteger K) x ^ p ^ a) (hbij : Function.Bijective σ) {ϖ : normInteger K} (hϖ : Irreducible ϖ) :
    Function.Bijective (gammaPhi p ι a σ hσ) := by
  set e := RingEquiv.ofBijective σ hbij
  have hϖ' : Irreducible (σ ϖ) := by
    have : Irreducible (e ϖ) := (MulEquiv.irreducible_iff (f := e.toMulEquiv)).2 hϖ
    simpa [e] using this
  have hram : ramIdx p hϖ' = ramIdx p hϖ := by
    have h1 := norm_natCast_prime_eq (K := K) p hϖ
    have h2 := norm_natCast_prime_eq (K := K) p hϖ'
    have hn : ‖((σ ϖ : normInteger K) : K)‖ = ‖(ϖ : K)‖ := by
      obtain ⟨n, hn⟩ := exists_norm_eq_pow hϖ (x := σ ϖ) hϖ'.ne_zero
      obtain ⟨m, hm⟩ := exists_norm_eq_pow hϖ' (x := ϖ) hϖ.ne_zero
      have h0 := norm_unif_pos hϖ
      have h1' := norm_unif_lt_one hϖ
      rw [hn] at hm
      rw [← pow_mul] at hm
      have : 1 = n * m := by
        have := pow_right_injective₀ h0 h1'.ne (show ‖(ϖ : K)‖ ^ 1 = ‖(ϖ : K)‖ ^ (n * m) by rw [pow_one]; exact hm)
        exact this
      have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_right this.symm
      rw [hn, hn1, pow_one]
    rw [hn] at h2
    rw [h1] at h2
    exact (pow_right_injective₀ (norm_unif_pos hϖ) (norm_unif_lt_one hϖ).ne h2).symm

  have hphi : ∀ x : Gamma p ι, gammaPhi p ι a σ hσ x =
      ∑ j : Fin (ramIdx p hϖ), wittOverFrob p ι a ((gammaBasis p ι hϖ).repr x j) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (j : ℕ)) := by
    intro x
    conv_lhs => rw [eq_sum_tmul p ι hϖ x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gammaPhi_tmul p ι a σ hσ, map_pow]
  obtain ⟨finv, hfl, hfr⟩ : ∃ g : WittOver p ι → WittOver p ι,
      Function.LeftInverse g (wittOverFrob p ι a) ∧ Function.RightInverse g (wittOverFrob p ι a) :=
    ⟨Function.surjInv (wittOverFrob_bijective p ι a).2,
      Function.leftInverse_surjInv (wittOverFrob_bijective p ι a),
      Function.rightInverse_surjInv (wittOverFrob_bijective p ι a).2⟩
  have hsum : ∀ c : Fin (ramIdx p hϖ) → WittOver p ι, ∀ j : Fin (ramIdx p hϖ'),
      (gammaBasis p ι hϖ').repr (∑ i : Fin (ramIdx p hϖ), c i ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (i : ℕ))) j =
        c (Fin.cast hram j) := by
    intro c j
    have : ∑ i : Fin (ramIdx p hϖ), c i ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (i : ℕ)) =
        ∑ i : Fin (ramIdx p hϖ'), c (Fin.cast hram i) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] ((σ ϖ) ^ (i : ℕ)) := by
      rw [← (finCongr hram.symm).sum_comp]
      rfl
    rw [this, repr_sum_tmul p ι hϖ']
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · apply (gammaBasis p ι hϖ).repr.injective
    ext j
    have h := congrArg (fun z => (gammaBasis p ι hϖ').repr z (Fin.cast hram.symm j)) hxy
    simp only [hphi, hsum] at h
    exact (wittOverFrob_bijective p ι a).1 (by simpa using h)
  · refine ⟨∑ j : Fin (ramIdx p hϖ), finv ((gammaBasis p ι hϖ').repr y (Fin.cast hram.symm j)) ⊗ₜ[WittVector p (IsLocalRing.ResidueField (normInteger K))] (ϖ ^ (j : ℕ)), ?_⟩
    apply (gammaBasis p ι hϖ').repr.injective
    ext j
    rw [hphi, hsum, repr_sum_tmul p ι hϖ, hfr]
    simp

end Frobenius

end ExtRobba

end GroundTheory.PAdicHodge
