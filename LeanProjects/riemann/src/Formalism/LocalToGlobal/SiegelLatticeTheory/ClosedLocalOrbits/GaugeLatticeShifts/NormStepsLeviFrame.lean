import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LeviFramePf

open Formalism.L2.SG.Pf.unitaryCongruence

section Gen

variable (I : AutInst) (g : ℕ)

theorem lf_memL_smul {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) {x : VA I} (hx : x ∈ I.Lf) :
    c • x ∈ I.Lf := I.Lf.smul_mem ⟨c, hc⟩ hx

theorem lf_mL_smul {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) {x : VA I} (hx : x ∈ mL I g) :
    c • x ∈ mL I g := (mL I g).smul_mem ⟨c, hc⟩ hx

theorem lf_mem_mL {x : VA I} (hx : x ∈ mL I g) : ∃ y ∈ I.Lf, x = (g : I.E ⊗[I.F] Af I.F) • y := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hx'
    exact ⟨y + y', add_mem hy hy', by rw [smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(c : I.E ⊗[I.F] Af I.F) • y, lf_memL_smul I c.2 hy, ?_⟩
    show (c : I.E ⊗[I.F] Af I.F) • ((g : I.E ⊗[I.F] Af I.F) • y) = _
    rw [smul_comm]

theorem lf_mL_le {x : VA I} (hx : x ∈ mL I g) : x ∈ I.Lf := by
  obtain ⟨y, hy, rfl⟩ := lf_mem_mL I g hx
  exact lf_memL_smul I (natCast_mem _ g) hy

private theorem hA_smul_right_eq_mul (I : AutInst) (x y : VA I) (a : I.E ⊗[I.F] Af I.F) :
    hA I x (a • y) = a * hA I x y := by
  unfold hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hA_sub_right_gauge_lattice_shifts (I : AutInst) (x y z : VA I) :
    hA I x (y - z) = hA I x y - hA I x z := by
  unfold hA Formalism.UG.hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem hA_smul_left_eq_sigA_mul (I : AutInst) (x y : VA I) (a : I.E ⊗[I.F] Af I.F) :
    hA I (a • x) y = sigA I a * hA I x y := by
  unfold hA Formalism.UG.hform sigA
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem zMod'_mul_of_mem_intAf (I : AutInst) (g : ℕ) {c a : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E)
    (ha : ZMod' I g a) : ZMod' I g (c * a) := by
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨c * t, mul_mem hc ht, by ring⟩

theorem lf_hA_sub_left (u u' v : VA I) : hA I (u - u') v = hA I u v - hA I u' v := by
  unfold hA Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lf_hA_sum_right (u : VA I) {ι : Type} (s : Finset ι) (f : ι → VA I) :
    hA I u (∑ k ∈ s, f k) = ∑ k ∈ s, hA I u (f k) := by
  unfold hA Formalism.UG.hform
  simp only [Finset.sum_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_comm

theorem lf_hA_mL_right {x y : VA I} (hx : x ∈ I.Lf) (hy : y ∈ mL I g) : ZMod' I g (hA I x y) := by
  obtain ⟨y', hy', rfl⟩ := lf_mem_mL I g hy
  rw [hA_smul_right]
  exact ⟨_, hA_int I hx hy', rfl⟩

theorem lf_hA_mL_left {x y : VA I} (hx : x ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I x y) := by
  obtain ⟨x', hx', rfl⟩ := lf_mem_mL I g hx
  rw [hA_smul_left, map_natCast]
  exact ⟨_, hA_int I hx' hy, rfl⟩

theorem lf_hA_cong {x x' y y' : VA I} (hx' : x' ∈ I.Lf) (hy : y ∈ I.Lf) (hxx : x - x' ∈ mL I g)
    (hyy : y - y' ∈ mL I g) : ZMod' I g (hA I x y - hA I x' y') := by
  obtain ⟨t1, ht1, h1⟩ := lf_hA_mL_left I g hxx hy
  obtain ⟨t2, ht2, h2⟩ := lf_hA_mL_right I g hx' hyy
  refine ⟨t1 + t2, add_mem ht1 ht2, ?_⟩
  rw [lf_hA_sub_left] at h1
  rw [hA_sub_right_gauge_lattice_shifts] at h2
  linear_combination h1 + h2

theorem lf_one_mem {κ : Type} [DecidableEq κ] (i j : κ) :
    (1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

end Gen

section Eps

variable {I : AutInst} {g : ℕ} {ε : I.E ⊗[I.F] Af I.F}

theorem lf_coprime_unit
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, ε * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε)
    {c : ℕ} (hc : Nat.Coprime c g) : ∃ t ∈ IntAf I.F I.E, ε * ((c : I.E ⊗[I.F] Af I.F) * t) = ε := by
  have h1 : (c : ℤ) * Nat.gcdA c g + (g : ℤ) * Nat.gcdB c g = 1 := by
    have := Nat.gcd_eq_gcd_ab c g
    rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at this
    exact this.symm
  obtain ⟨s', hs', he⟩ := hU ((-(Nat.gcdB c g) : ℤ) : I.E ⊗[I.F] Af I.F) (intCast_mem _ _)
  refine ⟨((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * s', mul_mem (intCast_mem _ _) hs', ?_⟩
  have h2 : (c : I.E ⊗[I.F] Af I.F) * ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) =
      1 + (g : I.E ⊗[I.F] Af I.F) * ((-(Nat.gcdB c g) : ℤ) : I.E ⊗[I.F] Af I.F) := by
    have h3 := congrArg (fun z : ℤ => (z : I.E ⊗[I.F] Af I.F)) h1
    push_cast at h3 ⊢
    linear_combination h3
  rw [show (c : I.E ⊗[I.F] Af I.F) * (((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * s') =
    ((c : I.E ⊗[I.F] Af I.F) * ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F)) * s' from (mul_assoc _ _ _).symm, h2]
  exact he

theorem lf_inAt_eps (hεO : ε ∈ IntAf I.F I.E)
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, ε * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε)
    {x : VA I} (h : InAt I g g x) : ε • x ∈ mL I g := by
  obtain ⟨c, hc, hcx⟩ := h
  obtain ⟨t, ht, hε⟩ := lf_coprime_unit hU hc
  have hx : ε • x = (ε * t) • ((c : I.E ⊗[I.F] Af I.F) • x) := by
    rw [smul_smul]
    conv_lhs => rw [← hε]
    congr 1
    ring
  rw [hx]
  exact lf_mL_smul I g (mul_mem hεO ht) hcx

theorem lf_eps_vec_cong (h1ε : ZMod' I g (1 - ε)) {x : VA I} (hx : x ∈ I.Lf) : ε • x - x ∈ mL I g := by
  obtain ⟨t, ht, he⟩ := h1ε
  unfold mL
  refine Submodule.subset_span ⟨(-t) • x, lf_memL_smul I (neg_mem ht) hx, ?_⟩
  have hε : ε = 1 - (g : I.E ⊗[I.F] Af I.F) * t := by rw [← he]; ring
  rw [hε, smul_smul, sub_smul, one_smul, mul_neg, neg_smul, sub_sub_cancel_left]

end Eps

theorem lf_det_adj_cong {A : Type*} [CommRing A] {κ : Type*} [Fintype κ] [DecidableEq κ] (O : Subring A)
    (g : ℕ) (t : Matrix κ κ A) (ht : ∀ i j, t i j ∈ O) :
    (∃ s ∈ O, (1 + (g : A) • t).det = 1 + (g : A) * s) ∧
      ∀ i j, ∃ s ∈ O, (1 + (g : A) • t).adjugate i j = (1 : Matrix κ κ A) i j + (g : A) * s := by
  classical
  let t' : Matrix κ κ O := fun i j => ⟨t i j, ht i j⟩
  have hmap : 1 + (g : A) • t = (1 + (g : O) • t').map O.subtype := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, t'] <;> rfl
  have hg : Ideal.Quotient.mk (Ideal.span {(g : O)}) (g : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hone : (1 + (g : O) • t').map (Ideal.Quotient.mk (Ideal.span {(g : O)})) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, hg]
  have hdet : Ideal.Quotient.mk (Ideal.span {(g : O)}) (1 + (g : O) • t').det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hone, Matrix.det_one]
  obtain ⟨s, hs⟩ : ∃ s : O, (1 + (g : O) • t').det = 1 + (g : O) * s := by
    have hm : (1 + (g : O) • t').det - 1 ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdet, map_one, sub_self]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨s, by linear_combination -hs⟩
  refine ⟨⟨s, s.2, ?_⟩, fun i j => ?_⟩
  · rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hs]
    simp
  · have hadj : (1 + (g : O) • t').adjugate.map (Ideal.Quotient.mk (Ideal.span {(g : O)})) = 1 := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, hone,
        Matrix.adjugate_one]
    have hm : (1 + (g : O) • t').adjugate i j - (1 : Matrix κ κ O) i j ∈ Ideal.span {(g : O)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
      have h1 := congrFun (congrFun hadj i) j
      rw [Matrix.map_apply] at h1
      rw [h1]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨r, r.2, ?_⟩
    have hr' : (1 + (g : O) • t').adjugate i j = (1 : Matrix κ κ O) i j + (g : O) * r := by
      linear_combination -hr
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply,
      Matrix.map_apply, hr']
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem lf_inv_on (I : AutInst) (g : ℕ) {η : I.E ⊗[I.F] Af I.F} (hηO : η ∈ IntAf I.F I.E)
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, η * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = η)
    {κ : Type} [Fintype κ] [DecidableEq κ] (t : Matrix κ κ (I.E ⊗[I.F] Af I.F))
    (ht : ∀ i j, t i j ∈ IntAf I.F I.E) :
    ∃ M : Matrix κ κ (I.E ⊗[I.F] Af I.F), (∀ i j, M i j ∈ IntAf I.F I.E) ∧
      η • ((1 + (g : I.E ⊗[I.F] Af I.F) • t) * M) = η • 1 ∧
      η • (M * (1 + (g : I.E ⊗[I.F] Af I.F) • t)) = η • 1 ∧
      ∀ i j, ZMod' I g (η * M i j - η * (1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j) := by
  obtain ⟨⟨s, hsO, hs⟩, hadj⟩ := lf_det_adj_cong (IntAf I.F I.E) g t ht
  obtain ⟨s', hs'O, hs'⟩ := hU s hsO
  refine ⟨s' • (1 + (g : I.E ⊗[I.F] Af I.F) • t).adjugate, fun i j => ?_, ?_, ?_, fun i j => ?_⟩
  · obtain ⟨r, hrO, hr⟩ := hadj i j
    rw [Matrix.smul_apply, smul_eq_mul, hr]
    exact mul_mem hs'O (add_mem (lf_one_mem I i j) (mul_mem (natCast_mem _ g) hrO))
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, hs, smul_smul, smul_smul]
    congr 1
    linear_combination hs'
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, hs, smul_smul, smul_smul]
    congr 1
    linear_combination hs'
  · obtain ⟨r, hrO, hr⟩ := hadj i j
    refine ⟨η * r - η * s * s' * (1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j -
      (g : I.E ⊗[I.F] Af I.F) * η * s * s' * r, ?_, ?_⟩
    · exact sub_mem (sub_mem (mul_mem hηO hrO) (mul_mem (mul_mem (mul_mem hηO hsO) hs'O) (lf_one_mem I i j)))
        (mul_mem (mul_mem (mul_mem (mul_mem (natCast_mem _ g) hηO) hsO) hs'O) hrO)
    · rw [Matrix.smul_apply, smul_eq_mul, hr]
      linear_combination ((1 : Matrix κ κ (I.E ⊗[I.F] Af I.F)) i j + (g : I.E ⊗[I.F] Af I.F) * r) * hs'

section Proj

variable (I : AutInst) {ι : Type} [Fintype ι] [DecidableEq ι] (ε : I.E ⊗[I.F] Af I.F) (uR : ι → VA I)
  (Q : Matrix ι ι (I.E ⊗[I.F] Af I.F))

def lfCf (y : VA I) : ι → I.E ⊗[I.F] Af I.F := ε • (Q *ᵥ fun l => hA I (uR l) y)

def lfProj (y : VA I) : VA I := ε • y - ∑ k, lfCf I ε uR Q y k • uR k

def lfGram : Matrix ι ι (I.E ⊗[I.F] Af I.F) := Matrix.of fun k l => hA I (uR k) (uR l)

theorem lf_proj_orth (hPQ : ε • (lfGram I uR * Q) = ε • 1) (y : VA I) (l : ι) :
    hA I (uR l) (lfProj I ε uR Q y) = 0 := by
  have hPQ' : ∀ m, ε * (lfGram I uR * Q) l m = ε * (1 : Matrix ι ι (I.E ⊗[I.F] Af I.F)) l m := fun m => by
    have := congrFun (congrFun hPQ l) m
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  unfold lfProj
  rw [hA_sub_right_gauge_lattice_shifts, lf_hA_sum_right, hA_smul_right_eq_mul]
  simp only [hA_smul_right_eq_mul]
  have key : ∑ k, lfCf I ε uR Q y k * hA I (uR l) (uR k) = ε * hA I (uR l) y := by
    calc ∑ k, lfCf I ε uR Q y k * hA I (uR l) (uR k)
        = ∑ m, (ε * (lfGram I uR * Q) l m) * hA I (uR m) y := by
          simp only [lfCf, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply,
            lfGram, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ m, (ε * (1 : Matrix ι ι (I.E ⊗[I.F] Af I.F)) l m) * hA I (uR m) y := by simp only [hPQ']
      _ = ε * hA I (uR l) y := by simp [Matrix.one_apply]
  rw [key, sub_self]

theorem lf_cf_eps (hεε : ε * ε = ε) (y : VA I) (k : ι) : ε * lfCf I ε uR Q y k = lfCf I ε uR Q y k := by
  simp only [lfCf, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hεε]

theorem lf_cf_eq (hσε : sigA I ε = ε) (y : VA I) (k : ι) :
    lfCf I ε uR Q y k = ∑ l, Q k l * hA I (ε • uR l) y := by
  simp only [lfCf, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hA_smul_left_eq_sigA_mul, hσε,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem lf_term_eq (hεε : ε * ε = ε) (y : VA I) (k : ι) :
    lfCf I ε uR Q y k • uR k = lfCf I ε uR Q y k • (ε • uR k) := by
  rw [smul_smul, mul_comm, lf_cf_eps I ε uR Q hεε]

theorem lf_proj_mem (hεO : ε ∈ IntAf I.F I.E) (hεε : ε * ε = ε) (hσε : sigA I ε = ε)
    (hu : ∀ k, ε • uR k ∈ I.Lf) (hQ : ∀ k l, Q k l ∈ IntAf I.F I.E) {y : VA I} (hy : y ∈ I.Lf) :
    lfProj I ε uR Q y ∈ I.Lf := by
  have hc : ∀ k, lfCf I ε uR Q y k ∈ IntAf I.F I.E := fun k => by
    rw [lf_cf_eq I ε uR Q hσε y k]
    exact sum_mem fun l _ => mul_mem (hQ k l) (hA_int (hu := hu l) (hv := hy))
  unfold lfProj
  refine I.Lf.sub_mem (lf_memL_smul I hεO hy) (I.Lf.sum_mem fun k _ => ?_)
  rw [lf_term_eq I ε uR Q hεε y k]
  exact lf_memL_smul I (hc k) (hu k)

theorem lf_proj_cong (g : ℕ) (hεε : ε * ε = ε) (hσε : sigA I ε = ε) (h1ε : ZMod' I g (1 - ε))
    (hu : ∀ k, ε • uR k ∈ I.Lf) (hQ : ∀ k l, Q k l ∈ IntAf I.F I.E) {y : VA I} (hy : y ∈ I.Lf)
    (hZ : ∀ l, ZMod' I g (hA I (ε • uR l) y)) : lfProj I ε uR Q y - y ∈ mL I g := by
  choose t ht he using hZ
  have hc : ∀ k, ZMod' I g (lfCf I ε uR Q y k) := fun k => by
    refine ⟨∑ l, Q k l * t l, sum_mem fun l _ => mul_mem (hQ k l) (ht l), ?_⟩
    rw [lf_cf_eq I ε uR Q hσε y k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [he l]
    ring
  have hsum : ∑ k, lfCf I ε uR Q y k • uR k ∈ mL I g := by
    refine (mL I g).sum_mem fun k _ => ?_
    obtain ⟨s, hs, hse⟩ := hc k
    rw [lf_term_eq I ε uR Q hεε y k, hse, ← smul_smul]
    unfold mL
    exact Submodule.subset_span ⟨s • (ε • uR k), lf_memL_smul I hs (hu k), rfl⟩
  have h1 := lf_eps_vec_cong h1ε hy
  unfold lfProj
  rw [show ε • y - ∑ k, lfCf I ε uR Q y k • uR k - y = (ε • y - y) - ∑ k, lfCf I ε uR Q y k • uR k by abel]
  exact (mL I g).sub_mem h1 hsum

end Proj

def hyperbolicMinusOneMatrix (A : Type*) [Ring A] (r : ℕ) : Matrix ((Fin r ⊕ Fin r) ⊕ Unit) ((Fin r ⊕ Fin r) ⊕ Unit) A :=
  Matrix.of (Sum.elim
    (Sum.elim (fun a => Sum.elim (Sum.elim (fun _ => 0) (fun b => if a = b then 1 else 0)) (fun _ => 0))
      (fun a => Sum.elim (Sum.elim (fun b => if a = b then 1 else 0) (fun _ => 0)) (fun _ => 0)))
    (fun _ => Sum.elim (fun _ => 0) (fun _ => -1)))

theorem hyperbolic_matrix_sq_eq_one (A : Type*) [Ring A] (r : ℕ) : hyperbolicMinusOneMatrix A r * hyperbolicMinusOneMatrix A r = 1 := by
  ext i j
  rcases i with (a | a) | ⟨⟩ <;> rcases j with (b | b) | ⟨⟩ <;>
    simp [hyperbolicMinusOneMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem hyperbolic_matrix_integral (I : AutInst) (r : ℕ) (k l : (Fin r ⊕ Fin r) ⊕ Unit) :
    hyperbolicMinusOneMatrix (I.E ⊗[I.F] Af I.F) r k l ∈ IntAf I.F I.E := by
  rcases k with (a | a) | ⟨⟩ <;> rcases l with (b | b) | ⟨⟩ <;>
    simp only [hyperbolicMinusOneMatrix, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr] <;>
    first
    | exact zero_mem _
    | exact one_mem _
    | exact neg_mem (one_mem _)
    | (split_ifs <;> first | exact zero_mem _ | exact one_mem _)

theorem lf_frame_core (I : AutInst) (g : ℕ) {ε : I.E ⊗[I.F] Af I.F} (hεO : ε ∈ IntAf I.F I.E)
    (hεε : ε * ε = ε) (hσε : sigA I ε = ε) (h1ε : ZMod' I g (1 - ε))
    (hU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, ε * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε)
    {ι : Type} [Fintype ι] [DecidableEq ι] (uR u0 : ι → VA I) (Q0 : Matrix ι ι (I.E ⊗[I.F] Af I.F))
    (hQ0O : ∀ k l, Q0 k l ∈ IntAf I.F I.E) (hQ0 : Q0 * Q0 = 1) (hu0 : ∀ k, u0 k ∈ I.Lf)
    (hc : ∀ k, ε • (uR k - u0 k) ∈ mL I g) (hgr : ∀ k l, ZMod' I g (hA I (u0 k) (u0 l) - Q0 k l))
    {m : ℕ} (ew : I.E ⊗[I.F] Af I.F) (bw bwd : Fin m → VA I) (hewi : ew * ew = ew)
    (hewO : ew ∈ IntAf I.F I.E) (hbL : ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf) (hbw : ∀ i, bw i = ew • bw i)
    (hbwd : ∀ i, bwd i = sigA I ew • bwd i)
    (hdual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0))
    (hW : ∀ k j, ZMod' I g (hA I (u0 k) (bw j)) ∧ ZMod' I g (hA I (u0 k) (bwd j))) :
    ∃ (η : I.E ⊗[I.F] Af I.F) (b d : Fin m → VA I), η ∈ IntAf I.F I.E ∧ η * η = η ∧ η * ew = η ∧
      ZMod' I g (ew - η) ∧
      (∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E, η * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = η) ∧
      (∀ i, b i ∈ I.Lf ∧ d i ∈ I.Lf ∧ η • b i = b i ∧ sigA I η • d i = d i) ∧
      (∀ k i, hA I (uR k) (b i) = 0 ∧ hA I (uR k) (d i) = 0) ∧
      (∀ i j, hA I (d i) (b j) = if i = j then η else 0) ∧
      ∀ i j, ZMod' I g (hA I (bwd i) (b j) - if i = j then ew else 0) ∧
        ZMod' I g (hA I (d i) (bw j) - if i = j then ew else 0) := by
  classical
  have hεu : ∀ k, ε • uR k - u0 k ∈ mL I g := fun k => by
    have h2 := lf_eps_vec_cong h1ε (hu0 k)
    have e : ε • uR k - u0 k = ε • (uR k - u0 k) + (ε • u0 k - u0 k) := by rw [smul_sub]; abel
    rw [e]
    exact (mL I g).add_mem (hc k) h2
  have huL : ∀ k, ε • uR k ∈ I.Lf := fun k => by
    have e : ε • uR k = (ε • uR k - u0 k) + u0 k := by abel
    rw [e]
    exact I.Lf.add_mem (lf_mL_le I g (hεu k)) (hu0 k)
  have hz0 : ∀ v : VA I, v - v ∈ mL I g := fun v => by
    rw [sub_self]
    exact (mL I g).zero_mem
  have hG : ∀ k l, ZMod' I g (ε * lfGram I uR k l - Q0 k l) := fun k l => by
    have e1 : ε * lfGram I uR k l = hA I (ε • uR k) (ε • uR l) := by
      simp only [lfGram, Matrix.of_apply]
      rw [hA_smul_left_eq_sigA_mul, hA_smul_right_eq_mul, hσε, ← mul_assoc, hεε]
    have h1 := lf_hA_cong I g (hu0 k) (huL l) (hεu k) (hεu l)
    have h2 := Z_add (ha := h1) (hb := hgr k l)
    convert h2 using 1
    rw [e1]
    ring
  have hGQ : ∀ k l, ZMod' I g (ε * (lfGram I uR * Q0) k l - (1 : Matrix ι ι (I.E ⊗[I.F] Af I.F)) k l) := fun k l => by
    have hs := Z_sum (I := I) (g := g) (s := Finset.univ)
      (f := fun m => Q0 m l * (ε * lfGram I uR k m - Q0 k m))
      (h := fun m _ => zMod'_mul_of_mem_intAf I g (hQ0O m l) (hG k m))
    convert hs using 1
    try dsimp only
    rw [← hQ0, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  choose tG htG heG using hGQ
  obtain ⟨M, hMO, hM1, -, -⟩ := lf_inv_on I g hεO hU (Matrix.of tG) (fun i j => htG i j)
  have hE : ε • (lfGram I uR * Q0) = ε • (1 + (g : I.E ⊗[I.F] Af I.F) • Matrix.of tG) := by
    ext k l
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.of_apply]
    linear_combination ε * heG k l - (lfGram I uR * Q0) k l * hεε
  have hPQ : ε • (lfGram I uR * (Q0 * M)) = ε • 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.smul_mul, hE, Matrix.smul_mul, hM1]
  have hQ : ∀ k l, (Q0 * M) k l ∈ IntAf I.F I.E := fun k l => by
    rw [Matrix.mul_apply]
    exact sum_mem fun m _ => mul_mem (hQ0O k m) (hMO m l)
  have hZy : ∀ y, y ∈ I.Lf → (∀ l, ZMod' I g (hA I (u0 l) y)) → ∀ l, ZMod' I g (hA I (ε • uR l) y) :=
    fun y hy hy0 l => by
      have h1 := lf_hA_cong I g (hu0 l) hy (hεu l) (hz0 y)
      have h2 := Z_add (ha := h1) (hb := hy0 l)
      simpa using h2
  obtain ⟨b', hb'L, hb'o, hb'c⟩ : ∃ b' : Fin m → VA I, (∀ i, b' i ∈ I.Lf) ∧
      (∀ i k, hA I (uR k) (b' i) = 0) ∧ ∀ i, b' i - bw i ∈ mL I g :=
    ⟨fun i => lfProj I ε uR (Q0 * M) (bw i),
      fun i => lf_proj_mem I ε uR (Q0 * M) hεO hεε hσε huL hQ (hbL i).1,
      fun i k => lf_proj_orth I ε uR (Q0 * M) hPQ (bw i) k,
      fun i => lf_proj_cong I ε uR (Q0 * M) g hεε hσε h1ε huL hQ (hbL i).1
        (hZy (bw i) (hbL i).1 fun l => (hW l i).1)⟩
  obtain ⟨d', hd'L, hd'o, hd'c⟩ : ∃ d' : Fin m → VA I, (∀ i, d' i ∈ I.Lf) ∧
      (∀ i k, hA I (uR k) (d' i) = 0) ∧ ∀ i, d' i - bwd i ∈ mL I g :=
    ⟨fun i => lfProj I ε uR (Q0 * M) (bwd i),
      fun i => lf_proj_mem I ε uR (Q0 * M) hεO hεε hσε huL hQ (hbL i).2,
      fun i k => lf_proj_orth I ε uR (Q0 * M) hPQ (bwd i) k,
      fun i => lf_proj_cong I ε uR (Q0 * M) g hεε hσε h1ε huL hQ (hbL i).2
        (hZy (bwd i) (hbL i).2 fun l => (hW l i).2)⟩
  have hH : ∀ i j, ZMod' I g (hA I (d' i) (b' j) - if i = j then ew else 0) := fun i j => by
    have h1 := lf_hA_cong I g (hbL i).2 (hb'L j) (hd'c i) (hb'c j)
    have h2 := Z_add (ha := h1) (hb := hdual i j)
    convert h2 using 1
    ring
  have hηO : ε * ew ∈ IntAf I.F I.E := mul_mem hεO hewO
  have hηη : ε * ew * (ε * ew) = ε * ew := by linear_combination ew * ew * hεε + ε * hewi
  have hηew : ε * ew * ew = ε * ew := by rw [mul_assoc, hewi]
  obtain ⟨t1, ht1, he1⟩ := id h1ε
  have hewη : ZMod' I g (ew - ε * ew) := ⟨t1 * ew, mul_mem ht1 hewO, by linear_combination ew * he1⟩
  have hηU : ∀ s ∈ IntAf I.F I.E, ∃ s' ∈ IntAf I.F I.E,
      ε * ew * ((1 + (g : I.E ⊗[I.F] Af I.F) * s) * s') = ε * ew := fun s hs => by
    obtain ⟨s', hs', he⟩ := hU s hs
    exact ⟨s', hs', by linear_combination ew * he⟩
  choose tH htH heH using hH
  obtain ⟨N, hNO, hN1, -, hNc⟩ := lf_inv_on I g hηO hηU (Matrix.of tH) (fun i j => htH i j)
  have hEH : (ε * ew) • (Matrix.of fun i j => hA I (d' i) (b' j)) =
      (ε * ew) • (1 + (g : I.E ⊗[I.F] Af I.F) • Matrix.of tH) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    have h := heH i j
    split_ifs at h ⊢
    · linear_combination (ε * ew) * h + hηew
    · linear_combination (ε * ew) * h
  have hHN : ∀ i j, ε * ew * ∑ l, hA I (d' i) (b' l) * N l j =
      ε * ew * (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] Af I.F)) i j := by
    have h : (ε * ew) • ((Matrix.of fun i j => hA I (d' i) (b' j)) * N) = (ε * ew) • 1 := by
      rw [← Matrix.smul_mul, hEH, Matrix.smul_mul, hN1]
    intro i j
    have := congrFun (congrFun h i) j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.of_apply] using this
  refine ⟨ε * ew, fun j => ∑ l, (ε * ew * N l j) • b' l, fun i => sigA I (ε * ew) • d' i, hηO, hηη, hηew,
    hewη, hηU, fun i => ⟨?_, ?_, ?_, ?_⟩, fun k i => ⟨?_, ?_⟩, fun i j => ?_, fun i j => ⟨?_, ?_⟩⟩
  · exact I.Lf.sum_mem fun l _ => lf_memL_smul I (mul_mem hηO (hNO l i)) (hb'L l)
  · exact lf_memL_smul I (sigA_mem (ha := hηO)) (hd'L i)
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    linear_combination N l i * hηη
  · rw [smul_smul, ← map_mul, hηη]
  · rw [lf_hA_sum_right]
    exact Finset.sum_eq_zero fun l _ => by rw [hA_smul_right_eq_mul, hb'o l k, mul_zero]
  · rw [hA_smul_right_eq_mul, hd'o i k, mul_zero]
  · rw [lf_hA_sum_right]
    have e3 : ∀ l, hA I (sigA I (ε * ew) • d' i) ((ε * ew * N l j) • b' l) =
        ε * ew * (hA I (d' i) (b' l) * N l j) := fun l => by
      rw [hA_smul_right_eq_mul, hA_smul_left_eq_sigA_mul, sigA_sigA]
      linear_combination (N l j * hA I (d' i) (b' l)) * hηη
    rw [Finset.sum_congr rfl fun l _ => e3 l, ← Finset.mul_sum, hHN i j, Matrix.one_apply]
    split_ifs <;> ring
  · have hK : ∀ l, ZMod' I g (hA I (bwd i) (b' l) - if i = l then ew else 0) := fun l => by
      have h1 := lf_hA_cong I g (hbL i).2 (hb'L l) (hz0 (bwd i)) (hb'c l)
      have h2 := Z_add (ha := h1) (hb := hdual i l)
      convert h2 using 1
      ring
    have A1 := Z_sum (I := I) (g := g) (s := Finset.univ)
      (f := fun l => ε * ew * N l j * (hA I (bwd i) (b' l) - if i = l then ew else 0))
      (h := fun l _ => zMod'_mul_of_mem_intAf I g (mul_mem hηO (hNO l j)) (hK l))
    have A3 : ZMod' I g (ε * ew * (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] Af I.F)) i j - if i = j then ew else 0) := by
      rw [Matrix.one_apply]
      split_ifs
      · rw [mul_one]
        obtain ⟨t, ht, he⟩ := hewη
        exact ⟨-t, neg_mem ht, by linear_combination -he⟩
      · exact ⟨0, zero_mem _, by ring⟩
    have hs : ∑ l, ε * ew * N l j * (if i = l then ew else 0) = ε * ew * N i j := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      linear_combination (ε * N i j) * hewi
    have h4 := Z_add (ha := Z_add (ha := A1) (hb := hNc i j)) (hb := A3)
    convert h4 using 1
    try dsimp only
    rw [lf_hA_sum_right]
    simp only [hA_smul_right_eq_mul]
    rw [Finset.sum_congr rfl fun l _ => mul_sub (ε * ew * N l j) (hA I (bwd i) (b' l))
      (if i = l then ew else 0), Finset.sum_sub_distrib, hs]
    ring
  · have hK : ZMod' I g (hA I (d' i) (bw j) - if i = j then ew else 0) := by
      have h1 := lf_hA_cong I g (hbL i).2 (hbL j).1 (hd'c i) (hz0 (bw j))
      have h2 := Z_add (ha := h1) (hb := hdual i j)
      convert h2 using 1
      ring
    have B2 : ZMod' I g (ε * ew * (if i = j then ew else 0) - if i = j then ew else 0) := by
      split_ifs
      · obtain ⟨t, ht, he⟩ := hewη
        exact ⟨-t, neg_mem ht, by linear_combination -he + hηew⟩
      · exact ⟨0, zero_mem _, by ring⟩
    have h4 := Z_add (ha := zMod'_mul_of_mem_intAf I g hηO hK) (hb := B2)
    convert h4 using 1
    rw [hA_smul_left_eq_sigA_mul, sigA_sigA]
    ring

section HidaSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

def lfUR : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit → VA X.B.I :=
  Sum.elim (Sum.elim (fun a => incl X.B.I (X.eR a)) (fun a => incl X.B.I (X.fR a)))
    (fun _ => X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u))

def referenceFrameFamily : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit → VA X.B.I :=
  Sum.elim (Sum.elim X.e0 X.f0) (fun _ => X.z0)

theorem reference_frame_mem_lattice (k : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) : referenceFrameFamily X k ∈ X.B.I.Lf := by
  rcases k with (a | a) | ⟨⟩
  exacts [(X.vectorsInLattice.1 a).1, (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1]

theorem reference_frame_gram_congruence (k l : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) :
    ZMod' X.B.I X.B.g (hA X.B.I (referenceFrameFamily X k) (referenceFrameFamily X l) - hyperbolicMinusOneMatrix (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) D.R.rS k l) := by
  rcases k with (a | a) | ⟨⟩ <;> rcases l with (b | b) | ⟨⟩ <;>
    simp only [hyperbolicMinusOneMatrix, referenceFrameFamily, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, sub_zero, sub_neg_eq_add]
  · exact (X.gramIntegral a b).1
  · exact (X.gramIntegral a b).2.2
  · exact (X.formsAtZero.2 a).1
  · have h := Z_sig (ha := (X.gramIntegral b a).2.2)
    rw [map_sub, ← hA_symm] at h
    by_cases hab : a = b
    · subst hab
      simpa using h
    · simpa [hab, Ne.symm hab] using h
  · exact (X.gramIntegral a b).2.1
  · exact (X.formsAtZero.2 a).2
  · have h := Z_sig (ha := (X.formsAtZero.2 b).1)
    rwa [← hA_symm] at h
  · have h := Z_sig (ha := (X.formsAtZero.2 b).2)
    rwa [← hA_symm] at h
  · exact X.formsAtZero.1

theorem lf_uR_cong {ε : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hεO : ε ∈ IntAf X.B.I.F X.B.I.E)
    (hU : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      ε * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ε)
    (k : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) : ε • (lfUR X u k - referenceFrameFamily X k) ∈ mL X.B.I X.B.g := by
  rcases k with (a | a) | ⟨⟩
  · have h := lf_inAt_eps hεO hU (X.basisApprox a).1
    have e : ε • (lfUR X u (Sum.inl (Sum.inl a)) - referenceFrameFamily X (Sum.inl (Sum.inl a))) =
        -(ε • (X.e0 a - incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX a)))) := by
      rw [← smul_neg, neg_sub]; rfl
    rw [e]
    exact neg_mem h
  · have h := lf_inAt_eps hεO hU (X.basisApprox a).2
    have e : ε • (lfUR X u (Sum.inl (Sum.inr a)) - referenceFrameFamily X (Sum.inl (Sum.inr a))) =
        -(ε • (X.f0 a - incl X.B.I (crdOf X.B.I X.ιE X.bas (X.fY a)))) := by
      rw [← smul_neg, neg_sub]; rfl
    rw [e]
    exact neg_mem h
  · exact lf_inAt_eps hεO hU (X.xu_z u)

theorem reference_frame_beta_orthogonal (k : (Fin D.R.rS ⊕ Fin D.R.rS) ⊕ Unit) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (referenceFrameFamily X k) (X.bw j)) ∧ ZMod' X.B.I X.B.g (hA X.B.I (referenceFrameFamily X k) (X.bwd j)) := by
  rcases k with (a | a) | ⟨⟩
  exacts [⟨((X.weightVectorsIntegral j).2.2 a).1, ((X.weightVectorsIntegral j).2.2 a).2.2.1⟩,
    ⟨((X.weightVectorsIntegral j).2.2 a).2.1, ((X.weightVectorsIntegral j).2.2 a).2.2.2⟩, ⟨(X.weightVectorsIntegral j).1, (X.weightVectorsIntegral j).2.1⟩]

end HidaSetting

end LeviFramePf

namespace LeviOntoSPf

open LeviFramePf

theorem exact_dual_frame_exists {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : FrameOfS X u := by
  unfold FrameOfS SIdem DualFrame IsDualFrame
  intro hS
  obtain ⟨ε, hεO, hεε, hσε, h1ε, hU⟩ := hS
  obtain ⟨η, b, d, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := lf_frame_core X.B.I X.B.g hεO hεε hσε h1ε hU
    (lfUR X u) (referenceFrameFamily X) (hyperbolicMinusOneMatrix _ D.R.rS) (hyperbolic_matrix_integral X.B.I D.R.rS) (hyperbolic_matrix_sq_eq_one _ D.R.rS) (reference_frame_mem_lattice X)
    (lf_uR_cong X u hεO hU) (reference_frame_gram_congruence X) X.ew X.bw X.bwd X.ew_idem X.ew_int X.vectorsInLattice.2.2 X.bw_w X.bwd_w
    X.bw_dual (reference_frame_beta_orthogonal X)
  refine ⟨η, b, d, h1, h2, h3, h4, h5, h6, ?_, h8, h9⟩
  intro y hy i
  unfold fixV at hy
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hy
  · exact h7 (Sum.inl (Sum.inl a)) i
  · exact h7 (Sum.inl (Sum.inr a)) i
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h7 (Sum.inr ()) i

end LeviOntoSPf

end Formalism.L2.SG.Pf.NormSteps
