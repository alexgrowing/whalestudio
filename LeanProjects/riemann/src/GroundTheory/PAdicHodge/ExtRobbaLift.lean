import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaGamma
import GroundTheory.PAdicHodge.ExtRobbaFrob
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open IsLocalRing

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem mem_int_of_map_mem_int (ψ : Γ →+* Γ) (g : L →+* L) (hg : ∀ c, ‖g c‖ ≤ 1 ↔ ‖c‖ ≤ 1)
    {u : Γ} (hπ : ψ T.π = T.π * u) (hu : u ∈ T.int) (hu1 : ‖T.red u‖ = 1)
    (hteich : ∀ c, ψ (T.teich c) = T.teich (g c)) {y : Γ} (hy : ψ y ∈ T.int) : y ∈ T.int := by
  classical
  by_contra hyint
  rw [T.mem_int_iff] at hyint
  push_neg at hyint
  set n0 := Nat.find hyint with hn0def
  have hn0 : 1 < ‖T.coeff y n0‖ := Nat.find_spec hyint
  have hlow : ∀ i < n0, ‖T.coeff y i‖ ≤ 1 := fun i hi => by
    have := Nat.find_min hyint hi; push_neg at this; exact this

  have hA : ψ (T.partialSum y n0) ∈ T.int := by
    simp only [partialSum, finSum, map_sum, map_mul, map_pow, hπ, hteich]
    refine Subring.sum_mem _ fun i hi => mul_mem (pow_mem (mul_mem T.π_mem_int hu) _) ?_
    exact T.teich_mem_int ((hg _).2 (hlow i (Finset.mem_range.1 hi)))

  set t := T.tail^[n0] y with htdef
  have hy' : y = T.partialSum y n0 + T.π ^ n0 * t := by rw [← T.sub_partialSum]; ring
  have ht : t = T.teich (T.coeff y n0) + T.π * T.tail t := by
    have := T.eq_teich_add_π_mul_tail t
    rwa [show T.red t = T.coeff y n0 from rfl] at this
  have hX : ψ y - ψ (T.partialSum y n0) =
      T.π ^ n0 * (u ^ n0 * T.teich (g (T.coeff y n0)) + T.π * (u ^ (n0 + 1) * ψ (T.tail t))) := by
    have e : ψ y = ψ (T.partialSum y n0) + ψ (T.π ^ n0 * t) := by rw [← map_add, ← hy']
    have hψt : ψ t = T.teich (g (T.coeff y n0)) + T.π * u * ψ (T.tail t) := by
      conv_lhs => rw [ht]
      rw [map_add, map_mul, hteich, hπ]
    rw [e, add_sub_cancel_left, map_mul, map_pow, hπ, hψt]
    ring
  have hXint : ψ y - ψ (T.partialSum y n0) ∈ T.int := sub_mem hy hA
  have hc := (T.mem_int_iff.1 hXint) n0
  rw [hX] at hc
  have := T.coeff_π_pow_mul_add n0
    (u ^ n0 * T.teich (g (T.coeff y n0)) + T.π * (u ^ (n0 + 1) * ψ (T.tail t))) 0
  rw [zero_add] at this
  rw [this, coeff_zero, map_add, map_mul, map_mul, map_pow, red_teich, red_π, zero_mul, add_zero,
    norm_mul, norm_pow, hu1, one_pow, one_mul] at hc
  exact absurd ((hg _).1 hc) (not_le.2 hn0)

end TeichLift

namespace ExtRobba

section Lift

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : ResidueField (normInteger K) →+* L)
variable {ϖ : normInteger K} (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

def gammaTeichLift : TeichLift p L (Gamma p ι) where
  π := gammaPi p ι ϖ
  red := gammaRed p ι
  red_surjective := gammaRed_surjective p ι
  ker_red := ker_gammaRed p ι hϖ
  π_mem_nonZeroDivisors := gammaPi_mem_nonZeroDivisors p ι hϖ
  isAdicComplete := isAdicComplete_gammaPi p ι hϖ
  int := gammaInt p ι
  π_mem_int := tmul_mem_gammaInt p ι (Subring.one_mem _) ϖ
  norm_red_le_one := fun _ hx => norm_gammaRed_le_one p ι hϖ hι hx
  exists_mem_int := fun _ ha => exists_mem_gammaInt_gammaRed_eq p ι ha
  exists_eq_π_mul := fun _ hx h0 => exists_mem_gammaInt_eq_gammaPi_mul p ι hϖ hι hx h0
  mem_int_of_approx := fun _ h => mem_gammaInt_of_forall p ι hϖ hι h

@[simp] theorem gammaTeichLift_π : (gammaTeichLift p ι hϖ hι).π = gammaPi p ι ϖ := rfl

@[simp] theorem gammaTeichLift_red : (gammaTeichLift p ι hϖ hι).red = gammaRed p ι := rfl

@[simp] theorem gammaTeichLift_int : (gammaTeichLift p ι hϖ hι).int = gammaInt p ι := rfl

include hι in

theorem norm_ι_eq_one {c : ResidueField (normInteger K)} (hc : c ≠ 0) : ‖ι c‖ = 1 := by
  have h1 : ‖ι c‖ * ‖ι c⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, norm_one]
  have ha := hι c
  have hb := hι c⁻¹
  nlinarith [norm_nonneg (ι c), norm_nonneg (ι c⁻¹)]

end Lift

section Frob

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField (normInteger K)) p]
  [PerfectRing (ResidueField (normInteger K)) p]
variable (σ : K →+* K) (hσn : ∀ x, ‖σ x‖ = ‖x‖)

def intFrob : normInteger K →+* normInteger K :=
  (σ.comp (normInteger K).subtype).codRestrict (normInteger K) fun x => mem_normInteger.2 (by
    rw [RingHom.comp_apply, hσn]; exact mem_normInteger.1 x.2)

@[simp] theorem coe_intFrob (x : normInteger K) : ((intFrob σ hσn x : normInteger K) : K) = σ x := rfl

variable (a : ℕ) (hσr : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ p ^ a‖ < 1)

include hσr in

theorem residue_intFrob (x : normInteger K) :
    residue (normInteger K) (intFrob σ hσn x) = residue (normInteger K) x ^ p ^ a := by
  rw [← sub_eq_zero, ← map_pow, ← map_sub, residue_eq_zero_iff_norm_lt_one]
  push_cast
  exact hσr x (mem_normInteger.1 x.2)

variable {ϖ : normInteger K} (hϖ : Irreducible ϖ)

include hσn hσr hϖ in

theorem exists_intFrob_approx (n : ℕ) (z : normInteger K) (hz : ‖(z : K)‖ ≤ ‖(ϖ : K)‖ ^ n) :
    ∃ x : normInteger K, ‖σ x - z‖ ≤ ‖(ϖ : K)‖ ^ (n + 1) := by
  have hϖ0 : ‖(ϖ : K)‖ ≠ 0 := (norm_unif_pos hϖ).ne'
  have hσϖ : ‖σ ϖ‖ = ‖(ϖ : K)‖ := hσn _
  have hσϖ0 : σ ϖ ≠ 0 := fun h => hϖ0 (by rw [← hσϖ, h, norm_zero])
  have hz' : ‖(z : K) / σ ϖ ^ n‖ ≤ 1 := by
    rw [norm_div, norm_pow, hσϖ, div_le_one (pow_pos (norm_unif_pos hϖ) n)]; exact hz
  set z' : normInteger K := ⟨(z : K) / σ ϖ ^ n, mem_normInteger.2 hz'⟩ with hz'def
  obtain ⟨x0, hx0⟩ := residue_surjective
    ((iterateFrobeniusEquiv (ResidueField (normInteger K)) p a).symm (residue (normInteger K) z'))
  have hres : residue (normInteger K) (intFrob σ hσn x0 - z') = 0 := by
    rw [map_sub, residue_intFrob p σ hσn a hσr, hx0, ← iterateFrobeniusEquiv_def,
      RingEquiv.apply_symm_apply, sub_self]
  rw [residue_eq_zero_iff_norm_lt_one] at hres
  have h1 := norm_le_norm_unif_of_lt_one hϖ hres
  push_cast at h1
  refine ⟨ϖ ^ n * x0, ?_⟩
  have e : σ ((ϖ ^ n * x0 : normInteger K) : K) - z = σ ϖ ^ n * (σ x0 - (z : K) / σ ϖ ^ n) := by
    push_cast
    rw [map_mul, map_pow, mul_sub, mul_div_cancel₀ _ (pow_ne_zero _ hσϖ0)]
  rw [e, norm_mul, norm_pow, hσϖ, pow_succ]
  exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (norm_nonneg _) _)

include hσn hσr hϖ in
theorem exists_intFrob_near (n : ℕ) (z : normInteger K) :
    ∃ x : normInteger K, ‖σ x - z‖ ≤ ‖(ϖ : K)‖ ^ n := by
  induction n generalizing z with
  | zero => exact ⟨0, by simpa using mem_normInteger.1 z.2⟩
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih z
    have hw : ‖((z - intFrob σ hσn x : normInteger K) : K)‖ ≤ ‖(ϖ : K)‖ ^ n := by
      push_cast; rw [norm_sub_rev]; exact hx
    obtain ⟨x', hx'⟩ := exists_intFrob_approx p σ hσn a hσr hϖ n _ hw
    refine ⟨x + x', ?_⟩
    have e : σ ((x + x' : normInteger K) : K) - z = σ x' - ((z - intFrob σ hσn x : normInteger K) : K) := by
      push_cast; rw [map_add, coe_intFrob]; ring
    rw [e]; exact hx'

include hσn hσr hϖ in

theorem intFrob_bijective : Function.Bijective (intFrob σ hσn) := by
  refine ⟨fun x y h => Subtype.ext (σ.injective (by
    have := congrArg (fun z : normInteger K => (z : K)) h; simpa using this)), fun y => ?_⟩
  have hiso : Isometry σ := AddMonoidHomClass.isometry_of_norm σ hσn
  have hclosed : IsClosed (Set.range σ) := hiso.isClosedEmbedding.isClosed_range
  have hmem : (y : K) ∈ closure (Set.range σ) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_unif_lt_one hϖ)
    obtain ⟨x, hx⟩ := exists_intFrob_near p σ hσn a hσr hϖ n y
    exact ⟨σ x, ⟨x, rfl⟩, by rw [dist_eq_norm, norm_sub_rev]; exact hx.trans_lt hn⟩
  rw [hclosed.closure_eq] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hx1 : ‖x‖ ≤ 1 := by rw [← hσn, hx]; exact mem_normInteger.1 y.2
  exact ⟨⟨x, mem_normInteger.2 hx1⟩, Subtype.ext hx⟩

def frobUnifUnit (hϖ : Irreducible ϖ) : normInteger K :=
  ⟨σ ϖ / ϖ, mem_normInteger.2 (by
    rw [norm_div, hσn, div_self (norm_unif_pos hϖ).ne'])⟩

theorem norm_frobUnifUnit : ‖((frobUnifUnit σ hσn hϖ : normInteger K) : K)‖ = 1 := by
  show ‖σ ϖ / ϖ‖ = 1
  rw [norm_div, hσn, div_self (norm_unif_pos hϖ).ne']

theorem intFrob_unif : intFrob σ hσn ϖ = ϖ * frobUnifUnit σ hσn hϖ := by
  apply Subtype.ext
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => (norm_unif_pos hϖ).ne' (by rw [h, norm_zero])
  show σ ϖ = (ϖ : K) * (σ ϖ / ϖ)
  rw [mul_div_cancel₀ _ hϖ0]

theorem residue_frobUnifUnit_ne_zero : residue (normInteger K) (frobUnifUnit σ hσn hϖ) ≠ 0 := by
  rw [Ne, residue_eq_zero_iff_norm_lt_one, norm_frobUnifUnit]
  exact lt_irrefl 1

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p]
variable (ι : ResidueField (normInteger K) →+* L) (hι : ∀ a, ‖ι a‖ ≤ 1)

def gammaPhiEquiv : Gamma p ι ≃+* Gamma p ι :=
  RingEquiv.ofBijective (gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr))
    (gammaPhi_bijective p ι a _ _ (intFrob_bijective p σ hσn a hσr hϖ) hϖ)

theorem gammaPhiEquiv_apply (x : Gamma p ι) :
    gammaPhiEquiv p σ hσn a hσr hϖ ι x =
      gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) x := rfl

theorem gammaPhi_gammaPi_eq :
    gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) (gammaPi p ι ϖ) =
      gammaPi p ι ϖ * gammaOfInt p ι (frobUnifUnit σ hσn hϖ) := by
  rw [gammaPhi_gammaPi, intFrob_unif σ hσn hϖ, gammaPi_eq, gammaPi_eq, gammaOfInt_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

include hι in
theorem norm_gammaRed_frobUnifUnit :
    ‖gammaRed p ι (gammaOfInt p ι (frobUnifUnit σ hσn hϖ))‖ = 1 := by
  rw [gammaOfInt_apply, gammaRed_tmul, map_one, WittVector.one_coeff_zero, one_mul]
  exact norm_ι_eq_one ι hι (residue_frobUnifUnit_ne_zero σ hσn hϖ)

def gammaTeichFrob : TeichLift.TeichFrob (gammaTeichLift p ι hϖ hι) where
  φ := gammaPhiEquiv p σ hσn a hσr hϖ ι
  a := a
  red_φ := fun x => gammaRed_gammaPhi p ι a _ _ x
  u := gammaOfInt p ι (frobUnifUnit σ hσn hϖ)
  φ_π := gammaPhi_gammaPi_eq p σ hσn a hσr hϖ ι
  u_mem_int := tmul_mem_gammaInt p ι (Subring.one_mem _) _
  norm_red_u := norm_gammaRed_frobUnifUnit p σ hσn hϖ ι hι
  map_int := fun _ hx => gammaPhi_mem_gammaInt p ι a _ _ hx
  symm_map_int := fun x hx => by
    set T := gammaTeichLift p ι hϖ hι
    have hψ : ∀ y, T.red (gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) y) =
        iterateFrobenius L p a (T.red y) := fun y => by
      rw [iterateFrobenius_def]; exact gammaRed_gammaPhi p ι a _ _ y
    refine T.mem_int_of_map_mem_int
      (gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr)) (iterateFrobenius L p a)
      (fun c => by
        rw [iterateFrobenius_def, norm_pow]
        exact pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero))
      (gammaPhi_gammaPi_eq p σ hσn a hσr hϖ ι) (tmul_mem_gammaInt p ι (Subring.one_mem _) _)
      (norm_gammaRed_frobUnifUnit p σ hσn hϖ ι hι) (T.map_teich _ _ hψ) ?_
    rw [← gammaPhiEquiv_apply p σ hσn a hσr hϖ ι, RingEquiv.apply_symm_apply]
    exact hx

@[simp] theorem gammaTeichFrob_a : (gammaTeichFrob p σ hσn a hσr hϖ ι hι).a = a := rfl

theorem gammaTeichFrob_φ (x : Gamma p ι) :
    (gammaTeichFrob p σ hσn a hσr hϖ ι hι).φ x =
      gammaPhi p ι a (intFrob σ hσn) (residue_intFrob p σ hσn a hσr) x := rfl

end Frob

end ExtRobba

end GroundTheory.PAdicHodge
