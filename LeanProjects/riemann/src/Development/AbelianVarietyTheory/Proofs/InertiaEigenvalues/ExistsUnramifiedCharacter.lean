import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section
namespace GlobalTheory.UnramZl
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem modEq_of_pow_modEq {l d : ℕ} (hl : 1 < l) (hd : 0 < d) {a b : ℕ}
    (h : l ^ a ≡ l ^ b [MOD l ^ d - 1]) : a ≡ b [MOD d] := by
  wlog hab : a ≤ b generalizing a b
  · exact (this h.symm (le_of_not_ge hab)).symm
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : l ^ d - 1 ∣ l ^ (a + c) - l ^ a :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hl.le hab)).1 h
  rw [pow_add, ← Nat.mul_sub_one] at h1
  have hcop : (l ^ d - 1).Coprime (l ^ a) := by
    apply Nat.Coprime.pow_right
    have h2 : (l ^ d - 1).Coprime (l ^ d) := by
      have : l ^ d = (l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
      conv_rhs => rw [this]
      simp
    exact h2.coprime_dvd_right (dvd_pow_self l hd.ne')
  have h3 := Nat.gcd_eq_left (hcop.dvd_of_dvd_mul_left h1)
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h3
  have h4 : l ^ d.gcd c = l ^ d := by
    have := Nat.one_le_pow (d.gcd c) l (by omega)
    have := Nat.one_le_pow d l (by omega)
    omega
  have h5 : d ∣ c := (Nat.pow_right_injective hl h4) ▸ Nat.gcd_dvd_right d c
  exact (Nat.modEq_iff_dvd' hab).2 (by simpa using h5)

variable {l : ℕ} [hl : Fact l.Prime]

theorem lev_pos (n : ℕ) : 0 < l ^ (l ^ n) - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow (pow_pos hl.out.pos n).ne' hl.out.one_lt)

theorem not_dvd_lev (n : ℕ) : ¬ l ∣ l ^ (l ^ n) - 1 := fun h => by
  have h1 : l ∣ l ^ (l ^ n) := dvd_pow_self l (pow_pos hl.out.pos n).ne'
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hl.out.pos)] at h2
  exact hl.out.not_dvd_one h2

def Acts (g : GQ l) (n a : ℕ) : Prop :=
  ∀ ζ : Om l, ζ ^ (l ^ (l ^ n) - 1) = 1 → g ζ = ζ ^ (l ^ a)

theorem exists_prim (n : ℕ) : ∃ ξ : Om l, IsPrimitiveRoot ξ (l ^ (l ^ n) - 1) := by
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) _

theorem Acts.uniq {g : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts g n b) :
    a ≡ b [MOD l ^ n] := by
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  have h := (ha ξ hξ.pow_eq_one).symm.trans (hb ξ hξ.pow_eq_one)
  rw [(hξ.isOfFinOrder (lev_pos n).ne').pow_eq_pow_iff_modEq, ← hξ.eq_orderOf] at h
  exact modEq_of_pow_modEq hl.out.one_lt (pow_pos hl.out.pos n) h

theorem Acts.down {g : GQ l} {n a : ℕ} (ha : Acts g (n + 1) a) : Acts g n a := fun ζ hζ => by
  obtain ⟨c, hc⟩ := Nat.pow_sub_one_dvd_pow_sub_one l (pow_dvd_pow l (Nat.le_succ n))
  exact ha ζ (by rw [hc, pow_mul, hζ, one_pow])

theorem Acts.mul {g h : GQ l} {n a b : ℕ} (ha : Acts g n a) (hb : Acts h n b) :
    Acts (g * h) n (a + b) := fun ζ hζ => by
  rw [AlgEquiv.mul_apply, hb ζ hζ, map_pow, ha ζ hζ, ← pow_mul, pow_add]

theorem exists_acts (g : GQ l) (n : ℕ) : ∃ a, Acts g n a :=
  gal_root g (lev_pos n) (not_dvd_lev n)

theorem exists_deg (g : GQ l) :
    ∃ x : ℤ_[l], ∀ n a, Acts g n a → PadicInt.toZModPow n x = (a : ZMod (l ^ n)) := by
  choose a ha using exists_acts g
  have hdv : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - a i := fun i => by
    have := ((ha i).uniq (ha (i + 1)).down).dvd
    exact_mod_cast this
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv), fun n b hb => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (a n : ℤ)) l hdv n, Int.cast_natCast]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 ((ha n).uniq hb)

def deg (g : GQ l) : ℤ_[l] := (exists_deg g).choose

theorem deg_spec {g : GQ l} {n a : ℕ} (h : Acts g n a) :
    PadicInt.toZModPow n (deg g) = (a : ZMod (l ^ n)) := (exists_deg g).choose_spec n a h

theorem deg_mul (g h : GQ l) : deg (g * h) = deg g + deg h := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  obtain ⟨a, ha⟩ := exists_acts g n
  obtain ⟨b, hb⟩ := exists_acts h n
  rw [map_add, deg_spec ha, deg_spec hb, deg_spec (ha.mul hb), Nat.cast_add]

theorem deg_eq_nat {g : GQ l} {a : ℕ} (h : ∀ n, Acts g n a) : deg g = a := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [deg_spec (h n), map_natCast]

theorem deg_one : deg (1 : GQ l) = 0 := by
  simpa using deg_eq_nat (g := (1 : GQ l)) (a := 0) fun n ζ _ => by simp

theorem deg_pow (g : GQ l) (N : ℕ) : deg (g ^ N) = N * deg g := by
  induction N with
  | zero => simp [deg_one]
  | succ N ih => rw [pow_succ, deg_mul, ih]; push_cast; ring

theorem continuous_deg : Continuous (deg : GQ l → ℤ_[l]) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt l hε
  obtain ⟨ξ, hξ⟩ := exists_prim (l := l) n
  haveI : NeZero (l ^ (l ^ n) - 1) := ⟨(lev_pos n).ne'⟩
  have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) ξ).preimage (continuous_mul_left g⁻¹)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ MulAction.stabilizer (GQ l) ξ by simp)] with h hh
  have h1 : (g⁻¹ * h) ξ = ξ := hh
  have h2 : h ξ = g ξ := by
    conv_rhs => rw [← h1, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
  obtain ⟨a, ha⟩ := exists_acts g n
  have hb : Acts h n a := fun ζ hζ => by
    rw [← ha ζ hζ]
    obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hζ
    rw [map_pow, map_pow, h2]
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    deg_spec ha, deg_spec hb, sub_self]

theorem deg_inertia {g : GQ l} (h : ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) : deg g = 0 := by
  simpa using deg_eq_nat (g := g) (a := 0) fun n ζ hζ => by
    let a : OO l := ⟨ζ, (norm_root (lev_pos n) hζ).le⟩
    have ha : a ^ (l ^ (l ^ n) - 1) = 1 := Subtype.ext hζ
    have := res_inj (lev_pos n) (not_dvd_lev n) (a := galO g a) (b := a)
      (by rw [← map_pow, ha, map_one]) ha ((res_eq_iff _ _).2 (h ζ a.2))
    rw [pow_zero, pow_one]
    exact congrArg Subtype.val this

theorem exists_deg_eq_one : ∃ g : GQ l, deg g = 1 := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  simpa using deg_eq_nat (g := g) (a := 1) fun n ζ hζ => by
    let c : ↥(MaximalUnramifiedExtension l) :=
      ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨_, lev_pos n, not_dvd_lev n, hζ⟩⟩
    have := hσ c _ (lev_pos n) (not_dvd_lev n) (Subtype.ext hζ)
    rw [show ζ = (c : Om l) from rfl, hg, this, pow_one]; rfl

theorem exists_unramified_character : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    ∃ δ : ↥(GK K) → ℚ_[l], Continuous δ ∧ (∀ g h, δ (g * h) = δ g + δ h) ∧
      (∀ g ∈ IK K, δ g = 0) ∧ ∃ g, δ g ≠ 0 := by
  intro l _ K
  refine ⟨fun g => (deg (g : GQ l) : ℚ_[l]),
    continuous_subtype_val.comp (continuous_deg.comp continuous_subtype_val),
    fun g h => by simp [deg_mul], fun g hg => ?_, ?_⟩
  · have : deg (g : GQ l) = 0 := by
      unfold IK at hg
      induction hg using Subgroup.closure_induction with
      | mem x hx => exact deg_inertia hx
      | one => exact deg_one
      | mul x y _ _ hx hy => rw [Subgroup.coe_mul, deg_mul, hx, hy, add_zero]
      | inv x _ hx =>
        have := deg_mul ((x⁻¹ : ↥(GK K)) : GQ l) x
        rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, deg_one, hx, add_zero] at this
        exact this.symm
    simp [this]
  · obtain ⟨φ, hφ⟩ := exists_deg_eq_one (l := l)
    haveI := K.2
    haveI : Finite (GQ l ⧸ GK K) :=
      Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K.1)
    obtain ⟨N, hN, -, hm⟩ := (GK K).exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite φ
    refine ⟨⟨φ ^ N, hm⟩, ?_⟩
    simp [deg_pow, hφ, hN.ne']

end GlobalTheory.UnramZl
