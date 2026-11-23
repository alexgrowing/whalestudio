import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrDefs
import Lemmata.PadicNatCastNorm.NormNatCastOfNotDvd
import Lemmata.FirstBlockLemmaC.Imports
import Lemmata.FirstBlockLemmaD.Imports

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField

variable {p : ℕ} [Fact p.Prime]

noncomputable abbrev res : Obar p →+* kbar p := IsLocalRing.residue (Obar p)

theorem norm_le_one (x : Obar p) : ‖(x : PadicAlgCl p)‖ ≤ 1 := mem_Obar_iff.1 x.2

theorem norm_sub_le_max' (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  first | exact Bl.FirstBlockLemmaD.goal1 .. | (apply Bl.FirstBlockLemmaD.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaD.goal1 <;> assumption)

theorem isUnit_iff (x : Obar p) : IsUnit x ↔ ‖(x : PadicAlgCl p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : Obar p) : PadicAlgCl p) * (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = 1 := by
      have h2 : (((u : Obar p) * ((u⁻¹ : (Obar p)ˣ) : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
        rw [u.mul_inv]; rfl
      exact h2
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have ha := norm_le_one (u : Obar p)
    have hb := norm_le_one ((u⁻¹ : (Obar p)ˣ) : Obar p)
    have hb0 := norm_nonneg ((u : Obar p) : PadicAlgCl p)
    nlinarith
  · intro h
    have hx0 : (x : PadicAlgCl p) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    have hi : ‖(x : PadicAlgCl p)⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(x : PadicAlgCl p)⁻¹, mem_Obar_iff.2 hi⟩ : Obar p) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0

theorem res_eq_zero_iff (x : Obar p) : res x = 0 ↔ ‖(x : PadicAlgCl p)‖ < 1 := by
  constructor
  · intro h
    by_contra hc
    have h1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm (norm_le_one x) (not_lt.1 hc)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit x).2 ((isUnit_iff x).2 h1) h
  · intro h
    by_contra hc
    have := (isUnit_iff x).1 ((IsLocalRing.residue_ne_zero_iff_isUnit x).1 hc)
    exact absurd this (ne_of_lt h)

theorem res_eq_iff (x y : Obar p) : res x = res y ↔ ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
  rfl

theorem mem_resK_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (c : kbar p) :
    c ∈ resK p K ↔ ∃ x : Obar p, (x : PadicAlgCl p) ∈ K ∧ res x = c := Iff.rfl

theorem resK_mono {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) : resK p K ≤ resK p L := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
  exact (mem_resK_iff L _).2 ⟨x, h hx, rfl⟩

theorem norm_GK {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

theorem norm_p_lt_one : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  have h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

scoped instance charP_kbar : CharP (kbar p) p := by
  obtain ⟨r, hr⟩ := CharP.exists (kbar p)
  have h0 : ((p : ℕ) : kbar p) = 0 := by
    have h1 : res ((p : ℕ) : Obar p) = 0 := by
      rw [res_eq_zero_iff]
      have : (((p : ℕ) : Obar p) : PadicAlgCl p) = ((p : ℕ) : PadicAlgCl p) := by simp
      rw [this]; exact norm_p_lt_one
    simpa using h1
  have h2 : r ∣ p := (CharP.cast_eq_zero_iff (kbar p) r p).1 h0
  have h3 : r = p := ((Nat.dvd_prime Fact.out).1 h2).resolve_left (CharP.char_ne_one (kbar p) r)
  exact h3 ▸ hr

theorem finite_resK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    Finite (resK p K) := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have hc : IsCompact (Metric.closedBall (0 : K) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := 1) one_pos
  classical
  let g : K → kbar p := fun x => if h : ‖(x : PadicAlgCl p)‖ ≤ 1 then res ⟨x, mem_Obar_iff.2 h⟩ else 0
  have hsub : (resK p K : Set (kbar p)) ⊆ g '' t := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
    have hxb : (⟨x, hx⟩ : K) ∈ Metric.closedBall (0 : K) 1 := by
      rw [mem_closedBall_zero_iff]; exact norm_le_one x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hxb)
    rw [Metric.mem_ball, dist_eq_norm] at hxy
    have hxy' : ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := hxy
    have hy1 : ‖(y : PadicAlgCl p)‖ ≤ 1 := by
      have h1 : (y : PadicAlgCl p) = (x : PadicAlgCl p) - ((x : PadicAlgCl p) - (y : PadicAlgCl p)) := by ring
      rw [h1]
      exact (norm_sub_le_max' _ _).trans (max_le (norm_le_one x) hxy'.le)
    refine ⟨y, hy, ?_⟩
    have hg : g y = res ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩ := dif_pos hy1
    rw [hg]
    exact ((res_eq_iff x ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩).2 hxy').symm
  exact (htf.image g).subset hsub

theorem qK_eq_pow (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : ℕ, 0 < f ∧ qK p K = p ^ f := by
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have hch : CharP (resK p K) p :=
    ((resK p K).subtype.charP_iff Subtype.val_injective p).2 inferInstance
  obtain ⟨n, -, hn⟩ := FiniteField.card (resK p K) p
  exact ⟨n, n.pos, by rw [qK, Nat.card_eq_fintype_card, hn]⟩

theorem one_lt_qK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    1 < qK p K := by
  obtain ⟨f, hf, h⟩ := qK_eq_pow K hK
  rw [h]
  exact Nat.one_lt_pow hf.ne' (Fact.out : p.Prime).one_lt

theorem not_dvd_qK_pow_sub_one (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {n : ℕ} (hn : 0 < n) : ¬ p ∣ qK p K ^ n - 1 := by
  obtain ⟨f, hf, h⟩ := qK_eq_pow K hK
  intro hd
  have h1 : p ∣ qK p K ^ n := by
    rw [h, ← pow_mul]; exact dvd_pow_self p (Nat.mul_pos hf hn).ne'
  have h2 : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by have := one_lt_qK K hK; omega)
  have h3 : p ∣ 1 := by
    have := (Nat.dvd_sub h1 hd)
    rwa [Nat.sub_sub_self h2] at this
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

theorem norm_eq_one_of_pow {m : ℕ} (hm : m ≠ 0) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) : ‖ζ‖ = 1 := by
  first | exact Bl.FirstBlockLemmaC.goal1 .. | (apply Bl.FirstBlockLemmaC.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaC.goal1 <;> assumption)

theorem norm_sub_one_of_pow {m : ℕ} (hm : ¬ p ∣ m) {η : PadicAlgCl p} (hη : η ^ m = 1) (h : η ≠ 1) :
    ‖η - 1‖ = 1 := by
  first | exact Bl.PadicNatCastNorm.goal1 .. | (apply Bl.PadicNatCastNorm.goal1 <;> assumption) | (intros; apply Bl.PadicNatCastNorm.goal1 <;> assumption)

theorem norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0] at hξ; exact zero_ne_one hξ
  have h1 : ζ - ξ = ξ * (ζ / ξ - 1) := by field_simp
  rw [h1, norm_mul, norm_eq_one_of_pow hm0 hξ, one_mul]
  apply norm_sub_one_of_pow hm
  · rw [div_pow, hζ, hξ, div_one]
  · intro h2; exact h ((div_eq_one_iff_eq hξ0).1 h2)

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
