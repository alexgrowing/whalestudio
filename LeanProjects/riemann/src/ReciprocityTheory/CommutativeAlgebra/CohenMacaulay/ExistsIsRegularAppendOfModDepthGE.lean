import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Lemmata.GeneralBFactSide.Imports

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem ModDepthGE.mono {m n : ℕ} (hmn : m ≤ n) (h : ModDepthGE R M n) : ModDepthGE R M m := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨rs.take m, by simp [hlen, hmn], fun r hr => hmem r (List.mem_of_mem_take hr), ?_⟩
  have hw : IsWeaklyRegular M (rs.take m) := by
    have := hreg.toIsWeaklyRegular
    rw [← List.take_append_drop m rs, isWeaklyRegular_append_iff] at this
    exact this.1
  refine ⟨hw, fun htop => hreg.top_ne_smul ?_⟩
  refine le_antisymm (htop.le.trans (Submodule.smul_mono_left ?_)) le_top
  exact Ideal.span_mono fun r hr => List.mem_of_mem_take hr

theorem ModDepthGE.of_quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R (QuotSMulTop x M) n) : ModDepthGE R M (n + 1) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨x :: rs, by simp [hlen], ?_, (isRegular_cons_iff M x rs).mpr ⟨reg, hreg⟩⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hx
  · exact hmem r hr

theorem exch_socle {x y : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) {a : M} (ha : a ∉ x • (⊤ : Submodule R M))
    (hma : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M)) :
    ∃ b : M, b ∉ y • (⊤ : Submodule R M) ∧
      ∀ z ∈ maximalIdeal R, z • b ∈ y • (⊤ : Submodule R M) := by
  obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma y hy)
  refine ⟨b, ?_, ?_⟩
  · intro hby
    obtain ⟨b', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hby
    apply ha
    have : y • a = y • (x • b') := by rw [← hb, smul_comm]
    rw [ry this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · intro z hz
    obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hma z hz)
    have : x • (z • b) = x • (y • c) := by
      rw [smul_comm x z, hb, smul_comm x y, hc, smul_comm]
    rw [rx this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

section Noeth

variable [IsNoetherianRing R]

theorem socle_of_max_mem_ass {N : Type*} [AddCommGroup N] [Module R N]
    (h : maximalIdeal R ∈ associatedPrimes R N) :
    ∃ a : N, a ≠ 0 ∧ ∀ z ∈ maximalIdeal R, z • a = 0 := by
  obtain ⟨-, a, ha⟩ := Submodule.isAssociatedPrime_iff.mp h
  refine ⟨a, ?_, fun z hz => ?_⟩
  · rintro rfl
    apply (maximalIdeal.isMaximal R).ne_top
    rw [ha, eq_top_iff]
    intro r _
    exact Submodule.mem_colon_singleton.mpr (by simp)
  · rw [ha] at hz
    simpa using Submodule.mem_colon_singleton.mp hz

theorem max_not_mem_ass_of_reg {N : Type*} [AddCommGroup N] [Module R N] {w : R}
    (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular N w) :
    maximalIdeal R ∉ associatedPrimes R N := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  exact ha (rw (show w • a = w • (0 : N) by rw [hz w hw, smul_zero]))

theorem max_not_mem_ass_swap {x y w : R} (hy : y ∈ maximalIdeal R) (rx : IsSMulRegular M x)
    (ry : IsSMulRegular M y) (hw : w ∈ maximalIdeal R) (rw : IsSMulRegular (QuotSMulTop y M) w) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x M) := by
  intro h
  obtain ⟨a, ha, hz⟩ := socle_of_max_mem_ass h
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have ha' : a ∉ x • (⊤ : Submodule R M) := fun h' => ha ((Submodule.Quotient.mk_eq_zero _).mpr h')
  have hz' : ∀ z ∈ maximalIdeal R, z • a ∈ x • (⊤ : Submodule R M) := fun z hz0 =>
    (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_smul]; exact hz z hz0)
  obtain ⟨b, hb, hzb⟩ := exch_socle hy rx ry ha' hz'
  have hb0 : (Submodule.Quotient.mk b : QuotSMulTop y M) ≠ 0 :=
    fun h' => hb ((Submodule.Quotient.mk_eq_zero _).mp h')
  apply hb0
  apply rw
  show w • _ = w • (0 : QuotSMulTop y M)
  rw [smul_zero, ← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hzb w hw)

theorem exists_reg_both {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (h₁ : maximalIdeal R ∉ associatedPrimes R N₁) (h₂ : maximalIdeal R ∉ associatedPrimes R N₂) :
    ∃ z ∈ maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  first | exact Bl.general_b_fact_side.goal1 .. | (apply Bl.general_b_fact_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_side.goal1 <;> assumption)

end Noeth

section Main

variable [IsNoetherianRing R]

universe u in
theorem exists_regular_sequence_cons (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R},
      x ∈ maximalIdeal R → IsSMulRegular N x → ModDepthGE R N (n + 1) →
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular N (x :: rs) := by
  induction n with
  | zero =>
    intro N _ _ _ x hx reg h
    obtain ⟨rs, -, -, hreg⟩ := h
    have := hreg.nontrivial
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    exact ⟨[], rfl, by simp, (isRegular_cons_iff N x []).mpr ⟨reg, IsRegular.nil R _⟩⟩
  | succ n ih =>
    intro N _ _ _ x hx reg h
    obtain ⟨ys0, hlen, hmem, hreg⟩ := h
    rcases ys0 with _ | ⟨y, ys⟩
    · simp at hlen
    rcases ys with _ | ⟨y', ys'⟩
    · simp at hlen
    have hy : y ∈ maximalIdeal R := hmem y (by simp)
    have hy' : y' ∈ maximalIdeal R := hmem y' (by simp)
    have := hreg.nontrivial
    obtain ⟨ry, hys⟩ := (isRegular_cons_iff N y _).mp hreg
    have ry' : IsSMulRegular (QuotSMulTop y N) y' := ((isRegular_cons_iff _ _ _).mp hys).1
    have hAy := max_not_mem_ass_of_reg hy' ry'
    have hAx := max_not_mem_ass_swap hy reg ry hy' ry'
    obtain ⟨z, hz, rzx, rzy⟩ := exists_reg_both hAx hAy
    have hdy : ModDepthGE R (QuotSMulTop y N) (n + 1) :=
      ⟨y' :: ys', by simpa using hlen, fun r hr => hmem r (List.mem_cons_of_mem _ hr), hys⟩
    obtain ⟨zs, hzs, hzsm, hzreg⟩ := ih (QuotSMulTop y N) hz rzy hdy
    have h1 : IsRegular N (y :: z :: zs) := (isRegular_cons_iff N y _).mpr ⟨ry, hzreg⟩
    have h2 : IsRegular N (z :: y :: zs) := IsLocalRing.isRegular_of_perm h1 (List.Perm.swap z y zs)
    obtain ⟨rz, hyz⟩ := (isRegular_cons_iff N z _).mp h2
    have : Nontrivial (QuotSMulTop x N) := nontrivial_quotSMulTop_of_mem_maximalIdeal N hx
    have : Nontrivial (QuotSMulTop z (QuotSMulTop x N)) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal _ hz
    have h3 : IsRegular N [x, z] :=
      (isRegular_cons_iff N x _).mpr ⟨reg, (isRegular_cons_iff _ z _).mpr ⟨rzx, IsRegular.nil R _⟩⟩
    have h4 : IsRegular N [z, x] := IsLocalRing.isRegular_of_perm h3 (List.Perm.swap z x [])
    have rxz : IsSMulRegular (QuotSMulTop z N) x :=
      ((isRegular_cons_iff _ x _).mp ((isRegular_cons_iff N z _).mp h4).2).1
    have hdz : ModDepthGE R (QuotSMulTop z N) (n + 1) := by
      refine ⟨y :: zs, by simp [hzs], fun r hr => ?_, hyz⟩
      rcases List.mem_cons.mp hr with rfl | hr
      exacts [hy, hzsm r hr]
    obtain ⟨ws, hws, hwsm, hwreg⟩ := ih (QuotSMulTop z N) hx rxz hdz
    have h5 : IsRegular N (z :: x :: ws) := (isRegular_cons_iff N z _).mpr ⟨rz, hwreg⟩
    have h6 : IsRegular N (x :: z :: ws) := IsLocalRing.isRegular_of_perm h5 (List.Perm.swap x z ws)
    refine ⟨z :: ws, by simp [hws], fun r hr => ?_, h6⟩
    rcases List.mem_cons.mp hr with rfl | hr
    exacts [hz, hwsm r hr]

end Main

variable [IsNoetherianRing R] [Module.Finite R M]

theorem exists_isRegular_cons_of_modDepthGE {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) {n : ℕ} (h : ModDepthGE R M (n + 1)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular M (x :: rs) :=
  exists_regular_sequence_cons n M hx reg h

theorem ModDepthGE.quotSMulTop {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R M (n + 1)) : ModDepthGE R (QuotSMulTop x M) n := by
  obtain ⟨rs, hl, hm, hr⟩ := exists_isRegular_cons_of_modDepthGE hx reg h
  exact ⟨rs, hl, hm, ((isRegular_cons_iff M x rs).mp hr).2⟩

theorem exists_isRegular_append_of_modDepthGE {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular M rs) {n : ℕ} (h : ModDepthGE R M (rs.length + n)) :
    ∃ rs' : List R, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular M (rs ++ rs') := by
  induction rs generalizing M with
  | nil =>
    simp only [List.length_nil, zero_add] at h
    obtain ⟨rs', hl, hm, hr⟩ := h
    exact ⟨rs', hl, hm, hr⟩
  | cons r rs ih =>
    have hr : r ∈ maximalIdeal R := hrs r (by simp)
    obtain ⟨rreg, hq⟩ := (isRegular_cons_iff M r rs).mp reg
    have hlen : (r :: rs).length + n = rs.length + n + 1 := by simp; omega
    rw [hlen] at h
    obtain ⟨rs', hl, hm, hreg'⟩ := ih (M := QuotSMulTop r M)
      (fun s hs => hrs s (List.mem_cons_of_mem _ hs)) hq (ModDepthGE.quotSMulTop hr rreg h)
    exact ⟨rs', hl, hm, (isRegular_cons_iff M r _).mpr ⟨rreg, hreg'⟩⟩

end ReciprocityTheory.CA
