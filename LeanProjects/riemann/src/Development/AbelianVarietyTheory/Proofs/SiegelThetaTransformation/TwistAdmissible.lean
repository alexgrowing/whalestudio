import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistAdm

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem int_smul_mem (Λ : Lt E n) (k : ℤ) {v : Fin n → E} (h : v ∈ Λ) : (k : E) • v ∈ Λ := by
  rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem h k

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.nat_smul_mem (Λ : _root_.GlobalTheory.SW.Lt E n) (k : ℕ)
    {v : Fin n → E} (h : v ∈ Λ) : (k : E) • v ∈ Λ :=
  _root_.GlobalTheory.SW.Base.nat_smul_mem Λ k h

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.single_mem_std (a : Fin N) :
    (Pi.single a 1 : Fin N → E) ∈ _root_.GlobalTheory.SW.stdL E N := by
  unfold _root_.GlobalTheory.SW.stdL
  exact Submodule.subset_span ⟨a, rfl⟩

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.col_eq (x : Matrix (Fin n) (Fin N) E) (a : Fin N) :
    xᵀ a = x *ᵥ Pi.single a 1 := by
  ext i
  simp [Matrix.mulVec_single]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec {Λ : _root_.GlobalTheory.SW.Lt E n}
    {y : Matrix (Fin n) (Fin N) E} (h : _root_.GlobalTheory.SW.ColsIn Λ y)
    {v : Fin N → E} (hv : v ∈ _root_.GlobalTheory.SW.stdL E N) : y *ᵥ v ∈ Λ := by
  unfold _root_.GlobalTheory.SW.stdL at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [← _root_.GlobalTheory.SW.TwistAdm.col_eq]
    exact h a
  | zero => simp [Λ.zero_mem]
  | add u w _ _ hu hw =>
    rw [Matrix.mulVec_add]
    exact Λ.add_mem hu hw
  | smul r w _ hw =>
    rw [Matrix.mulVec_smul]
    exact Λ.smul_mem r hw

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.mem_of_coprime (Λ : _root_.GlobalTheory.SW.Lt E n) {u w : ℕ}
    (h : u.Coprime w) {v : Fin n → E}
    (hu : (u : E) • v ∈ Λ) (hw : (w : E) • v ∈ Λ) : v ∈ Λ :=
  _root_.GlobalTheory.SW.Base.mem_of_coprime Λ h hu hw

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.relIndex_ne_zero (A B : _root_.GlobalTheory.SW.Lt E N)
    (hB : B.FG) {t : ℕ} (ht : 0 < t)
    (h : ∀ v ∈ B, (t : E) • v ∈ A) : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
  set I : Ideal (𝓞 E) := Ideal.span {(t : 𝓞 E)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast ht.ne'
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Finite (B ⧸ (⊤ : Submodule (𝓞 E) B)) := inferInstance
  have hfin : Finite (B ⧸ I • (⊤ : Submodule (𝓞 E) B)) :=
    Submodule.finite_quotient_smul I ((Submodule.fg_top B).mpr hB)
  have hle : I • (⊤ : Submodule (𝓞 E) B) ≤ A.comap B.subtype := by
    rw [Submodule.smul_le]
    intro r hr b _
    obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have key : ((t : 𝓞 E)) • (b : Fin N → E) = (t : E) • (b : Fin N → E) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, mul_smul, key]
    exact A.smul_mem r' (h b b.2)
  haveI : Finite (B ⧸ A.comap B.subtype) :=
    Finite.of_surjective (Submodule.factor hle) (by
      rintro ⟨x⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩)
  exact @AddSubgroup.index_ne_zero_of_finite _ _ _ this

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.std_fg : (_root_.GlobalTheory.SW.stdL E N).FG := by
  unfold _root_.GlobalTheory.SW.stdL
  exact Submodule.fg_span (Set.finite_range _)

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.TwistAdm.cols_of_cond {R s : ℕ} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    {Λ : _root_.GlobalTheory.SW.Lt E n} {x : Matrix (Fin n) (Fin N) E}
    (hs : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛)
    (hx : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) :
    _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x)) := by
  intro a
  have h1 := hx _ (hs _ (_root_.GlobalTheory.SW.TwistAdm.single_mem_std a))
  have e : ((R : E) • ((s : E) • x))ᵀ a = (R : E) • (x *ᵥ ((s : E) • Pi.single a 1)) := by
    rw [_root_.GlobalTheory.SW.TwistAdm.col_eq, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_smul]
  rw [e]
  exact h1

variable [IsCMField E]

theorem val_smul {M R : ℕ} {φ : Fam E n N} (hφ : admitted M R φ) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M)
    {x : Matrix (Fin n) (Fin N) E} {s : ℕ} (hs : s ≡ 1 [MOD R ^ 2])
    (hx : ColsIn Λ ((R : E) • x)) : φ Λ ((s : E) • x) = φ Λ x := by
  obtain ⟨k, hk⟩ := hs.symm.dvd
  have h1 : (s : E) = 1 + R * (k * R) := by
    have := congrArg (Int.cast : ℤ → E) hk
    push_cast at this
    linear_combination this
  have : (s : E) • x = x + (R : E) • ((k : E) • ((R : E) • x)) := by
    rw [h1, add_smul, one_smul, smul_smul, smul_smul, mul_assoc]
  rw [this]
  refine hφ.per Λ hΛ _ _ fun a => ?_
  exact int_smul_mem Λ k (hx a)

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
omit [IsCMField E] in
theorem _root_.GlobalTheory.SW.TwistAdm.exists_mult {M R : ℕ} (hR : 0 < R)
    {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (h : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N)) :
    ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛 := by
  obtain ⟨s, -, hcop, -, hstd⟩ := h
  have hc : s.Coprime (R ^ 2) :=
    Nat.Coprime.pow_right 2 (Nat.Coprime.coprime_dvd_right (dvd_mul_right R M) hcop)
  rcases Nat.lt_or_ge 1 (R ^ 2) with hlt | hle
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hlt
    refine ⟨s * m, ?_, fun v hv => ?_⟩
    · show s * m % R ^ 2 = 1 % R ^ 2
      rw [hm, Nat.mod_eq_of_lt hlt]
    · have := _root_.GlobalTheory.SW.TwistAdm.nat_smul_mem 𝔛 m (hstd v hv)
      rwa [smul_smul, ← Nat.cast_mul, Nat.mul_comm] at this
  · have hR1 : R ^ 2 = 1 :=
      le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hR.ne'))
    exact ⟨s, by rw [hR1]; exact Nat.modEq_one, hstd⟩

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
omit [IsCMField E] in
theorem _root_.GlobalTheory.SW.TwistAdm.twist_eq {R : ℕ} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (φ : _root_.GlobalTheory.SW.Fam E n N)
    (hex : ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛)
    (Λ : _root_.GlobalTheory.SW.Lt E n)
    (x : Matrix (Fin n) (Fin N) E) : _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x =
      if ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ then φ Λ ((hex.choose : E) • x) else 0 := by
  by_cases h : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ
  · rw [if_pos h]
    simp only [_root_.GlobalTheory.SW.twist]
    rw [dif_pos ⟨h, hex⟩]
  · rw [if_neg h]
    simp only [_root_.GlobalTheory.SW.twist]
    rw [dif_neg (fun h' => h h'.1)]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
private theorem adm_apply_add_mul_intCast_smul {M R : ℕ} {φ : _root_.GlobalTheory.SW.Fam E n N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ) {Λ : _root_.GlobalTheory.SW.Lt E n}
    (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) (x y : Matrix (Fin n) (Fin N) E)
    (hy : _root_.GlobalTheory.SW.ColsIn Λ y) (k : ℤ) : φ Λ (x + ((R : E) * (k : E)) • y) = φ Λ x := by
  have hnat : ∀ (z : Matrix (Fin n) (Fin N) E) (m : ℕ),
      φ Λ (z + ((R : E) * (m : E)) • y) = φ Λ z := by
    intro z m
    rw [mul_smul]
    refine hφ.per Λ hΛ z _ (fun a => ?_)
    rw [Matrix.transpose_smul]
    exact _root_.GlobalTheory.SW.TwistAdm.nat_smul_mem Λ m (hy a)
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hnat x m
  · have := hnat (x + ((R : E) * (((-(m : ℤ)) : ℤ) : E)) • y) m
    rw [← this]
    congr 1
    push_cast
    rw [add_assoc, ← add_smul]
    simp

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
private theorem adm_apply_mul_congr_one_mod_sq {M R : ℕ} {φ : _root_.GlobalTheory.SW.Fam E n N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ) {Λ : _root_.GlobalTheory.SW.Lt E n}
    (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) (x : Matrix (Fin n) (Fin N) E) {t u : ℕ}
    (hu : u ≡ 1 [MOD R ^ 2]) (ht : _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((t : E) • x))) :
    φ Λ (((t * u : ℕ) : E) • x) = φ Λ ((t : E) • x) := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hu.symm
  have hkE : (u : E) = 1 + (R : E) ^ 2 * (k : E) := by
    have := congrArg (Int.cast : ℤ → E) hk
    push_cast at this
    linear_combination this
  have e : ((t * u : ℕ) : E) = (t : E) + ((R : E) * (k : E)) * ((R : E) * (t : E)) := by
    push_cast
    rw [hkE]
    ring
  rw [← adm_apply_add_mul_intCast_smul hφ hΛ ((t : E) • x) _ ht k]
  congr 1
  simp only [e, add_smul, mul_smul]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
theorem _root_.GlobalTheory.SW.TwistAdm.twist_val {M R : ℕ} {φ : _root_.GlobalTheory.SW.Fam E n N}
    {𝔛 : _root_.GlobalTheory.SW.Lt E N} (hφ : _root_.GlobalTheory.SW.admitted M R φ)
    (hA : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N))
    {Λ : _root_.GlobalTheory.SW.Lt E n} (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M)
    (x : Matrix (Fin n) (Fin N) E) (s : ℕ) (hs : s ≡ 1 [MOD R ^ 2])
    (h : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) (hx : _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x))) :
    _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x = φ Λ ((s : E) • x) := by
  obtain ⟨-, hR⟩ := hφ.pos
  have hex := _root_.GlobalTheory.SW.TwistAdm.exists_mult hR hA
  rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, if_pos h]
  have hc0 := _root_.GlobalTheory.SW.TwistAdm.cols_of_cond hex.choose_spec.2 h
  rw [← adm_apply_mul_congr_one_mod_sq hφ hΛ x hs hc0, Nat.mul_comm hex.choose s,
    adm_apply_mul_congr_one_mod_sq hφ hΛ x hex.choose_spec.1 hx]

theorem twist_std {M R : ℕ} {φ : Fam E n N} (hφ : admitted M R φ) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) :
    twist R (stdL E N) φ Λ = φ Λ := by
  have hA : Agree (R * M) (stdL E N) (stdL E N) :=
    ⟨1, one_pos, Nat.coprime_one_left _, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
  funext x
  by_cases h : ∀ ξ ∈ stdL E N, (R : E) • (x *ᵥ ξ) ∈ Λ
  · rw [twist_val hφ hA hΛ x 1 rfl h (cols_of_cond (fun v hv => by simpa using hv) h)]
    simp
  · rw [twist_eq φ (exists_mult hφ.pos.2 hA), if_neg h]
    by_contra h0
    refine h fun ξ hξ => ?_
    rw [← Matrix.smul_mulVec]
    exact colsIn_mulVec (hφ.supp Λ hΛ x (Ne.symm h0)) hξ

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
theorem _root_.GlobalTheory.SW.TwistAdm.twist_level {M R : ℕ}
    {φ : _root_.GlobalTheory.SW.Fam E n N} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ)
    (hA : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N))
    (a : Matrix (Fin N) (Fin N) E) (c : ℕ)
    (h1 : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ _root_.GlobalTheory.SW.stdL E N)
    {Λ : _root_.GlobalTheory.SW.Lt E n} (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) :
    _root_.GlobalTheory.SW.LevelL Λ (R * c) (fun x : Matrix (Fin n) (Fin N) E =>
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ
        (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by
  obtain ⟨-, hR⟩ := hφ.pos
  have hex := _root_.GlobalTheory.SW.TwistAdm.exists_mult hR hA
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have hx' : _root_.GlobalTheory.SW.twist R 𝔛 φ Λ (x * a) ≠ 0 := hx
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex] at hx'
    have hcond : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ := by
      by_contra hc
      exact hx' (if_neg hc)
    intro b
    obtain ⟨ξ, hξ, hξa⟩ := h1 _ (_root_.GlobalTheory.SW.TwistAdm.single_mem_std b)
    have hmem := hcond ξ hξ
    rw [← Matrix.mulVec_mulVec, hξa, Matrix.mulVec_smul, smul_smul] at hmem
    rw [_root_.GlobalTheory.SW.TwistAdm.col_eq, Matrix.smul_mulVec, Nat.cast_mul]
    exact hmem
  · show _root_.GlobalTheory.SW.twist R 𝔛 φ Λ ((x + ((R * c : ℕ) : E) • y) * a) =
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ (x * a)
    have hmv : ∀ ξ, ((x + ((R * c : ℕ) : E) • y) * a) *ᵥ ξ =
        (x * a) *ᵥ ξ + (R : E) • (y *ᵥ ((c : E) • (a *ᵥ ξ))) := by
      intro ξ
      rw [Matrix.add_mul, Matrix.add_mulVec, Matrix.smul_mul, Matrix.smul_mulVec]
      simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul, Nat.cast_mul]
    have hiff : (∀ ξ ∈ 𝔛, (R : E) • (((x + ((R * c : ℕ) : E) • y) * a) *ᵥ ξ) ∈ Λ) ↔
        ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ := by
      refine forall₂_congr fun ξ hξ => ?_
      rw [hmv, smul_add]
      exact Λ.add_mem_iff_left (_root_.GlobalTheory.SW.TwistAdm.nat_smul_mem Λ R
        (_root_.GlobalTheory.SW.TwistAdm.nat_smul_mem Λ R
          (_root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec hy (h2 ξ hξ))))
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, _root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex]
    by_cases hc : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ
    · rw [if_pos (hiff.mpr hc), if_pos hc]
      have hs := hex.choose_spec.2
      have hcols : _root_.GlobalTheory.SW.ColsIn Λ ((hex.choose : E) • (y * ((c : E) • a))) := by
        intro b
        have hb := h2 _ (hs _ (_root_.GlobalTheory.SW.TwistAdm.single_mem_std b))
        have hmem := _root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec hy hb
        have e : ((hex.choose : E) • (y * ((c : E) • a)))ᵀ b =
            y *ᵥ ((c : E) • (a *ᵥ ((hex.choose : E) • Pi.single b 1))) := by
          rw [_root_.GlobalTheory.SW.TwistAdm.col_eq, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
            Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
            Matrix.mulVec_smul, smul_comm]
        rw [e]
        exact hmem
      have key : (hex.choose : E) • ((x + ((R * c : ℕ) : E) • y) * a) =
          (hex.choose : E) • (x * a) + (R : E) • ((hex.choose : E) • (y * ((c : E) • a))) := by
        rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
        push_cast
        module
      rw [key]
      exact hφ.per Λ hΛ _ _ hcols
    · rw [if_neg (mt hiff.mp hc), if_neg hc]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
theorem _root_.GlobalTheory.SW.TwistAdm.twist_adm {M R : ℕ}
    {φ : _root_.GlobalTheory.SW.Fam E n N} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ)
    (hA : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N)) :
    ∃ R', _root_.GlobalTheory.SW.admitted M R' (_root_.GlobalTheory.SW.twist R 𝔛 φ) := by
  obtain ⟨hM, hR⟩ := hφ.pos
  obtain ⟨t, ht0, htcop, hXstd, hstdX⟩ := id hA
  have hex := _root_.GlobalTheory.SW.TwistAdm.exists_mult hR hA
  have hlev : ∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      _root_.GlobalTheory.SW.LevelL Λ (R * t) (_root_.GlobalTheory.SW.twist R 𝔛 φ Λ) := by
    intro Λ hΛ
    have := _root_.GlobalTheory.SW.TwistAdm.twist_level hφ hA (1 : Matrix (Fin N) (Fin N) E) t
      (fun v hv => ⟨(t : E) • v, hstdX v hv, by rw [Matrix.one_mulVec]⟩)
      (fun ξ hξ => by rw [Matrix.one_mulVec]; exact hXstd ξ hξ) hΛ
    simpa only [Matrix.mul_one] using this
  refine ⟨R * t, ⟨⟨hM, Nat.mul_pos hR ht0⟩, ?_, fun Λ hΛ => (hlev Λ hΛ).1,
    fun Λ hΛ => (hlev Λ hΛ).2, ?_⟩⟩
  · intro h hh Λ hΛ Λ' hΛ' hcar x
    have hcar' : ∀ v, v ∈ Λ ↔ h *ᵥ v ∈ Λ' := hcar
    have hiff : (∀ ξ ∈ 𝔛, (R : E) • ((h * x) *ᵥ ξ) ∈ Λ') ↔ ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ := by
      refine forall₂_congr fun ξ _ => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hcar']
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, _root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex]
    by_cases hc : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ
    · rw [if_pos (hiff.mpr hc), if_pos hc, ← Matrix.mul_smul]
      exact hφ.equiv h hh Λ hΛ Λ' hΛ' hcar _
    · rw [if_neg (mt hiff.mp hc), if_neg hc]
  · intro Λ hΛ Λ' hΛ' hagr x hx hx'
    obtain ⟨u, hu0, hucop, hΛΛ', hΛ'Λ⟩ := id hagr
    have hut1 : u.Coprime t := Nat.Coprime.coprime_dvd_right ((dvd_mul_left t R).mul_right M) hucop
    have hut : u.Coprime (t * t) := Nat.Coprime.mul_right hut1 hut1
    have transfer : ∀ {A B : _root_.GlobalTheory.SW.Lt E n},
        _root_.GlobalTheory.SW.ColsIn B (((R * t : ℕ) : E) • x) → (∀ v ∈ A, (u : E) • v ∈ B) →
        ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ A → (R : E) • (x *ᵥ ξ) ∈ B := by
      intro A B hB hAB ξ hξ hmem
      refine _root_.GlobalTheory.SW.TwistAdm.mem_of_coprime B hut (hAB _ hmem) ?_
      have hB' := _root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec hB (hXstd ξ hξ)
      have e : ((t * t : ℕ) : E) • (R : E) • (x *ᵥ ξ) = (((R * t : ℕ) : E) • x) *ᵥ ((t : E) • ξ) := by
        simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
        congr 1
        push_cast
        ring
      rw [e]
      exact hB'
    have hiff : (∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) ↔ ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ' :=
      ⟨fun hc ξ hξ => transfer hx' hΛΛ' ξ hξ (hc ξ hξ),
        fun hc ξ hξ => transfer hx hΛ'Λ ξ hξ (hc ξ hξ)⟩
    rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, _root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex]
    by_cases hc : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ
    · rw [if_pos hc, if_pos (hiff.mp hc)]
      have hagrRM : _root_.GlobalTheory.SW.Agree (R * M) Λ Λ' :=
        ⟨u, hu0, Nat.Coprime.coprime_dvd_right
          (Nat.mul_dvd_mul (dvd_mul_right R t) dvd_rfl) hucop, hΛΛ', hΛ'Λ⟩
      exact hφ.loc Λ hΛ Λ' hΛ' hagrRM _
        (_root_.GlobalTheory.SW.TwistAdm.cols_of_cond hex.choose_spec.2 hc)
        (_root_.GlobalTheory.SW.TwistAdm.cols_of_cond hex.choose_spec.2 (hiff.mp hc))
    · rw [if_neg hc, if_neg (mt hiff.mpr hc)]

omit [IsCMField E] in
theorem gidx_pos {m : ℕ} {𝔛 : Lt E N} (hfg : 𝔛.FG) (hA : Agree m 𝔛 (stdL E N)) : 0 < gidx 𝔛 := by
  obtain ⟨t, ht, -, h1, h2⟩ := hA
  exact div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_ne_zero _ _ hfg ht h1)))
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero (relIndex_ne_zero _ _ std_fg ht h2)))

end GlobalTheory.SW.TwistAdm

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in

theorem _root_.GlobalTheory.SW.twist_admissible : ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (n N M R : ℕ) (φ : _root_.GlobalTheory.SW.Fam E n N)
    (𝔛 : _root_.GlobalTheory.SW.Lt E N), _root_.GlobalTheory.SW.admitted M R φ → 𝔛.FG →
    _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N) →
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M, ∀ x (s : ℕ), s ≡ 1 [MOD R ^ 2] →
      (∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) → _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x)) →
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x = φ Λ ((s : E) • x)) ∧
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      _root_.GlobalTheory.SW.twist R (_root_.GlobalTheory.SW.stdL E N) φ Λ = φ Λ) ∧
    _root_.GlobalTheory.SW.gidx (_root_.GlobalTheory.SW.stdL E N) = 1 ∧
    0 < _root_.GlobalTheory.SW.gidx 𝔛 ∧
    (∃ R', _root_.GlobalTheory.SW.admitted M R' (_root_.GlobalTheory.SW.twist R 𝔛 φ)) ∧
    ∀ (a : Matrix (Fin N) (Fin N) E) (c : ℕ), 0 < c → a.det ≠ 0 →
      (∀ v ∈ _root_.GlobalTheory.SW.stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v) →
      (∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ _root_.GlobalTheory.SW.stdL E N) →
      ∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
        _root_.GlobalTheory.SW.LevelL Λ (R * c) (fun x => _root_.GlobalTheory.SW.twist R 𝔛 φ Λ (x * a)) := by
  intro E _ _ _ n N M R φ 𝔛 hφ hfg hA
  refine ⟨fun Λ hΛ x s hs h hx => _root_.GlobalTheory.SW.TwistAdm.twist_val hφ hA hΛ x s hs h hx,
    fun Λ hΛ => ?_, _root_.GlobalTheory.SW.Base.gidx_stdL, ?_,
    _root_.GlobalTheory.SW.TwistAdm.twist_adm hφ hA,
    fun a c _ _ h1 h2 Λ hΛ => _root_.GlobalTheory.SW.TwistAdm.twist_level hφ hA a c h1 h2 hΛ⟩
  · have hstd1 : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N,
        ((1 : ℕ) : E) • v ∈ _root_.GlobalTheory.SW.stdL E N := fun v hv => by
      rwa [Nat.cast_one, one_smul]
    have hAstd : _root_.GlobalTheory.SW.Agree (R * M) (_root_.GlobalTheory.SW.stdL E N)
        (_root_.GlobalTheory.SW.stdL E N) :=
      ⟨1, one_pos, Nat.coprime_one_left _, hstd1, hstd1⟩
    funext x
    by_cases hc : ∀ ξ ∈ _root_.GlobalTheory.SW.stdL E N, (R : E) • (x *ᵥ ξ) ∈ Λ
    · have hcols := _root_.GlobalTheory.SW.TwistAdm.cols_of_cond hstd1 hc
      rw [_root_.GlobalTheory.SW.TwistAdm.twist_val hφ hAstd hΛ x 1 (Nat.ModEq.refl 1) hc hcols,
        Nat.cast_one, one_smul]
    · have hex : ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ _root_.GlobalTheory.SW.stdL E N,
          (s : E) • v ∈ _root_.GlobalTheory.SW.stdL E N := ⟨1, Nat.ModEq.refl 1, hstd1⟩
      rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, if_neg hc]
      by_contra hne
      exact hc fun ξ hξ => by
        rw [← Matrix.smul_mulVec]
        exact _root_.GlobalTheory.SW.TwistAdm.colsIn_mulVec (hφ.supp Λ hΛ x (Ne.symm hne)) hξ
  · obtain ⟨t, ht0, -, hXstd, hstdX⟩ := id hA
    unfold _root_.GlobalTheory.SW.gidx
    have h1 := _root_.GlobalTheory.SW.TwistAdm.relIndex_ne_zero (_root_.GlobalTheory.SW.stdL E N) 𝔛
      hfg ht0 hXstd
    have h2 := _root_.GlobalTheory.SW.TwistAdm.relIndex_ne_zero 𝔛 _ _root_.GlobalTheory.SW.TwistAdm.std_fg
      ht0 hstdX
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h1)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h2))
