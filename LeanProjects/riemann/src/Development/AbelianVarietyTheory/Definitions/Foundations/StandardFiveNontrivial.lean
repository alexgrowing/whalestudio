import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare

section Fn
variable {G : Type} [Group G] [Fintype G]

def conv (a b : G → ℂ) : G → ℂ := fun x => ∑ y, a y * b (y⁻¹ * x)

def op {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (e : G → ℂ) : Module.End ℂ M := ∑ γ, e γ • ρ γ

def rk {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (e : G → ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (op ρ e))

def IsProj (e : G → ℂ) : Prop := conv e e = e ∧ ∀ x, e x⁻¹ = (starRingEnd ℂ) (e x)

def zc (χ : G → ℂ) : G → ℂ := fun γ => χ 1 / (Fintype.card G : ℂ) * χ γ⁻¹

def eps (S : G → Prop) (χ : G → ℂ) : G → ℂ := fun γ => if S γ then (χ γ)⁻¹ / (Nat.card {u // S u} : ℂ) else 0

def dirac : G → ℂ := fun γ => if γ = 1 then 1 else 0

end Fn

def tens {ι G : Type} [Fintype ι] (e : ι → G → ℂ) : (ι → G) → ℂ := fun γ => ∏ v, e v (γ v)

def tens2 {G G' : Type} (a : G → ℂ) (b : G' → ℂ) : G × G' → ℂ := fun γ => a γ.1 * b γ.2

variable (g : ℕ) [Fact g.Prime] (N : ℕ)

abbrev GG : Type := GL (Fin N) (ZMod g)

def IsUp (u : GG g N) : Prop := (∀ a, u.val a a = 1) ∧ ∀ a b, b < a → u.val a b = 0

structure Lev where
  sharp : Bool
  s : ℕ
  k : ℕ
  hk : s + k < N
  ψ : AddChar (ZMod g) ℂ
  hψ : ψ ≠ 1
  co : Fin N → (ZMod g)ˣ

variable {g N}

def Lev.Mem (L : Lev g N) (u : GG g N) : Prop :=
  IsUp g N u ∧ (L.sharp = true → ∀ a b : Fin N, L.s ≤ a → (a : ℕ) < L.s + L.k → (b : ℕ) = L.s + L.k → u.val a b = 0)

def Lev.Edge (L : Lev g N) (a b : Fin N) : Prop :=
  if L.sharp = true then
    ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L.s ∧ ¬ (0 < L.k ∧ (a : ℕ) + 1 = L.s + L.k)) ∨ ((a : ℕ) + 1 = L.s ∧ (b : ℕ) = L.s + L.k)
  else (b : ℕ) = a + 1

def Lev.chi (L : Lev g N) (u : GG g N) : ℂ :=
  L.ψ (∑ a, ∑ b, if L.Edge a b then (L.co a : ZMod g) * u.val a b else 0)

def Lev.e (L : Lev g N) : GG g N → ℂ := eps L.Mem L.chi

def IsGeneric {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) : Prop :=
  ∃ L : Lev g N, L.sharp = false ∧ ∃ x : M, x ≠ 0 ∧ ∀ u, IsUp g N u → ρ u x = L.chi u • x

def IsSeries (τ : (ZMod g)[X] → GG g N → ℂ) : Prop :=
  Set.InjOn τ (sqSet g N : Set (ZMod g)[X]) ∧ ∀ f ∈ sqSet g N, ∃ V : FDRep ℂ (GG g N), CategoryTheory.Simple V ∧
    V.character = τ f ∧ IsGeneric V.ρ ∧
    Module.finrank ℂ V * torusCard g f = ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1)

def eGood {ι : Type} [Fintype ι] {m : ℕ} (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ) :
    (ι → GG g N) → ℂ :=
  ∑ F ∈ goodSet g N ch, tens fun v => zc (τ v (F v))

def AllUnip {ι : Type} (γ : ι → GG g N) : Prop := ∀ v, IsNilpotent ((γ v).val - 1)

def CountAt {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) (ep : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ e : (ι₁ → GG g₁ N) × (ι₂ → GG g₂ N) → ℂ, IsProj e →
    ((∀ γ, e γ ≠ 0 → AllUnip γ.1) ∨ ∀ γ, e γ ≠ 0 → AllUnip γ.2) →
    |(rk ρ e : ℝ) - c * (e 1).re| ≤ ep * (c * (e 1).re)

def PrimeOK (g q d : ℕ) : Prop :=
  q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1 ∧ 2 ^ 12 ≤ g

namespace Basic

theorem mem_one (L : Lev g N) : L.Mem 1 := by
  refine ⟨⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne']⟩, fun _ a b h1 h2 h3 => ?_⟩
  have : a ≠ b := by intro h; subst h; omega
  simp [Matrix.one_apply, this]

theorem mem_mul (L : Lev g N) {u w : GG g N} (hu : L.Mem u) (hw : L.Mem w) : L.Mem (u * w) := by
  have isUp_mul : ∀ {u w : GG g N}, IsUp g N u → IsUp g N w → IsUp g N (u * w) := by
    intro u w hu hw
    obtain ⟨hu1, hu0⟩ := hu
    obtain ⟨hw1, hw0⟩ := hw
    constructor
    · intro a
      rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
      · rw [hu1, hw1, one_mul]
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with h | h
        · rw [hu0 a c h, zero_mul]
        · rw [hw0 c a h, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ a) h
    · intro a b hab
      rw [Units.val_mul, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      rcases lt_or_ge c a with h | h
      · rw [hu0 a c h, zero_mul]
      · rw [hw0 c b (lt_of_lt_of_le hab h), mul_zero]
  obtain ⟨hu, hu'⟩ := hu
  obtain ⟨hw, hw'⟩ := hw
  refine ⟨isUp_mul hu hw, ?_⟩
  intro hs a b h1 h2 h3
  rw [Units.val_mul, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  rcases lt_or_ge c a with h | h
  · rw [hu.2 a c h, zero_mul]
  · rcases lt_trichotomy c b with h' | h' | h'
    · have hca : (a : ℕ) ≤ c := h
      have hcb : (c : ℕ) < b := h'
      rw [hw' hs c b (by omega) (by omega) h3, mul_zero]
    · subst h'
      rw [hu' hs a c h1 h2 h3, zero_mul]
    · rw [hw.2 c b h', mul_zero]

theorem entry_mul (L : Lev g N) {u w : GG g N} (hu : L.Mem u) (hw : L.Mem w) {a b : Fin N} (h : L.Edge a b) :
    (u * w).val a b = u.val a b + w.val a b := by
  obtain ⟨⟨u1, u2⟩, u3⟩ := hu
  obtain ⟨⟨w1, w2⟩, w3⟩ := hw
  have hab : (a : ℕ) < b := by
    unfold Lev.Edge at h
    split_ifs at h <;> omega
  have hne : b ≠ a := by intro h; subst h; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem b a (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [w1, u1, mul_one, one_mul]
  · intro c _ ⟨hcb, hca⟩
    rcases lt_or_gt_of_ne hca with h1 | h1
    · rw [u2 a c h1, zero_mul]
    · rcases lt_or_gt_of_ne hcb with h2 | h2
      · have h1' : (a : ℕ) < c := h1
        have h2' : (c : ℕ) < b := h2
        unfold Lev.Edge at h
        split_ifs at h with hs
        · rw [w3 hs c b (by omega) (by omega) (by omega), mul_zero]
        · omega
      · rw [w2 c b h2, mul_zero]

theorem chi_mul (L : Lev g N) {u w : GG g N} (hu : L.Mem u) (hw : L.Mem w) : L.chi (u * w) = L.chi u * L.chi w := by
  unfold Lev.chi
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [entry_mul L hu hw h, mul_add]
  · simp

theorem mem_inv (L : Lev g N) {u : GG g N} (hu : L.Mem u) : L.Mem u⁻¹ := by
  have hp : ∀ n : ℕ, L.Mem (u ^ n) := by
    intro n
    induction n with
    | zero => simpa using mem_one L
    | succ n ih => rw [pow_succ]; exact mem_mul L ih hu
  have : u⁻¹ = u ^ (orderOf u - 1) := by
    have h0 : 0 < orderOf u := orderOf_pos u
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
  rw [this]; exact hp _

theorem norm_chi (L : Lev g N) (u : GG g N) : ‖L.chi u‖ = 1 := AddChar.norm_apply _ _

theorem chi_ne (L : Lev g N) (u : GG g N) : L.chi u ≠ 0 := by
  intro h; have := norm_chi L u; rw [h] at this; simp at this

theorem chi_one (L : Lev g N) : L.chi 1 = 1 := by
  have := chi_mul L (mem_one L) (mem_one L)
  rw [mul_one] at this
  exact (mul_eq_left₀ (chi_ne L 1)).mp this.symm

theorem chi_inv (L : Lev g N) {u : GG g N} (hu : L.Mem u) : L.chi u⁻¹ = (L.chi u)⁻¹ := by
  have := chi_mul L hu (mem_inv L hu)
  rw [mul_inv_cancel, chi_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem isProj_e (L : Lev g N) : IsProj L.e := by
  haveI : Nonempty {u // L.Mem u} := ⟨⟨1, mem_one L⟩⟩
  have hc : (Nat.card {u // L.Mem u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  refine ⟨?_, fun x => ?_⟩
  · ext x
    simp only [conv, Lev.e, eps]
    by_cases hx : L.Mem x
    · rw [if_pos hx]
      have : ∀ y : GG g N, (if L.Mem y then (L.chi y)⁻¹ / (Nat.card {u // L.Mem u} : ℂ) else 0) *
          (if L.Mem (y⁻¹ * x) then (L.chi (y⁻¹ * x))⁻¹ / (Nat.card {u // L.Mem u} : ℂ) else 0) =
          if L.Mem y then (L.chi x)⁻¹ / (Nat.card {u // L.Mem u} : ℂ) / (Nat.card {u // L.Mem u} : ℂ) else 0 := by
        intro y
        by_cases hy : L.Mem y
        · rw [if_pos hy, if_pos hy, if_pos (mem_mul L (mem_inv L hy) hx), chi_mul L (mem_inv L hy) hx, chi_inv L hy]
          have := chi_ne L y
          have := chi_ne L x
          field_simp
        · simp [hy]
      rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      field_simp
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : L.Mem y
      · have : ¬ L.Mem (y⁻¹ * x) := fun h => hx (by simpa using mem_mul L hy h)
        simp [this]
      · simp [hy]
  · simp only [Lev.e, eps]
    by_cases hx : L.Mem x
    · rw [if_pos hx, if_pos (mem_inv L hx), chi_inv L hx, map_div₀, map_inv₀, ← Complex.inv_eq_conj (norm_chi L x)]
      simp
    · have : ¬ L.Mem x⁻¹ := fun h => hx (by simpa using mem_inv L h)
      simp [hx, this]

def levOfChar (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (N : ℕ) (b : Bool) (s k : ℕ) (h : s + k < N) : Lev g N :=
  ⟨b, s, k, h, ψ, hψ, fun _ => 1⟩

def levStandard (g : ℕ) [Fact g.Prime] (N : ℕ) (b : Bool) (s k : ℕ) (h : s + k < N) : Lev g N :=
  levOfChar ZMod.stdAddChar (fun h1 => by
    have h2 : (ZMod.stdAddChar (N := g)) 1 = ZMod.stdAddChar (N := g) 0 := by rw [h1]; simp
    exact one_ne_zero (ZMod.injective_stdAddChar h2)) N b s k h

theorem standard_edge_five (a b : Fin 5) : (levStandard g 5 true 1 2 (by norm_num)).Edge a b ↔
    (a, b) = (0, 3) ∨ (a, b) = (1, 2) ∨ (a, b) = (3, 4) := by
  simp only [Lev.Edge, levStandard, levOfChar, if_true]
  revert a b; decide

def transv (a b : Fin N) (h : a ≠ b) : GG g N :=
  ⟨Matrix.transvection a b 1, Matrix.transvection a b (-1),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

theorem transv_apply (a b : Fin N) (h : a ≠ b) (i j : Fin N) :
    (transv (g := g) a b h).val i j = (if i = j then 1 else 0) + (if a = i ∧ b = j then 1 else 0) := by
  simp [transv, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

theorem isUp_transv (a b : Fin N) (h : a < b) : IsUp g N (transv a b h.ne) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [transv_apply, if_pos rfl, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ h
  · rw [transv_apply, if_neg hij.ne', if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h hij

theorem standard_five_nontrivial :
    (∃ u, (levStandard g 5 true 1 2 (by norm_num)).Mem u ∧ (levStandard g 5 true 1 2 (by norm_num)).chi u ≠ 1) ∧
      ∃ u, IsUp g 5 u ∧ ¬ (levStandard g 5 true 1 2 (by norm_num)).Mem u := by
  refine ⟨⟨transv 0 3 (by decide), ⟨isUp_transv 0 3 (by decide), fun _ a b h1 h2 h3 => ?_⟩, ?_⟩,
    transv 1 3 (by decide), isUp_transv 1 3 (by decide), fun h => ?_⟩
  · simp only [levStandard, levOfChar] at h1 h2 h3
    rw [transv_apply, if_neg, if_neg, add_zero]
    · rintro ⟨rfl, rfl⟩
      simp at h1
    · rintro rfl
      omega
  · have hs : (∑ a, ∑ b, if (levStandard g 5 true 1 2 (by norm_num)).Edge a b then
        (((levStandard g 5 true 1 2 (by norm_num)).co a : (ZMod g)ˣ) : ZMod g) *
          (transv (g := g) (0 : Fin 5) 3 (by decide)).val a b else 0) = 1 := by
      simp only [standard_edge_five, transv_apply]
      simp [Fin.sum_univ_five, levStandard, levOfChar]
    unfold Lev.chi
    rw [hs]
    intro h
    exact one_ne_zero (((ZMod.isPrimitive_stdAddChar g).zmod_char_eq_one_iff g 1).1 h)
  · have := h.2 rfl 1 3 (by simp [levStandard, levOfChar]) (by simp [levStandard, levOfChar])
      (by simp [levStandard, levOfChar])
    rw [transv_apply] at this
    simp at this

def levGrp (L : Lev g N) : Subgroup (GG g N) where
  carrier := {u | L.Mem u}
  one_mem' := mem_one L
  mul_mem' := mem_mul L
  inv_mem' := mem_inv L

def levChiHom (L : Lev g N) : levGrp L →* ℂ where
  toFun u := L.chi u
  map_one' := chi_one L
  map_mul' u w := chi_mul L u.2 w.2

theorem primeOK_example : PrimeOK 6529 3 17 ∧ Nat.Prime 6529 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩

section Alg
variable {G : Type} [Group G] [Fintype G]

def alg (e : G → ℂ) : MonoidAlgebra ℂ G := ∑ γ, MonoidAlgebra.single γ (e γ)

theorem coeff_alg (e : G → ℂ) (x : G) : (alg e).coeff x = e x := by
  unfold alg
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem alg_coeff (a : MonoidAlgebra ℂ G) : alg (fun x => a.coeff x) = a := by
  ext x; exact coeff_alg _ x

theorem alg_injective : Function.Injective (alg : (G → ℂ) → MonoidAlgebra ℂ G) := fun a b h => by
  funext x; rw [← coeff_alg a, h, coeff_alg]

theorem coeff_mul_eq_conv (a b : MonoidAlgebra ℂ G) (x : G) :
    (a * b).coeff x = conv (fun y => a.coeff y) (fun y => b.coeff y) x := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  · rfl
  · simp

theorem alg_conv (a b : G → ℂ) : alg (conv a b) = alg a * alg b := by
  ext x
  rw [coeff_mul_eq_conv, coeff_alg]
  simp only [coeff_alg]

theorem alg_dirac : alg (dirac : G → ℂ) = 1 := by
  ext x
  rw [coeff_alg, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply, dirac]
  simp [eq_comm]

theorem op_eq_asAlgebraHom {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (e : G → ℂ) :
    op ρ e = ρ.asAlgebraHom (alg e) := by
  simp [op, alg, Representation.asAlgebraHom_single]

theorem asAlgebraHom_eq_op {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a : MonoidAlgebra ℂ G) :
    ρ.asAlgebraHom a = op ρ (fun x => a.coeff x) := by
  rw [op_eq_asAlgebraHom, alg_coeff]

theorem op_conv {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a b : G → ℂ) :
    op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op_eq_asAlgebraHom, alg_conv, map_mul]

theorem op_dirac {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) : op ρ dirac = 1 := by
  rw [op_eq_asAlgebraHom, alg_dirac, map_one]

theorem conv_assoc (a b c : G → ℂ) : conv (conv a b) c = conv a (conv b c) :=
  alg_injective (by simp only [alg_conv, mul_assoc])

end Alg

section Proj
variable {G : Type} [Group G] [Fintype G]

def adj (e : G → ℂ) : G → ℂ := fun x => (starRingEnd ℂ) (e x⁻¹)

omit [Fintype G] in

theorem adj_adj (e : G → ℂ) : adj (adj e) = e := by funext x; simp [adj]

theorem adj_conv (a b : G → ℂ) : adj (conv a b) = conv (adj b) (adj a) := by
  funext x
  simp only [adj, conv, map_sum, map_mul]
  rw [← Equiv.sum_comp (Equiv.mulLeft x⁻¹)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_comm, mul_assoc]

theorem eq_zero_of_conv_adj {a : G → ℂ} (h : conv a (adj a) = 0) : a = 0 := by
  have h1 := congrFun h 1
  simp only [conv, adj, mul_one, inv_inv, Complex.mul_conj, Pi.zero_apply] at h1
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun y _ => Complex.normSq_nonneg _] at h1
  funext y
  exact Complex.normSq_eq_zero.mp (h1 y (Finset.mem_univ _))

theorem alg_sub (a b : G → ℂ) : alg (a - b) = alg a - alg b := by
  ext x; simp [coeff_alg]

theorem isProj_of_central {e : G → ℂ} (he : conv e e = e) (hc : ∀ a, conv e a = conv a e) : IsProj e := by
  have ha : conv (adj e) (adj e) = adj e := by rw [← adj_conv, he]
  have hE : alg e * alg e = alg e := by rw [← alg_conv, he]
  have hA : alg (adj e) * alg (adj e) = alg (adj e) := by rw [← alg_conv, ha]
  have hC : alg (adj e) * alg e = alg e * alg (adj e) := by rw [← alg_conv, ← hc, alg_conv]
  have h1 : adj (conv e (adj e)) = conv e (adj e) := by rw [adj_conv, adj_adj]
  have h2 : adj (e - conv e (adj e)) = adj e - conv e (adj e) := by
    conv_rhs => rw [← h1]
    funext x; simp [adj]
  have h3 : e - conv e (adj e) = 0 := by
    refine eq_zero_of_conv_adj (alg_injective ?_)
    rw [h2, alg_conv, alg_sub, alg_sub, alg_conv, show alg (0 : G → ℂ) = 0 by simp [alg], sub_mul, mul_sub, mul_sub,
      ← mul_assoc, hE, mul_assoc, hA, mul_assoc, ← mul_assoc (alg (adj e)), hC, mul_assoc, hA, ← mul_assoc, hE]
    simp
  have h4 : adj e = e := by rw [sub_eq_zero.mp h3, h1]
  refine ⟨he, fun x => ?_⟩
  conv_lhs => rw [← h4]
  simp [adj]

theorem conv_tens {ι : Type} [Fintype ι] (a b : ι → G → ℂ) :
    conv (tens a) (tens b) = tens fun v => conv (a v) (b v) := by
  funext x
  simp only [conv, tens, Finset.prod_univ_sum, Fintype.piFinset_univ, ← Finset.prod_mul_distrib, Pi.mul_apply, Pi.inv_apply]

theorem conv_tens2 {G' : Type} [Group G'] [Fintype G'] (a a' : G → ℂ) (b b' : G' → ℂ) :
    conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b') := by
  funext x
  simp only [conv, tens2, Fintype.sum_prod_type, Finset.sum_mul_sum, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isProj_tens {ι : Type} [Fintype ι] {a : ι → G → ℂ} (h : ∀ v, IsProj (a v)) : IsProj (tens a) := by
  refine ⟨by rw [conv_tens]; simp only [fun v => (h v).1], fun x => ?_⟩
  simp only [tens, Pi.inv_apply, map_prod, fun v => (h v).2]

theorem isProj_tens2 {G' : Type} [Group G'] [Fintype G'] {a : G → ℂ} {b : G' → ℂ} (ha : IsProj a) (hb : IsProj b) :
    IsProj (tens2 a b) := by
  refine ⟨by rw [conv_tens2, ha.1, hb.1], fun x => ?_⟩
  simp only [tens2, Prod.fst_inv, Prod.snd_inv, map_mul, ha.2, hb.2]

theorem rk_eq_sum_trace {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M)
    {e : G → ℂ} (he : conv e e = e) : (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have hi : IsIdempotentElem (op ρ e) := by rw [IsIdempotentElem, ← op_conv, he]
  rw [rk, ← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace]
  simp [op]

end Proj

theorem countAt_of_trace_eq_zero {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
    (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M)
    (h : ∀ γ, γ ≠ 1 → AllUnip γ.1 ∨ AllUnip γ.2 → LinearMap.trace ℂ M (ρ γ) = 0) : CountAt ρ 0 := by
  refine ⟨Module.finrank ℂ M, by exact_mod_cast Module.finrank_pos, fun e he hu => ?_⟩
  have h1 := rk_eq_sum_trace ρ he.1
  rw [Finset.sum_eq_single 1, map_one, LinearMap.trace_one, mul_comm] at h1
  · have h2 := congrArg Complex.re h1
    rw [Complex.natCast_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at h2
    rw [h2]; simp
  · intro γ _ hγ
    by_cases h0 : e γ = 0
    · rw [h0, zero_mul]
    · rw [h γ hγ (hu.imp (fun H => H γ h0) fun H => H γ h0), mul_zero]
  · simp

section Reg
variable (G : Type) [Group G] [Fintype G]

def regFn : Representation ℂ G (G → ℂ) where
  toFun γ := LinearMap.funLeft ℂ ℂ (fun x => γ⁻¹ * x)
  map_one' := by ext f x; simp [LinearMap.funLeft_apply]
  map_mul' a b := by ext f x; simp [LinearMap.funLeft_apply, mul_assoc]

variable {G}

theorem op_reg (e f : G → ℂ) : op (regFn G) e f = conv e f := by
  ext x
  simp [op, regFn, conv, LinearMap.sum_apply, LinearMap.funLeft_apply]

theorem trace_op_reg (e : G → ℂ) : LinearMap.trace ℂ _ (op (regFn G) e) = Fintype.card G * e 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace]
  have : ∀ x : G, Matrix.diag (LinearMap.toMatrix (Pi.basisFun ℂ G) (Pi.basisFun ℂ G) (op (regFn G) e)) x = e 1 := by
    intro x
    simp only [Matrix.diag, LinearMap.toMatrix_apply, op_reg, Pi.basisFun_apply, Pi.basisFun_repr, conv]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro y _ hy
      rw [Pi.single_eq_of_ne, mul_zero]
      simpa using hy
    · simp
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp

theorem rk_reg (e : G → ℂ) (he : conv e e = e) : (rk (regFn G) e : ℂ) = Fintype.card G * e 1 := by
  have hi : IsIdempotentElem (op (regFn G) e) := by
    refine LinearMap.ext fun f => ?_
    rw [Module.End.mul_apply, op_reg, op_reg, ← conv_assoc, he]
  rw [← trace_op_reg]
  exact ((LinearMap.IsIdempotentElem.isProj_range _ hi).trace).symm

end Reg

theorem countAt_reg {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] :
    CountAt (regFn ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N))) 0 := by
  refine ⟨Fintype.card ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)), by exact_mod_cast Fintype.card_pos, fun e he _ => ?_⟩
  have h := congrArg Complex.re (rk_reg e he.1)
  rw [Complex.natCast_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at h
  rw [h]
  simp

theorem isProj_dirac {G : Type} [Group G] [Fintype G] : IsProj (dirac : G → ℂ) := by
  refine ⟨?_, fun x => ?_⟩
  · ext x
    rw [conv, Finset.sum_eq_single 1]
    · simp [dirac]
    · intro y _ hy; simp [dirac, hy]
    · simp
  · by_cases h : x = 1 <;> simp [dirac, h]

theorem finrank_pos_of_countAt {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) {ep : ℝ}
    (hep : ep < 1) (h : CountAt ρ ep) : 0 < Module.finrank ℂ M := by
  obtain ⟨c, hc, h⟩ := h
  have h1 := h dirac isProj_dirac (Or.inl fun γ hγ v => by
    have : γ = 1 := by by_contra h'; simp [dirac, h'] at hγ
    subst this
    simp)
  have h2 : op ρ dirac = 1 := by simp [op, dirac]
  have h3 : rk ρ dirac = Module.finrank ℂ M := by
    rw [rk, h2, Module.End.one_eq_id, LinearMap.range_id, finrank_top]
  rw [h3] at h1
  simp only [dirac, if_true, Complex.one_re, mul_one] at h1
  by_contra h0
  have : Module.finrank ℂ M = 0 := by omega
  rw [this, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hc] at h1
  nlinarith

theorem not_isSeries_zero (τ : (ZMod g)[X] → GG g 0 → ℂ) : ¬ IsSeries τ := by
  rintro ⟨-, h⟩
  obtain ⟨V, -, -, ⟨L, -⟩, -⟩ := h 1 (by simp [sqSet])
  exact absurd L.hk (by omega)

def lineRep (χ : (ZMod g)ˣ →* ℂˣ) : Representation ℂ (GG g N) ℂ where
  toFun γ := ((χ (Matrix.GeneralLinearGroup.det γ) : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_comm]

theorem char_lineRep (χ : (ZMod g)ˣ →* ℂˣ) (γ : GG g N) :
    (FDRep.of (lineRep χ)).character γ = ((χ (Matrix.GeneralLinearGroup.det γ) : ℂˣ) : ℂ) := by
  change LinearMap.trace ℂ ℂ (((χ (Matrix.GeneralLinearGroup.det γ) : ℂˣ) : ℂ) • LinearMap.id) = _
  simp

theorem mem_sqSet_one {f : (ZMod g)[X]} (hf : f ∈ sqSet g 1) : f = X + C (f.coeff 0) ∧ f.coeff 0 ≠ 0 := by
  simp only [sqSet, Finset.mem_filter, Finset.mem_image] at hf
  obtain ⟨⟨c, -, rfl⟩, -, h⟩ := hf
  exact ⟨by simp, h⟩

theorem exists_isSeries_one : ∃ τ : (ZMod g)[X] → GG g 1 → ℂ, IsSeries τ := by
  obtain ⟨φ⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (ZMod g)ˣ ℂ
  let u : (ZMod g)[X] → (ZMod g)ˣ := fun f => if h : f.coeff 0 = 0 then 1 else Units.mk0 _ h
  refine ⟨fun f => (FDRep.of (lineRep (φ.symm (u f)))).character, ?_, fun f hf => ?_⟩
  · intro f hf f' hf' h
    obtain ⟨e1, n1⟩ := mem_sqSet_one hf
    obtain ⟨e2, n2⟩ := mem_sqSet_one hf'
    have h1 : φ.symm (u f) = φ.symm (u f') := by
      ext a
      have := congrFun h (Matrix.GeneralLinearGroup.scalar (Fin 1) a)
      simpa [char_lineRep] using this
    have h2 := congrArg Units.val (φ.symm.injective h1)
    simp only [u, n1, n2, dif_neg, not_false_eq_true, Units.val_mk0] at h2
    rw [e1, e2, h2]
  · refine ⟨FDRep.of (lineRep (φ.symm (u f))), ?_, rfl, ?_, ?_⟩
    · rw [FDRep.simple_iff_char_is_norm_one]
      simp [char_lineRep]
    · refine ⟨levStandard g 1 false 0 0 (by norm_num), rfl, (1 : ℂ), one_ne_zero, fun w hw => ?_⟩
      have : w = 1 := by
        ext a b
        rw [Subsingleton.elim b a, hw.1]; simp
      subst this
      rw [chi_one]; simp
    · obtain ⟨e1, n1⟩ := mem_sqSet_one hf
      have hi : UniqueFactorizationMonoid.normalizedFactors (X + C (f.coeff 0) : (ZMod g)[X]) = {X + C (f.coeff 0)} := by
        have hm : (X + C (f.coeff 0) : (ZMod g)[X]).Monic := monic_X_add_C _
        rw [UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_of_degree_eq_one (degree_X_add_C _)),
          hm.normalize_eq_self]
      have h1 : Module.finrank ℂ (FDRep.of (lineRep (N := 1) (φ.symm (u f)))) = 1 := Module.finrank_self ℂ
      rw [h1, torusCard, degType, e1, hi]
      simp

theorem isNilpotent_of_isUp {u : GG g N} (hu : IsUp g N u) : IsNilpotent (u.val - 1) := by
  have ht : (u.val - 1).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp [hu.2 a b h', h'.ne']
  have hc := Matrix.charpoly_of_upperTriangular _ ht
  have h0 := Matrix.aeval_self_charpoly (u.val - 1)
  rw [hc] at h0
  refine ⟨N, ?_⟩
  simpa [hu.1] using h0

theorem allUnip_of_tens_e {ι : Type} [Fintype ι] (L : ι → Lev g N) (γ : ι → GG g N)
    (h : tens (fun v => (L v).e) γ ≠ 0) : AllUnip γ := by
  intro v
  have h1 : (L v).e (γ v) ≠ 0 := (Finset.prod_ne_zero_iff.mp h) v (Finset.mem_univ _)
  by_contra h2
  exact h1 (if_neg fun hm => h2 (isNilpotent_of_isUp hm.1))

end Basic

end GlobalTheory.BadShare
