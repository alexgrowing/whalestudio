import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelDatumSubgroupCharacterPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShapeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialEqOfUpperUnipotentDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatumStatement

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.FirstRows

theorem inv_mem_of_mul_mem {G : Type} [Group G] [Finite G] (S : G → Prop) (h1 : S 1)
    (hm : ∀ u v, S u → S v → S (u * v)) (u : G) (hu : S u) : S u⁻¹ := by
  have hp : ∀ n : ℕ, S (u ^ n) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hm _ _ ih hu
  have : u⁻¹ = u ^ (orderOf u - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
  rw [this]; exact hp _

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def InBlock (k : ℕ) (h : GG g N) : Prop :=
  ∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → h.val a b = if a = b then 1 else 0

theorem inBlock_one (k : ℕ) : InBlock k (1 : GG g N) := by
  intro a b _
  simp [Matrix.one_apply]

theorem InBlock.mul_right {k : ℕ} {h : GG g N} (hh : InBlock k h) (A : Matrix (Fin N) (Fin N) (ZMod g))
    (a b : Fin N) (hb : k ≤ (b : ℕ)) : (A * h.val) a b = A a b := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [hh c b (Or.inr hb)]]
  simp

theorem InBlock.mul_left {k : ℕ} {h : GG g N} (hh : InBlock k h) (A : Matrix (Fin N) (Fin N) (ZMod g))
    (a b : Fin N) (ha : k ≤ (a : ℕ)) : (h.val * A) a b = A a b := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [hh a c (Or.inl ha)]]
  simp

theorem InBlock.mul {k : ℕ} (h h' : GG g N) (hh : InBlock k h) (hh' : InBlock k h') : InBlock k (h * h') := by
  intro a b hab
  rw [Units.val_mul]
  rcases hab with ha | hb
  · rw [hh.mul_left _ _ _ ha]; exact hh' a b (Or.inl ha)
  · rw [hh'.mul_right _ _ _ hb]; exact hh a b (Or.inr hb)

theorem InBlock.inv {k : ℕ} {h : GG g N} (hh : InBlock k h) : InBlock k h⁻¹ :=
  inv_mem_of_mul_mem _ (inBlock_one k) InBlock.mul h hh

theorem conj_entry {k : ℕ} {h n : GG g N} (hh : InBlock k h)
    (hn : ∀ a b : Fin N, (b : ℕ) ≤ k → n.val a b = if a = b then 1 else 0)
    (a b : Fin N) (hab : (b : ℕ) ≤ k ∨ k ≤ (a : ℕ)) : (h⁻¹ * (n * h)).val a b = n.val a b := by
  by_cases hb : (b : ℕ) ≤ k
  · have h1 : ∀ a, (n.val * h.val) a b = h.val a b := by
      intro a
      have : ∀ c, n.val a c * h.val c b = (if a = c then 1 else 0) * h.val c b := by
        intro c
        by_cases hc : (c : ℕ) ≤ k
        · rw [hn a c hc]
        · have : c ≠ b := by rintro rfl; exact hc hb
          rw [hh c b (Or.inl (by omega)), if_neg this, mul_zero, mul_zero]
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => this c]
      simp
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [h1 c],
      ← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, hn a b hb]
    simp [Matrix.one_apply]
  · have ha : k ≤ (a : ℕ) := by omega
    rw [Units.val_mul, Units.val_mul, hh.inv.mul_left _ _ _ ha, hh.mul_right _ _ _ (by omega)]

theorem exists_block {k : ℕ} {j : GG g N} (hj : IsUp g N j)
    (hk : ∀ a b : Fin N, (a : ℕ) < k → (b : ℕ) = k → j.val a b = 0) :
    ∃ u : GG g N, IsUp g N u ∧ InBlock k u ∧
      ∀ a b : Fin N, (b : ℕ) ≤ k → (u⁻¹ * j).val a b = if a = b then 1 else 0 := by
  let A : Matrix (Fin N) (Fin N) (ZMod g) := fun a b =>
    if (a : ℕ) < k ∧ (b : ℕ) < k then j.val a b else if a = b then 1 else 0
  have hd : ∀ a, A a a = 1 := by
    intro a; simp [A, hj.1]
  have hl : ∀ a b, b < a → A a b = 0 := by
    intro a b hab; simp [A, hj.2 a b hab, hab.ne']
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun a b hab => hl a b hab)]
    simp [hd]
  let u : GG g N := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet
  have hu : u.val = A := rfl
  refine ⟨u, ⟨hd, hl⟩, ?_, ?_⟩
  · intro a b hab
    rw [hu]
    exact if_neg (by omega)
  · intro a b hb
    have h1 : ∀ c, j.val c b = u.val c b := by
      intro c
      rw [hu]
      simp only [A]
      split_ifs with h1 h2
      · rfl
      · subst h2; exact hj.1 _
      · rcases lt_or_gt_of_ne h2 with h | h
        · have : (c : ℕ) < b := h
          exact hk c b (by omega) (by omega)
        · exact hj.2 _ _ h
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_congr rfl fun c _ => by rw [h1 c],
      ← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel]
    simp [Matrix.one_apply]

theorem mem_iff_isUp {L : Lev g N} (hL : L.sharp = false) (u : GG g N) : L.Mem u ↔ IsUp g N u := by
  simp [Lev.Mem, hL]

theorem chi_congr {L : Lev g N} (hL : L.sharp = false) {u v : GG g N}
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → u.val a b = v.val a b) : L.chi u = L.chi v := by
  unfold Lev.chi
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with he
  · rw [h a b (by simpa [Lev.Edge, hL] using he)]
  · rfl

theorem chi_ne_zero (L : Lev g N) (u : GG g N) : L.chi u ≠ 0 := by
  intro h
  unfold Lev.chi at h
  have := AddChar.map_add_eq_mul L.ψ (∑ a, ∑ b, if L.Edge a b then (L.co a : ZMod g) * u.val a b else 0)
    (-(∑ a, ∑ b, if L.Edge a b then (L.co a : ZMod g) * u.val a b else 0))
  rw [h] at this
  simp at this

def blockUp (g : ℕ) [Fact g.Prime] (N k : ℕ) : Finset (GG g N) :=
  Finset.univ.filter fun u => IsUp g N u ∧ InBlock k u

theorem mem_blockUp {k : ℕ} {u : GG g N} : u ∈ blockUp g N k ↔ IsUp g N u ∧ InBlock k u := by
  simp [blockUp]

variable {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M)

def avg (L : Lev g N) (k : ℕ) (x : M) (w : GG g N) : M :=
  ∑ u ∈ blockUp g N k, (L.chi u)⁻¹ • ρ (u * w) x

theorem avg_eigen {L : Lev g N} (hL : L.sharp = false) {x : M} (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x)
    {k : ℕ} {w : GG g N} (hw : InBlock k w) {j : GG g N} (hj : IsUp g N j)
    (hk : ∀ a b : Fin N, (a : ℕ) < k → (b : ℕ) = k → j.val a b = 0) :
    ρ j (avg ρ L k x w) = L.chi j • avg ρ L k x w := by
  obtain ⟨h1, hm, -, hc, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  simp only [mem_iff_isUp hL] at h1 hm hc
  have hi := inv_mem_of_mul_mem _ h1 hm
  obtain ⟨u, hu, hub, hn⟩ := exists_block hj hk
  have hnu : IsUp g N (u⁻¹ * j) := hm _ _ (hi _ hu) hj
  obtain ⟨n, rfl⟩ : ∃ n, j = u * n := ⟨u⁻¹ * j, by simp⟩
  rw [inv_mul_cancel_left] at hn hnu
  have e1 : ρ n (avg ρ L k x w) = L.chi n • avg ρ L k x w := by
    unfold avg
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hh : InBlock k (v * w) := InBlock.mul _ _ (mem_blockUp.1 hv).2 hw
    generalize v * w = h at hh
    have hc' := conj_entry hh hn
    have hup : IsUp g N (h⁻¹ * (n * h)) :=
      ⟨fun a => by rw [hc' a a (by omega)]; exact hnu.1 a,
        fun a b hab => by
          have : (b : ℕ) < a := hab
          rw [hc' a b (by omega)]; exact hnu.2 a b hab⟩
    have hchi : L.chi (h⁻¹ * (n * h)) = L.chi n := chi_congr hL fun a b hab => hc' a b (by omega)
    have : ρ n (ρ h x) = ρ h (ρ (h⁻¹ * (n * h)) x) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
    rw [map_smul, this, hx _ hup, hchi, map_smul, smul_comm]
  have e2 : ρ u (avg ρ L k x w) = L.chi u • avg ρ L k x w := by
    unfold avg
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_bijective (fun v => u * v) (Group.mulLeft_bijective u) ?_ ?_
    · intro v
      simp only [mem_blockUp]
      refine ⟨fun h => ⟨hm _ _ hu h.1, InBlock.mul _ _ hub h.2⟩, fun h => ?_⟩
      have := And.intro (hm _ _ (hi _ hu) h.1) (InBlock.mul _ _ hub.inv h.2)
      rwa [inv_mul_cancel_left] at this
    · intro v hv
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_assoc, hc _ _ hu (mem_blockUp.1 hv).1, smul_smul,
        mul_inv, mul_inv_cancel_left₀ (chi_ne_zero L u)]
  rw [map_mul, Module.End.mul_apply, e1, map_smul, e2, smul_smul, hc _ _ hu hnu, mul_comm]

theorem avg_independent [FiniteDimensional ℂ M] {L : Lev g N} (hL : L.sharp = false) {x : M} (hx0 : x ≠ 0)
    (hx : ∀ u, IsUp g N u → ρ u x = L.chi u • x) {k : ℕ} (hk : k < N) (R : Finset (GG g N))
    (hR : ∀ w ∈ R, InBlock k w ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b)
    (hχ : ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → InBlock k u → InBlock k u' →
      u * w = w * u' → L.chi u = L.chi u') :
    LinearIndependent ℂ fun w : R => avg ρ L k x w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc w₀
  let φ : GG g N → ℂ := fun h =>
    ∑ w : R, ∑ u ∈ blockUp g N k, if h = u * w then c w * (L.chi u)⁻¹ else 0
  have hφ : ∀ h, φ h ≠ 0 → InBlock k h := by
    intro h hh
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
    obtain ⟨u, hu, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have : h = u * w := by by_contra hne; exact hw (if_neg hne)
    rw [this]
    exact InBlock.mul _ _ (mem_blockUp.1 hu).2 (hR w w.2).1
  have hsum : ∑ h, φ h • ρ h x = 0 := by
    rw [← hc]
    simp only [φ, avg, Finset.sum_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [ite_smul, mul_smul]
  have key : ∑ u' ∈ blockUp g N k, φ (w₀ * u') * L.chi u' = 0 := by
    refine Eq.trans (Finset.sum_congr ?_ fun _ _ => rfl)
      (GlobalTheory.T.whittaker_translates_corner_linearIndependent g N M ρ L hL x hx0 hx k hk φ hφ hsum w₀)
    ext u
    simp only [mem_blockUp, Finset.mem_filter, Finset.mem_univ, true_and, InBlock]
  have h2 : ∀ u' ∈ blockUp g N k, φ (w₀ * u') * L.chi u' =
      c w₀ * ((((blockUp g N k).filter fun u => w₀ * u' = u * w₀).card : ℕ) : ℂ) := by
    intro u' hu'
    have hu' := mem_blockUp.1 hu'
    simp only [φ]
    rw [Finset.sum_eq_single w₀, Finset.card_filter, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun u hu => ?_
      have hu := mem_blockUp.1 hu
      split_ifs with h
      · rw [hχ w₀ w₀.2 u u' hu.1 hu'.1 hu.2 hu'.2 h.symm, mul_assoc, inv_mul_cancel₀ (chi_ne_zero L u')]
        simp
      · simp
    · intro w _ hw
      refine Finset.sum_eq_zero fun u hu => if_neg fun h => hw (Subtype.ext ?_)
      exact GlobalTheory.T.monomial_eq_of_upperUnipotent_double_coset g N w w₀ u u' (hR w w.2).2 (hR w₀ w₀.2).2 (mem_blockUp.1 hu).1 hu'.1 h.symm
    · simp
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Nat.cast_sum, mul_eq_zero] at key
  refine key.resolve_right ?_
  have h1 : (1 : GG g N) ∈ blockUp g N k :=
    mem_blockUp.2 ⟨(mem_iff_isUp hL 1).1 (GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L).1, inBlock_one k⟩
  rw [Nat.cast_eq_zero, Finset.sum_eq_zero_iff]
  intro h
  have := h 1 h1
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
  exact this h1 (by simp)

theorem card_le_rk [FiniteDimensional ℂ M] (L : Lev g N) {ι : Type} [Fintype ι] (x : ι → M)
    (hx : LinearIndependent ℂ x) (he : ∀ i u, L.Mem u → ρ u (x i) = L.chi u • x i) :
    Fintype.card ι ≤ rk ρ L.e := by
  obtain ⟨h1, hm, hc1, hc, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  exact (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L.Mem L.chi h1 hm hc1 hc).2.2.2 _ (x ∘ (Fintype.equivFin ι).symm)
    (hx.comp _ (Fintype.equivFin ι).symm.injective) fun i => he _

theorem exists_unit_coeff [FiniteDimensional ℂ M] (hρ : IsGeneric ρ) :
    ∃ L : Lev g N, L.sharp = false ∧ (∀ a, L.co a = 1) ∧
      ∃ x : M, x ≠ 0 ∧ ∀ u, IsUp g N u → ρ u x = L.chi u • x := by
  obtain ⟨L, hL, x, hx0, hx⟩ := hρ
  let L₁ : Lev g N := { L with co := fun _ => 1 }
  have hL₁ : L₁.sharp = false := hL
  refine ⟨L₁, hL₁, fun _ => rfl, ?_⟩
  have h1 := card_le_rk ρ L (fun _ : Unit => x) (linearIndependent_unique_iff.2 hx0)
    fun _ u hu => hx u hu.1
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L₁ rfl rfl rfl, Fintype.card_unit] at h1
  obtain ⟨⟨y, hy⟩, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h1
  obtain ⟨h1, hm, hc1, hc, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L₁
  refine ⟨y, fun h => hy0 (Subtype.ext h), fun u hu => ?_⟩
  exact ((GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) M ρ L₁.Mem L₁.chi h1 hm hc1 hc).2.2.1 y).1 hy u ((mem_iff_isUp hL₁ u).2 hu)

end GlobalTheory.BadShare.FirstRows

namespace GlobalTheory.BadShare
open FirstRows

theorem rk_ge_of_isGeneric_of_s_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, L.sharp = true → L.s = 0 →
    (1 - 1 / (g : ℝ)) * (g : ℝ) ^ L.k ≤ (rk ρ L.e : ℝ) := by
  intro g hg N M _ _ _ ρ hρ L hL hs
  obtain ⟨L₁, hL₁, hco, x, hx0, hx⟩ := exists_unit_coeff ρ hρ
  let L' : Lev g N := { L with ψ := L₁.ψ, hψ := L₁.hψ, co := L₁.co }
  have hkN : L.k < N := by have := L.hk; omega
  have hmem : ∀ u, L'.Mem u → ∀ a b : Fin N, (a : ℕ) < L.k → (b : ℕ) = L.k → u.val a b = 0 := by
    intro u hu a b ha hb
    exact hu.2 hL a b (by simp [L', hs]) (by simpa [L', hs] using ha) (by simpa [L', hs] using hb)
  have hchi : ∀ u, L'.Mem u → L'.chi u = L₁.chi u := by
    intro u hu
    unfold Lev.chi
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 : L'.Edge a b ↔ ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L.k) := by
      simp only [Lev.Edge, L', hL, hs, if_true]
      omega
    have e2 : L₁.Edge a b ↔ (b : ℕ) = a + 1 := by simp [Lev.Edge, hL₁]
    by_cases h1 : (b : ℕ) = a + 1
    · rw [if_pos (e2.2 h1)]
      by_cases h2 : (a : ℕ) + 1 = L.k
      · rw [if_neg (fun h => (e1.1 h).2 h2), hmem u hu a b (by omega) (by omega), mul_zero]
      · rw [if_pos (e1.2 ⟨h1, h2⟩)]
    · rw [if_neg (fun h => h1 (e1.1 h).1), if_neg (fun h => h1 (e2.1 h))]
  rw [GlobalTheory.T.rank_levelDatum_idempotent_eq_of_same_shape g N M ρ L L' rfl rfl rfl]
  have hg0 : (0 : ℝ) < g := Nat.cast_pos.2 hg.out.pos
  rcases Nat.eq_zero_or_pos L.k with hk | hk
  · have h1 := card_le_rk ρ L' (fun _ : Unit => x) (linearIndependent_unique_iff.2 hx0)
      fun _ u hu => by rw [hchi u hu]; exact hx u hu.1
    rw [Fintype.card_unit] at h1
    have h1 : (1 : ℝ) ≤ rk ρ L'.e := by exact_mod_cast h1
    have : 0 < 1 / (g : ℝ) := by positivity
    rw [hk, pow_zero]
    linarith
  · obtain ⟨R, hcard, hR, hχ⟩ := GlobalTheory.T.exists_relevant_bruhat_cells_levelDatum g N L₁ hL₁ hco L.k hk hkN
    have h1 := card_le_rk ρ L' _ (avg_independent ρ hL₁ hx0 hx hkN R hR hχ) fun w u hu => by
      rw [hchi u hu]; exact avg_eigen ρ hL₁ hx (hR w w.2).1 hu.1 (hmem u hu)
    rw [Fintype.card_coe] at h1
    have h2 : (((g - 1) * g ^ (L.k - 1) : ℕ) : ℝ) ≤ rk ρ L'.e := by exact_mod_cast hcard.trans h1
    rw [Nat.cast_mul, Nat.cast_sub hg.out.pos, Nat.cast_pow, Nat.cast_one] at h2
    refine le_of_eq_of_le ?_ h2
    obtain ⟨m, hm⟩ : ∃ m, L.k = m + 1 := ⟨L.k - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    field_simp

end GlobalTheory.BadShare
