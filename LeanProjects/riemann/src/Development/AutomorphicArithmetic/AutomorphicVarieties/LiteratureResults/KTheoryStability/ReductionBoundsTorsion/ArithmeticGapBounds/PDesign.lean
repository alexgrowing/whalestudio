import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

noncomputable section

open scoped BigOperators

namespace PositivityTheory.KB.SpectralGap.DesignMultiplication

open Finset

private theorem core_lemma {G : Type*} [Group G] [Fintype G] (E : Subgroup G) (f : G → ℝ)
    (hf : ∀ e ∈ E, ∀ k, f (e * k) = f k) (x e e' : G) (he : e ∈ E) (he' : e' ∈ E) :
    ∑ k, f (e * x * e' * k) * f k = ∑ k, f (x * k) * f k := by
  have h1 : ∀ k, f (e * x * e' * k) = f (x * (e' * k)) := by
    intro k
    rw [show e * x * e' * k = e * (x * (e' * k)) by group]
    exact hf e he _
  simp_rw [h1]
  calc ∑ k, f (x * (e' * k)) * f k = ∑ k, f (x * (e' * k)) * f (e' * k) :=
        Finset.sum_congr rfl fun k _ => by rw [hf e' he' k]
    _ = ∑ m, f (x * m) * f m :=
        Fintype.sum_equiv (Equiv.mulLeft e') _ _ (fun k => rfl)

theorem core {G : Type*} [Group G] [Fintype G] (E E' : Subgroup G)
    (htt : ∀ g, g ∉ E → ∀ g', g' ∉ E → ∃ e ∈ E, ∃ e' ∈ E, g' = e * g * e')
    (f g : G → ℝ) (hf : ∀ e ∈ E, ∀ k, f (e * k) = f k) (hg : ∀ e ∈ E', ∀ k, g (e * k) = g k)
    (h0 : ∑ k, f k = 0) :
    (∑ k, f k * g k) ^ 2 * ((E.subgroupOf E').index : ℝ) ≤ (∑ k, f k ^ 2) * ∑ k, g k ^ 2 := by
  classical
  set c : G → ℝ := fun x => ∑ k, f (x * k) * f k with hc
  have cE : ∀ x ∈ E, c x = ∑ k, f k ^ 2 := by
    intro x hx
    simp only [hc]
    exact Finset.sum_congr rfl fun k _ => by rw [hf x hx k, sq]
  have csum : ∑ x, c x = 0 := by
    simp only [hc]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ x, f (x * k) = ∑ x, f x := Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun _ => rfl)
    rw [this, h0, zero_mul]
  have cinv : ∀ x e e', e ∈ E → e' ∈ E → c (e * x * e') = c x := fun x e e' he he' =>
    core_lemma E f hf x e e' he he'
  have cneg : ∀ x, x ∉ E → c x ≤ 0 := by
    intro x hx
    have split := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => y ∈ E) c)
    rw [csum] at split
    have hpos : 0 ≤ ∑ y ∈ Finset.univ.filter (fun y => y ∈ E), c y :=
      Finset.sum_nonneg fun y hy => by
        rw [cE y (Finset.mem_filter.1 hy).2]
        exact Finset.sum_nonneg fun k _ => sq_nonneg _
    have hconst : ∀ y ∈ Finset.univ.filter (fun y => y ∉ E), c y = c x := by
      intro y hy
      obtain ⟨e, he, e', he', rfl⟩ := htt x hx y (Finset.mem_filter.1 hy).2
      exact cinv x e e' he he'
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at split
    have hcard : (0:ℝ) < ((Finset.univ.filter (fun y => y ∉ E)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩
    nlinarith
  have key1 : ∀ a : E', ∑ k, f (a * k) * g k = ∑ k, f k * g k := by
    intro a
    refine Fintype.sum_equiv (Equiv.mulLeft (a : G)) _ _ (fun k => ?_)
    show f ((a : G) * k) * g k = f ((a : G) * k) * g ((a : G) * k)
    rw [hg _ a.2 k]
  set n' : ℝ := (Fintype.card E' : ℝ) with hn'
  set F : G → ℝ := fun k => ∑ a : E', f (a * k) with hF
  have hFg : n' * ∑ k, f k * g k = ∑ k, F k * g k := by
    simp only [hF, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [key1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn']
  have hpair : ∀ a b : E', ∑ k, f (a * k) * f (b * k) = c ((a : G) * (b : G)⁻¹) := by
    intro a b
    refine Fintype.sum_equiv (Equiv.mulLeft (b : G)) _ _ (fun k => ?_)
    show f ((a : G) * k) * f ((b : G) * k) = f ((a : G) * (b : G)⁻¹ * ((b : G) * k)) * f ((b : G) * k)
    rw [show (a : G) * (b : G)⁻¹ * ((b : G) * k) = (a : G) * k by group]
  have hF2 : ∑ k, F k ^ 2 = n' * ∑ a : E', c a := by
    calc ∑ k, F k ^ 2 = ∑ a : E', ∑ b : E', ∑ k, f (a * k) * f (b * k) := by
          simp only [hF, sq, Finset.sum_mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a : E', ∑ b : E', c ((a : G) * (b : G)⁻¹) := by simp only [hpair]
      _ = ∑ b : E', ∑ a : E', c ((a : G) * (b : G)⁻¹) := Finset.sum_comm
      _ = ∑ b : E', ∑ a : E', c a := by
          refine Finset.sum_congr rfl fun b _ => ?_
          exact Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ (fun a => rfl)
      _ = n' * ∑ a : E', c a := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn']
  set m : ℝ := ((Finset.univ.filter (fun a : E' => (a : G) ∈ E)).card : ℝ) with hm
  have hcE' : ∑ a : E', c a ≤ m * ∑ k, f k ^ 2 := by
    calc ∑ a : E', c a ≤ ∑ a : E', (if (a : G) ∈ E then ∑ k, f k ^ 2 else 0) :=
          Finset.sum_le_sum fun a _ => by
            split_ifs with h
            · exact (cE _ h).le
            · exact cneg _ h
      _ = m * ∑ k, f k ^ 2 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hidx : ((E.subgroupOf E').index : ℝ) * m = n' := by
    have h1 := Subgroup.card_mul_index (E.subgroupOf E')
    have h2 : Nat.card (E.subgroupOf E') = (Finset.univ.filter (fun a : E' => (a : G) ∈ E)).card := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => Subgroup.mem_subgroupOf))
    rw [h2, Nat.card_eq_fintype_card] at h1
    rw [hm, hn', ← h1]
    push_cast
    ring
  have hn0 : 0 < n' := by
    rw [hn']
    exact_mod_cast Fintype.card_pos
  have hm0 : 0 < m := by
    rw [hm]
    have h1 : (1 : E') ∈ Finset.univ.filter (fun a : E' => (a : G) ∈ E) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, E.one_mem⟩
    exact_mod_cast Finset.card_pos.2 ⟨1, h1⟩
  have CS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F g
  rw [← hFg, hF2] at CS
  have hB : 0 ≤ ∑ k, g k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h3 : n' * (n' * (∑ k, f k * g k) ^ 2) ≤ n' * (m * (∑ k, f k ^ 2) * ∑ k, g k ^ 2) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcE' hn0.le) hB
    nlinarith
  have h4 := le_of_mul_le_mul_left h3 hn0
  rw [← hidx] at h4
  have h5 : m * ((∑ k, f k * g k) ^ 2 * ((E.subgroupOf E').index : ℝ)) ≤ m * ((∑ k, f k ^ 2) * ∑ k, g k ^ 2) := by
    nlinarith
  exact le_of_mul_le_mul_left h5 hm0

theorem out_mk {Γ : Type*} [Group Γ] (N H : Subgroup Γ) [N.Normal] (hNH : N ≤ H) (φ : Γ → ℝ)
    (hφ : ∀ h ∈ H, ∀ k, φ (h * k) = φ k) (k : Γ) : φ ((k : Γ ⧸ N).out) = φ k := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N k
  rw [hn]
  have e : k * (n : Γ) = (k * n * k⁻¹) * k := by group
  rw [e, hφ _ (hNH (Subgroup.Normal.conj_mem ‹_› _ n.2 k))]

theorem rel_out {Γ : Type*} [Group Γ] (H : Subgroup Γ) (φ : Γ → ℝ)
    (hφ : ∀ h ∈ H, ∀ k, φ (h * k) = φ k) (y : Γ) :
    φ (Quotient.mk (QuotientGroup.rightRel H) y).out = φ y := by
  have h1 : y * ((Quotient.mk (QuotientGroup.rightRel H) y).out)⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel H) y)
  have e : (Quotient.mk (QuotientGroup.rightRel H) y).out
      = (y * ((Quotient.mk (QuotientGroup.rightRel H) y).out)⁻¹)⁻¹ * y := by group
  rw [e, hφ _ (H.inv_mem h1)]

def rmul {Γ : Type*} [Group Γ] (H : Subgroup Γ) (k : Γ) :
    Quotient (QuotientGroup.rightRel H) ≃ Quotient (QuotientGroup.rightRel H) where
  toFun := Quotient.map' (· * k) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    convert hab using 1; group)
  invFun := Quotient.map' (· * k⁻¹) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    convert hab using 1; group)
  left_inv := fun c => by
    induction c using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv := fun c => by
    induction c using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

theorem bridge {Γ : Type*} [Group Γ] (H N : Subgroup Γ) [N.Normal] (hNH : N ≤ H) (hH : H.index ≠ 0)
    [Fintype (Γ ⧸ N)] (φ : Γ → ℝ) (hφ : ∀ h ∈ H, ∀ k, φ (h * k) = φ k) :
    (H.index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel H), φ c.out =
      (Fintype.card (Γ ⧸ N) : ℝ)⁻¹ * ∑ q : Γ ⧸ N, φ q.out := by
  classical
  let π : (Γ ⧸ N) → Quotient (QuotientGroup.rightRel H) :=
    fun q => Quotient.mk (QuotientGroup.rightRel H) q.out
  have hrel : ∀ a b : Γ, (Quotient.mk (QuotientGroup.rightRel H) a = Quotient.mk _ b) ↔ b * a⁻¹ ∈ H := by
    intro a b
    rw [Quotient.eq]
    exact QuotientGroup.rightRel_apply
  have hπ : ∀ g : Γ, π (g : Γ ⧸ N) = Quotient.mk _ g := by
    intro g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
    show Quotient.mk _ (g : Γ ⧸ N).out = _
    rw [hn, hrel, show g * (g * (n : Γ))⁻¹ = g * (n : Γ)⁻¹ * g⁻¹ by group]
    exact hNH (‹N.Normal›.conj_mem _ (N.inv_mem n.2) g)
  have hsurj : Function.Surjective π := fun c =>
    ⟨(c.out : Γ ⧸ N), by rw [hπ]; exact Quotient.out_eq c⟩
  haveI : Fintype (Quotient (QuotientGroup.rightRel H)) := Fintype.ofSurjective π hsurj
  have hψ : ∀ q : Γ ⧸ N, φ q.out = φ (π q).out := fun q => (rel_out H φ hφ q.out).symm
  have hπmul : ∀ q t x : Γ ⧸ N, π q = π x → π (q * t) = π (x * t) := by
    intro q t x h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hπ, hπ]
    rw [hπ, hπ, hrel] at h
    rw [hrel, show d * b * (a * b)⁻¹ = d * a⁻¹ by group]
    exact h
  set r := (Finset.univ.filter (fun q : Γ ⧸ N => π q = π 1)).card with hr
  have hfib : ∀ c, (Finset.univ.filter (fun q : Γ ⧸ N => π q = c)).card = r := by
    intro c
    obtain ⟨t, rfl⟩ := hsurj c
    symm
    refine Finset.card_nbij' (fun q => q * t) (fun q => q * t⁻¹) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      simpa using hπmul q t 1 hq
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      simpa using hπmul q t⁻¹ t hq
    · intro q _
      simp
    · intro q _
      simp
  have hsum : ∑ q : Γ ⧸ N, φ q.out
      = r * ∑ c : Quotient (QuotientGroup.rightRel H), φ c.out := by
    calc ∑ q : Γ ⧸ N, φ q.out = ∑ q : Γ ⧸ N, φ (π q).out := Finset.sum_congr rfl fun q _ => hψ q
      _ = ∑ c : Quotient (QuotientGroup.rightRel H),
            ∑ q ∈ Finset.univ.filter (fun q : Γ ⧸ N => π q = c), φ (π q).out :=
          (Finset.sum_fiberwise _ π _).symm
      _ = ∑ c : Quotient (QuotientGroup.rightRel H),
            ∑ q ∈ Finset.univ.filter (fun q : Γ ⧸ N => π q = c), φ c.out :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun q hq => by
            rw [(Finset.mem_filter.1 hq).2]
      _ = ∑ c : Quotient (QuotientGroup.rightRel H), (r : ℝ) * φ c.out := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_const, hfib c, nsmul_eq_mul]
      _ = r * ∑ c : Quotient (QuotientGroup.rightRel H), φ c.out := (Finset.mul_sum _ _ _).symm
  have hcard : Fintype.card (Γ ⧸ N) = r * Fintype.card (Quotient (QuotientGroup.rightRel H)) := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hindex : H.index = Fintype.card (Quotient (QuotientGroup.rightRel H)) := by
    rw [Subgroup.index_eq_card, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  have hr0 : (r : ℝ) ≠ 0 := by
    have h1 : (1 : Γ ⧸ N) ∈ Finset.univ.filter (fun q : Γ ⧸ N => π q = π 1) := by simp
    exact_mod_cast (Finset.card_pos.2 ⟨1, h1⟩).ne'
  rw [finsum_eq_sum_of_fintype, hsum, hcard, hindex]
  push_cast
  field_simp

end PositivityTheory.KB.SpectralGap.DesignMultiplication

namespace PositivityTheory.KB.SpectralGap

open DesignMultiplication in
theorem design_holds : Design := by
  intro Λ S _ _ j B E E' K hB hEK hE'K hidx hTT h25 a b ha hb x h0
  classical
  subst hB
  set Bk := (E ⊓ E').subgroupOf K with hBk
  set N := Bk.normalCore with hN
  haveI : Bk.FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx
  haveI : Finite (K ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hNB : N ≤ Bk := Subgroup.normalCore_le _
  let φ : (S → ℝ) → K → ℝ := fun u k => u (j (k : Λ) * x)
  have hinvB : ∀ u, LInv j (E ⊓ E') u → ∀ h ∈ Bk, ∀ k, φ u (h * k) = φ u k := by
    intro u hu h hh k
    show u (j ((h : Λ) * (k : Λ)) * x) = u (j (k : Λ) * x)
    rw [map_mul, mul_assoc]
    exact hu _ (Subgroup.mem_subgroupOf.mp hh) _
  have havg : ∀ u, LInv j (E ⊓ E') u →
      avg j (E ⊓ E') K u x = (Fintype.card (K ⧸ N) : ℝ)⁻¹ * ∑ q : K ⧸ N, φ u q.out :=
    fun u hu => bridge Bk N hNB hidx (φ u) (hinvB u hu)
  have haB : LInv j (E ⊓ E') a := fun γ hγ y => ha γ hγ.1 y
  have hbB : LInv j (E ⊓ E') b := fun γ hγ y => hb γ hγ.2 y
  have habB : LInv j (E ⊓ E') (fun y => a y * b y) := fun γ hγ y => by
    simp only [haB γ hγ y, hbB γ hγ y]
  have haaB : LInv j (E ⊓ E') (fun y => a y ^ 2) := fun γ hγ y => by
    simp only [haB γ hγ y]
  have hbbB : LInv j (E ⊓ E') (fun y => b y ^ 2) := fun γ hγ y => by
    simp only [hbB γ hγ y]
  have hf0 : ∀ u, LInv j (E ⊓ E') u → ∀ k : K, φ u ((k : K ⧸ N).out) = φ u k :=
    fun u hu k => out_mk N Bk hNB (φ u) (hinvB u hu) k
  set EG := (E.subgroupOf K).map (QuotientGroup.mk' N) with hEG
  set E'G := (E'.subgroupOf K).map (QuotientGroup.mk' N) with hE'G
  set f : K ⧸ N → ℝ := fun q => φ a q.out with hfdef
  set g : K ⧸ N → ℝ := fun q => φ b q.out with hgdef
  have hf : ∀ e ∈ EG, ∀ q, f (e * q) = f q := by
    intro e he q
    obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    show φ a ((QuotientGroup.mk' N e0 * (k : K ⧸ N)).out) = φ a (k : K ⧸ N).out
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hf0 a haB, hf0 a haB]
    show a (j ((e0 : Λ) * (k : Λ)) * x) = a (j (k : Λ) * x)
    rw [map_mul, mul_assoc]
    exact ha _ (Subgroup.mem_subgroupOf.mp he0) _
  have hg : ∀ e ∈ E'G, ∀ q, g (e * q) = g q := by
    intro e he q
    obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    show φ b ((QuotientGroup.mk' N e0 * (k : K ⧸ N)).out) = φ b (k : K ⧸ N).out
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hf0 b hbB, hf0 b hbB]
    show b (j ((e0 : Λ) * (k : Λ)) * x) = b (j (k : Λ) * x)
    rw [map_mul, mul_assoc]
    exact hb _ (Subgroup.mem_subgroupOf.mp he0) _
  have htt : ∀ q, q ∉ EG → ∀ q', q' ∉ EG → ∃ e ∈ EG, ∃ e' ∈ EG, q' = e * q * e' := by
    intro q hq q' hq'
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective q'
    have hk : (k : Λ) ∉ E := fun h =>
      hq (Subgroup.mem_map.mpr ⟨k, Subgroup.mem_subgroupOf.mpr h, rfl⟩)
    have hk' : (k' : Λ) ∉ E := fun h =>
      hq' (Subgroup.mem_map.mpr ⟨k', Subgroup.mem_subgroupOf.mpr h, rfl⟩)
    obtain ⟨e, he, e', he', heq⟩ := hTT k k.2 hk k' k'.2 hk'
    refine ⟨QuotientGroup.mk' N ⟨e, hEK he⟩,
      Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr he, rfl⟩,
      QuotientGroup.mk' N ⟨e', hEK he'⟩,
      Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr he', rfl⟩, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    ext
    simp [heq]
  have hcard0 : (Fintype.card (K ⧸ N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum0 : ∑ q, f q = 0 := by
    have := havg a haB
    rw [h0] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h (inv_ne_zero hcard0)
    · exact h
  have hcore := core EG E'G htt f g hf hg hsum0
  have hidxG : ((EG.subgroupOf E'G).index : ℝ) ≥ 25 := by
    have hNE : N ≤ E.subgroupOf K := fun y hy =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp (hNB hy)).1
    have e1 : (EG.subgroupOf E'G).index = (E.subgroupOf E').index := by
      have h1 := Subgroup.relIndex_comap EG (QuotientGroup.mk' N) (E'.subgroupOf K)
      rw [hEG, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNE,
        Subgroup.relIndex_subgroupOf hE'K] at h1
      exact h1.symm
    rw [e1, ← Subgroup.inf_subgroupOf_right]
    exact_mod_cast h25
  rw [havg _ habB, havg _ haaB, havg _ hbbB]
  have hA : 0 ≤ ∑ q, f q ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hBq : 0 ≤ ∑ q, g q ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
  have key : (∑ q, f q * g q) ^ 2 ≤ 1 / 25 * ((∑ q, f q ^ 2) * ∑ q, g q ^ 2) := by
    have hS : 0 ≤ (∑ q, f q * g q) ^ 2 := sq_nonneg _
    nlinarith
  show ((Fintype.card (K ⧸ N) : ℝ)⁻¹ * ∑ q, f q * g q) ^ 2 ≤
    1 / 25 * (((Fintype.card (K ⧸ N) : ℝ)⁻¹ * ∑ q, f q ^ 2) *
      ((Fintype.card (K ⧸ N) : ℝ)⁻¹ * ∑ q, g q ^ 2))
  have hc2 : 0 ≤ ((Fintype.card (K ⧸ N) : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc ((Fintype.card (K ⧸ N) : ℝ)⁻¹ * ∑ q, f q * g q) ^ 2
      = ((Fintype.card (K ⧸ N) : ℝ)⁻¹) ^ 2 * (∑ q, f q * g q) ^ 2 := by ring
    _ ≤ ((Fintype.card (K ⧸ N) : ℝ)⁻¹) ^ 2 * (1 / 25 * ((∑ q, f q ^ 2) * ∑ q, g q ^ 2)) :=
        mul_le_mul_of_nonneg_left key hc2
    _ = _ := by ring

end PositivityTheory.KB.SpectralGap
