import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfForall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFlagPairingCramerOfLeadingCoeffs
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Kill

open GlobalTheory.DegCnt.IdealPow GlobalTheory.DegCnt.BlockMinor GlobalTheory.DegCnt.FrameCramer GlobalTheory.DegCnt.Monomial GlobalTheory.UnimodQuot

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem c_ne (N : NF H r) : N.c ≠ 0 := fun h => by simpa [h] using N.c_norm

theorem Dl_eq (N : NF H r) (l : ℕ) (hl : l ≤ N.j) : ∃ ε : ℤˣ,
    Dl N.F N.F' l ((hl.trans N.j_le).trans (Nat.le_succ r)) = ((ε : ℤ) : K) * minor N.w.blocks l := by
  refine ⟨∏ b : Fin l, N.sgn (Fin.castLE hl b), ?_⟩
  have : (Zhat N.F N.F').submatrix (Fin.castLE ((hl.trans N.j_le).trans (Nat.le_succ r)))
      (Fin.castLE ((hl.trans N.j_le).trans (Nat.le_succ r))) =
      (Matrix.of fun a b : Fin l => Formalism.MainNotions.S.Loc.ptEntryL N.w.blocks a b) *
        Matrix.diagonal fun b : Fin l => ((N.sgn (Fin.castLE hl b) : ℤ) : K) := by
    ext a b
    rw [Matrix.mul_diagonal]
    exact N.pair (Fin.castLE hl a) (Fin.castLE hl b)
  unfold Dl minor
  rw [this, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
  push_cast
  rfl

omit [NumberField K] [StarRing K] in
theorem unit_ne (ε : ℤˣ) : ((ε : ℤ) : K) ≠ 0 := by
  rcases Int.units_eq_one_or ε with h | h <;> simp [h]

omit [NumberField K] [StarRing K] in
theorem unit_sq (ε : ℤˣ) : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
  rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]

theorem Dj_ne (N : NF H r) : Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ≠ 0 := by
  obtain ⟨ε, hε⟩ := Dl_eq N N.j le_rfl
  rw [hε]
  refine mul_ne_zero (unit_ne ε) ?_
  have := minor_full N.w.blocks
  rwa [N.w.size] at this

theorem pair' (N : NF H r) (a b : Fin r) (ha : a.val < N.j) (hb : b.val < N.j) :
    H.B (N.F.e a.castSucc) (N.F'.e b.castSucc) =
      Formalism.MainNotions.S.Loc.ptEntryL N.w.blocks a b * ((N.sgn ⟨b, hb⟩ : ℤ) : K) := N.pair ⟨a, ha⟩ ⟨b, hb⟩

theorem sum_block (r l s : ℕ) : 2 * ∑ a ∈ Finset.range (l + s), ((r : ℤ) - a) =
    2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a) + s * (2 * r - 2 * l - s + 1) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, Finset.sum_range_succ, mul_add, ih]; push_cast; ring

omit [NumberField K] [StarRing K] in
theorem mem_one_of_pow (γ : 𝓞 K) {w : K} {s : ℕ} (hs : 0 < s) (ε : ℤˣ) {t : K} (ht : t ∈ (1 : Submodule (𝓞 K) K))
    (h : (γ : K) * w ^ s = ((ε : ℤ) : K) * t) : (γ : K) * w ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at ht ⊢
  apply IsIntegral.of_pow hs
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have : ((γ : K) * w) ^ (s + 1) = (γ : K) ^ s * (((ε : ℤ) : K) * t) := by
    rw [← h, Nat.succ_eq_add_one]; ring
  rw [this]
  exact (γ.isIntegral_coe.pow s).mul ((isIntegral_algebraMap (R := ℤ) (x := (ε : ℤ))).mul ht)

def Absorbs (𝔡 𝔠 : Ideal (𝓞 K)) (m : ℤ) (g : K) : Prop := g ≠ 0 → ∀ γ ∈ 𝔠,
  (∀ u ∈ ipow 𝔡 m, (γ : K) * u * g ∈ (1 : Submodule (𝓞 K) K)) ∧
  (∀ u ∈ ipow 𝔡 (-m), (γ : K) * u / g ∈ (1 : Submodule (𝓞 K) K))

omit [StarRing K] in
theorem absorbs_zero {𝔡 𝔠 : Ideal (𝓞 K)} {m : ℤ} {g : K} (h : g = 0) : Absorbs 𝔡 𝔠 m g := fun h' => absurd h h'

theorem Absorbs.star {𝔡 𝔠 : Ideal (𝓞 K)} {m m' : ℤ} {x y : V} (h : 𝔡 ≠ ⊥)
    (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (hc : ∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K))
    (hg : Absorbs 𝔡 𝔠 m (H.B x y)) (hm : m' = m) : Absorbs 𝔡 𝔠 m' (H.B y x) := by
  subst hm
  rw [← H.herm]
  intro h0 γ hγ
  obtain ⟨γ', hγ', e⟩ := hc γ hγ
  have := hg (fun h => h0 (by rw [h, star_zero])) γ' hγ'
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have := star_mem_one (this.1 _ (star_mem h hs hu))
    simpa [e, mul_comm, mul_left_comm] using this
  · have := star_mem_one (this.2 _ (star_mem h hs hu))
    simpa [e, mul_comm, mul_left_comm] using this

omit [StarRing K] in
theorem absorbs_of_dvd {𝔡 𝔠 : Ideal (𝓞 K)} {m : ℤ} (hm : m = 0) (g : 𝓞 K) (hg : ∀ x ∈ 𝔠, g ∣ x) {g' : K}
    (e : g' = g) : Absorbs 𝔡 𝔠 m g' := by
  subst hm e
  intro h0 γ hγ
  rw [neg_zero, ipow_zero]
  obtain ⟨δ, rfl⟩ := hg γ hγ
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩ <;> obtain ⟨u, rfl⟩ := Submodule.mem_one.1 hu
  · exact Submodule.mem_one.2 ⟨g * δ * u * g, by simp⟩
  · refine Submodule.mem_one.2 ⟨δ * u, ?_⟩
    rw [eq_div_iff h0]
    simp; ring

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem absorbs_pair (N : NF H r) {Λ : Submodule (𝓞 K) V}
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) (hF : IsFrame N.F Λ N.aa) (hF' : IsFrame N.F' Λ N.aa)
    {𝔠 : Ideal (𝓞 K)}
    (hD : ∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠,
      ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧
        (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K))
    (a b : Fin r) (ha : a.val < N.j) (hb : b.val < N.j) :
    Absorbs N.𝔡 𝔠 (-((r : ℤ) - a.val) + -((r : ℤ) - b.val)) (H.B (N.F.e a.castSucc) (N.F'.e b.castSucc)) := by
  intro h0 γ hγ
  obtain ⟨l, s, t, ε, h1, h2, h3, h4, h5, h6⟩ := exists_block N.w.blocks a (by rw [N.w.size]; exact ha)
  rw [N.w.size] at h3
  rw [pair' N a b ha hb, h4] at h0 ⊢
  have hab : a.val + b.val + 1 = l + (l + s) := by
    by_contra hc
    exact h0 (by rw [if_neg hc, zero_mul])
  rw [if_pos hab] at h0 ⊢
  obtain ⟨ε₁, e1⟩ := Dl_eq N l (by omega)
  obtain ⟨ε₂, e2⟩ := Dl_eq N (l + s) h3
  have n1 := e1 ▸ mul_ne_zero (unit_ne (K := K) ε₁) h5
  have n2 := e2 ▸ mul_ne_zero (unit_ne (K := K) ε₂)
    (h6 ▸ mul_ne_zero (mul_ne_zero (unit_ne (K := K) ε) (pow_ne_zero s t.ne_zero)) h5)
  have m1 := mem_of_forall N.𝔡_ne (neg_add_cancel _) (x := (γ : K) / Dl N.F N.F' l _)
    fun y hy => by rw [div_mul_eq_mul_div]; exact (hD l _ (by omega) n1 γ hγ y hy).1
  have m2 := mem_of_forall N.𝔡_ne (neg_add_cancel _) (x := (γ : K) / Dl N.F N.F' (l + s) _)
    fun y hy => by rw [div_mul_eq_mul_div]; exact (hD (l + s) _ h3 n2 γ hγ y hy).1
  have hab' : (a.val : ℤ) + b.val + 1 = l + (l + s) := by exact_mod_cast hab
  have hsum := sum_block r l s
  set g := (t : K) * ((N.sgn ⟨b, hb⟩ : ℤ) : K) with hg
  set η : ℤˣ := ε₂ * ε * ε₁ * N.sgn ⟨b, hb⟩ ^ s with hη
  have e3 : Dl N.F N.F' (l + s) ((h3.trans N.j_le).trans (Nat.le_succ r)) = ((η : ℤ) : K) * g ^ s *
      Dl N.F N.F' l (((Nat.le_add_right l s).trans (h3.trans N.j_le)).trans (Nat.le_succ r)) := by
    rw [e1, e2, h6, hη, hg]
    have q1 := unit_sq (K := K) ε₁
    have q2 : ((N.sgn ⟨b, hb⟩ : ℤ) : K) ^ s * ((N.sgn ⟨b, hb⟩ : ℤ) : K) ^ s = 1 := by
      rw [← mul_pow, unit_sq, one_pow]
    push_cast
    rw [mul_pow]
    linear_combination (-(((ε₂ : ℤ) : K) * ((ε : ℤ) : K) * (t : K) ^ s * minor N.w.blocks l)) * q1 -
      (((ε₂ : ℤ) : K) * ((ε : ℤ) : K) * (t : K) ^ s * minor N.w.blocks l * ((ε₁ : ℤ) : K) * ((ε₁ : ℤ) : K)) * q2
  have q := unit_sq (K := K) η
  have qn := unit_ne (K := K) η
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have := (cramer N.F N.F' Λ hint N.𝔡_ne N.𝔡_star hF.1 hF'.1 (h3.trans N.j_le)
      (mul_mem N.𝔡_ne (by rw [hsum]; linear_combination (s : ℤ) * hab') m1 (pow_mem N.𝔡_ne hu s))).1
    rw [mul_assoc]
    refine mem_one_of_pow γ (s := s) (by omega) η this ?_
    rw [e3]
    field_simp
    linear_combination (-((γ : K) * (u * g) ^ s)) * q
  · have := (cramer N.F N.F' Λ hint N.𝔡_ne N.𝔡_star hF.1 hF'.1 ((Nat.le_add_right l s).trans (h3.trans N.j_le))
      (mul_mem N.𝔡_ne (by rw [hsum]; linear_combination (-s : ℤ) * hab') m2 (pow_mem N.𝔡_ne hu s))).1
    rw [mul_div_assoc]
    refine mem_one_of_pow γ (s := s) (by omega) η this ?_
    rw [e3, div_pow]
    field_simp

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem swap0 {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by rw [← H.herm, h, star_zero]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_e'_high (N : NF H r) (a b : Fin r) (ha : N.j ≤ a.val) :
    H.B (N.F.e a.castSucc) (N.F'.e b.castSucc) = 0 := by
  have := N.F'.iso a b
  rw [N.same a.castSucc ha, H.B.map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left (c_ne N)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem z_e' (N : NF H r) (b : Fin r) : H.B N.F.z (N.F'.e b.castSucc) = 0 := by
  have := swap0 (N.F'.zperp b)
  rw [N.same (Fin.last r) N.j_le, H.B.map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left (c_ne N)

def vec (N : NF H r) : Fin r ⊕ {a : Fin r // a.val < N.j} ⊕ Unit ⊕ {a : Fin r // N.j ≤ a.val} → V :=
  Sum.elim (fun a => N.F.e a.castSucc) (Sum.elim (fun a => N.F'.e a.1.castSucc)
    (Sum.elim (fun _ => N.F.z) fun a => N.ist a.1))

def expo (N : NF H r) : Fin r ⊕ {a : Fin r // a.val < N.j} ⊕ Unit ⊕ {a : Fin r // N.j ≤ a.val} → ℤ :=
  Sum.elim (fun a => -((r : ℤ) - a.val)) (Sum.elim (fun a => -((r : ℤ) - a.1.val))
    (Sum.elim (fun _ => 0) fun a => (r : ℤ) - a.1.val))

theorem P0_eq (N : NF H r) : N.P0 = ⨆ i, line (ipow N.𝔡 (expo N i)) (vec N i) := by
  simp only [iSup_sum, iSup_subtype, iSup_const, NF.P0, NF.aa, vec, expo, Sum.elim_inl, Sum.elim_inr, ipow_zero,
    sup_assoc]

theorem kill_ideal_P0 (N : NF H r) {Λ : Submodule (𝓞 K) V}
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) (hF : IsFrame N.F Λ N.aa) (hF' : IsFrame N.F' Λ N.aa)
    {𝔠 : Ideal (𝓞 K)} (hc : ∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) (hT : ∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x)
    (hD : ∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠,
      ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧
        (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) :
    𝔠 • dual H N.P0 ≤ N.P0 ∧ 𝔠 • N.P0 ≤ dual H N.P0 := by
  have a12 : ∀ a b, Absorbs N.𝔡 𝔠 (expo N (.inl a) + expo N (.inr (.inl b)))
      (H.B (vec N (.inl a)) (vec N (.inr (.inl b)))) := by
    intro a b
    by_cases ha : a.val < N.j
    · exact absorbs_pair N hint hF hF' hD a b.1 ha b.2
    · exact absorbs_zero (e_e'_high N a b.1 (not_lt.1 ha))
  have a14 : ∀ a b, Absorbs N.𝔡 𝔠 (expo N (.inl a) + expo N (.inr (.inr (.inr b))))
      (H.B (vec N (.inl a)) (vec N (.inr (.inr (.inr b))))) := by
    intro a b
    have := N.ist_e a b.1 b.2
    by_cases hab : a = b.1
    · rw [if_pos hab] at this
      exact absorbs_of_dvd (by simp [expo, hab]) 1 (fun _ _ => one_dvd _) (this.trans (by simp))
    · rw [if_neg hab] at this
      exact absorbs_zero this
  have hzz : H.B N.F.z N.F.z = -(N.T : K) := N.hT ▸ N.F.zz
  have hex : ∀ a : Fin r, a.val < N.j → ∃ b : Fin r, b.val < N.j ∧
      Formalism.MainNotions.S.Loc.ptEntryL N.w.blocks a b ≠ 0 ∧ ∀ a', Formalism.MainNotions.S.Loc.ptEntryL N.w.blocks a' b ≠ 0 → a' = a := by
    intro a ha
    obtain ⟨b, hb, h⟩ := exists_entry N.w.blocks a (by rw [N.w.size]; exact ha)
    rw [N.w.size] at hb
    exact ⟨⟨b, hb.trans_le N.j_le⟩, hb, h⟩
  refine monomial (vec N) (expo N) N.𝔡_ne N.𝔡_star (fun i k => ?_) (fun i => ?_) _ (P0_eq N)
  · show Absorbs N.𝔡 𝔠 _ _
    rcases i with a | a | a | a <;> rcases k with b | b | b | b
    · exact absorbs_zero (N.F.iso a b)
    · exact a12 a b
    · exact absorbs_zero (N.F.zperp a)
    · exact a14 a b
    · exact (a12 b a).star N.𝔡_ne N.𝔡_star hc (add_comm _ _)
    · exact absorbs_zero (N.F'.iso a b)
    · exact absorbs_zero (swap0 (z_e' N a))
    · exact absorbs_zero (N.ist_e' a b a.2 b.2)
    · exact absorbs_zero (swap0 (N.F.zperp b))
    · exact absorbs_zero (z_e' N b)
    · exact absorbs_of_dvd (by simp [expo]) (-(N.T : 𝓞 K)) (fun x hx => neg_dvd.2 (hT x hx)) (hzz.trans (by simp))
    · exact absorbs_zero (N.normalForm_dual_orthogonal_last b b.2)
    · exact (a14 b a).star N.𝔡_ne N.𝔡_star hc (add_comm _ _)
    · exact absorbs_zero (swap0 (N.ist_e' b a b.2 a.2))
    · exact absorbs_zero (swap0 (N.normalForm_dual_orthogonal_last a a.2))
    · exact absorbs_zero (N.ist_iso a b a.2 b.2)
  · rcases i with a | a | a | a
    · by_cases ha : a.val < N.j
      · obtain ⟨b, hb, h1, h2⟩ := hex a ha
        refine ⟨.inr (.inl ⟨b, hb⟩), ?_, ?_⟩
        · exact pair' N a b ha hb ▸ mul_ne_zero h1 (unit_ne _)
        · rintro (i | i | i | i) hi
          · by_cases hij : i.val < N.j
            · refine (pair' N i b hij hb).trans (mul_eq_zero_of_left ?_ _)
              by_contra h3
              exact hi (congrArg Sum.inl (Fin.ext (h2 _ h3)))
            · exact e_e'_high N i b (not_lt.1 hij)
          · exact N.F'.iso i b
          · exact z_e' N b
          · exact swap0 (N.ist_e' b i hb i.2)
      · have ha' := not_lt.1 ha
        refine ⟨.inr (.inr (.inr ⟨a, ha'⟩)), ?_, ?_⟩
        · exact (N.ist_e a a ha').trans_ne (by simp)
        · rintro (i | i | i | i) hi
          · exact (N.ist_e i a ha').trans (if_neg fun h => hi (congrArg Sum.inl h))
          · exact N.ist_e' i a i.2 ha'
          · exact N.normalForm_dual_orthogonal_last a ha'
          · exact N.ist_iso i a i.2 ha'
    · obtain ⟨b, hb, h1, h2⟩ := hex a a.2
      refine ⟨.inl b, fun h => ?_, ?_⟩
      · have := swap0 h
        rw [entry_symm] at h1
        exact (pair' N b a hb a.2 ▸ mul_ne_zero h1 (unit_ne _)) this
      · rintro (i | i | i | i) hi
        · exact N.F.iso i b
        · refine swap0 ((pair' N b i hb i.2).trans (mul_eq_zero_of_left ?_ _))
          by_contra h3
          rw [entry_symm] at h3
          exact hi (congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext (Fin.ext (h2 _ h3))))
        · exact swap0 (N.F.zperp b)
        · refine swap0 ((N.ist_e b i i.2).trans (if_neg fun h => ?_))
          have := i.2
          rw [← h] at this
          omega
    · refine ⟨.inr (.inr (.inl ())), ?_, ?_⟩
      · exact N.F.zz.trans_ne (neg_ne_zero.2 N.F.hT)
      · rintro (i | i | i | i) hi
        · exact N.F.zperp i
        · exact swap0 (z_e' N i)
        · exact absurd rfl hi
        · exact swap0 (N.normalForm_dual_orthogonal_last i i.2)
    · refine ⟨.inl a.1, fun h => ?_, ?_⟩
      · have := (N.ist_e a a a.2).symm.trans (swap0 h)
        simp at this
      · rintro (i | i | i | i) hi
        · exact N.F.iso i a
        · exact swap0 (e_e'_high N a i a.2)
        · exact swap0 (N.F.zperp a)
        · exact swap0 ((N.ist_e a i i.2).trans (if_neg fun h =>
            hi (congrArg (fun x => Sum.inr (Sum.inr (Sum.inr x))) (Subtype.ext h.symm))))

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem orth_Xa (F : FlagD H r) {m : ℕ} {v : V} (hv : ∀ a : Fin r, H.B (F.e a.castSucc) v = 0) {x : V}
    (hx : x ∈ F.Xa m) : H.B x v = 0 := by
  have : F.Xa m ≤ LinearMap.ker (H.B.flip v) := by
    rw [FlagD.Xa, Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    exact hv a
  exact this hx

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem iso_Xa (F : FlagD H r) {m n : ℕ} {x y : V} (hx : x ∈ F.Xa m) (hy : y ∈ F.Xa n) : H.B x y = 0 := by
  refine orth_Xa F (fun a => ?_) hx
  rw [← H.herm, orth_Xa F (fun b => F.iso b a) hy, star_zero]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_le (F : FlagD H r) (m : ℕ) : F.Xa m ≤ F.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem X_le (F F' : FlagD H r) (j : ℕ) (h : ∀ a : Fin r, j ≤ a.val → ∃ c : K, F.e a.castSucc = c • F'.e a.castSucc) :
    ∀ x ∈ F.X, ∃ y ∈ F.Xa j, ∃ i, i ∈ F.X ∧ i ∈ F'.X ∧ y + i = x := by
  have : F.X ≤ F.Xa j ⊔ (F.X ⊓ F'.X) := by
    rw [FlagD.X, FlagD.Xa, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    by_cases hj : a.val < j
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, hj, rfl⟩)
    · obtain ⟨c, hc⟩ := h a (not_lt.1 hj)
      refine Submodule.mem_sup_right ⟨Submodule.subset_span ⟨a, ha, rfl⟩, ?_⟩
      show F.e a.castSucc ∈ F'.X
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  intro x hx
  obtain ⟨y, hy, i, hi, e⟩ := Submodule.mem_sup.1 (this hx)
  exact ⟨y, hy, i, hi.1, hi.2, e⟩

theorem kill_ideal_V0 (N : NF H r) {Λ : Submodule (𝓞 K) V}
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) (hF : IsFrame N.F Λ N.aa) (hF' : IsFrame N.F' Λ N.aa)
    {𝔠 : Ideal (𝓞 K)} (hT : ∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x)
    (hD : ∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠,
      ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧
        (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K))
    {v : V} (hv : v ∈ V0 N.F N.F') (hvp : ∀ p ∈ Λ, p ∈ V0 N.F N.F' → H.B v p ∈ (1 : Submodule (𝓞 K) K))
    {γ₁ γ₂ γ₃ : 𝓞 K} (h₁ : γ₁ ∈ 𝔠) (h₂ : γ₂ ∈ 𝔠) (h₃ : γ₃ ∈ 𝔠) :
    γ₁ • γ₂ • γ₃ • v ∈ Λ ⊔ rs (𝓞 K) (II N.F N.F') := by
  have hDj := Dj_ne N
  have k1 : ∀ γ ∈ 𝔠, ∀ x ∈ N.F.Xa N.j, (∀ p ∈ Λ, p ∈ N.F'.Xa N.j → H.B x p ∈ (1 : Submodule (𝓞 K) K)) →
      (γ : K) • x ∈ Λ := by
    intro γ hγ x hx hp
    have m := mem_of_forall N.𝔡_ne (neg_add_cancel _) (x := (γ : K) / Dl N.F N.F' N.j _)
      fun y hy => by rw [div_mul_eq_mul_div]; exact (hD N.j _ le_rfl hDj γ hγ y hy).1
    have := (cramer N.F N.F' Λ hint N.𝔡_ne N.𝔡_star hF.1 hF'.1 N.j_le m).2 x hx hp
    rwa [div_mul_cancel₀ _ hDj] at this
  have k2 : ∀ γ ∈ 𝔠, ∀ x ∈ N.F'.Xa N.j, (∀ p ∈ Λ, p ∈ N.F.Xa N.j → H.B x p ∈ (1 : Submodule (𝓞 K) K)) →
      (γ : K) • x ∈ Λ := by
    intro γ hγ x hx hp
    have m := mem_of_forall N.𝔡_ne (neg_add_cancel _) (x := (γ : K) / star (Dl N.F N.F' N.j _))
      fun y hy => by rw [div_mul_eq_mul_div]; exact (hD N.j _ le_rfl hDj γ hγ y hy).2
    have := (cramer N.F' N.F Λ hint N.𝔡_ne N.𝔡_star hF'.1 hF.1 N.j_le m).2 x hx hp
    rwa [Dl_swap N.F N.F', div_mul_cancel₀ _ (star_ne_zero.2 hDj)] at this
  have d1 := X_le N.F N.F' N.j fun a ha => ⟨N.c⁻¹, by
    rw [N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ (c_ne N), one_smul]⟩
  have d2 := X_le N.F' N.F N.j fun a ha => ⟨N.c, N.same a.castSucc ha⟩
  have zX : ∀ {m : ℕ} {x : V}, x ∈ N.F.Xa m → H.B x N.F.z = 0 := fun hx => orth_Xa N.F N.F.zperp hx
  have zX' : ∀ {m : ℕ} {x : V}, x ∈ N.F'.Xa m → H.B x N.F.z = 0 := fun hx =>
    orth_Xa N.F' (fun a => swap0 (z_e' N a)) hx
  have hXV : N.F.X ≤ V0 N.F N.F' := le_sup_left.trans le_sup_left
  have hX'V : N.F'.X ≤ V0 N.F N.F' := le_sup_right.trans le_sup_left
  have hzV : N.F.z ∈ V0 N.F N.F' := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hzz : H.B N.F.z N.F.z = -(N.T : K) := N.hT ▸ N.F.zz
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨x₀, hx₀, x₀', hx₀', rfl⟩ := Submodule.mem_sup.1 hv₁
  obtain ⟨x, hx, i, hi, hi', rfl⟩ := d1 x₀ hx₀
  obtain ⟨x', hx', i₂, hi₂', hi₂, rfl⟩ := d2 x₀' hx₀'
  obtain ⟨β, rfl⟩ : ∃ β : K, β • N.F.z = v₂ := by
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv₂
    refine ⟨a + b * N.c, ?_⟩
    rw [add_smul, mul_smul]
    exact congrArg (fun t => a • N.F.z + b • t) (N.same (Fin.last r) N.j_le).symm
  have hx1 := fun γ hγ => k1 γ hγ x hx fun p hp hp' => by
    have := hvp p hp (hX'V (Xa_le _ _ hp'))
    simpa [iso_Xa N.F' hi' hp', iso_Xa N.F' hx' hp', iso_Xa N.F' hi₂' hp', swap0 (zX' hp')] using this
  have hx2 := fun γ hγ => k2 γ hγ x' hx' fun p hp hp' => by
    have := hvp p hp (hXV (Xa_le _ _ hp'))
    simpa [iso_Xa N.F hi hp', iso_Xa N.F hx hp', iso_Xa N.F hi₂ hp', swap0 (zX hp')] using this
  have h1 : (1 : K) ∈ lead N.F Λ (Fin.last r) := by rw [hF.2]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨zt, hzt, ξ₀, hξ₀, hz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨ξ, hξ, ι, hι, hι', rfl⟩ := d1 ξ₀ hξ₀
  have hz' : zt = N.F.z - ξ - ι := by
    have : zt + (ξ + ι) = (1 : K) • N.F.z := hz
    rw [one_smul] at this
    rw [← this]; abel
  have hξp : ∀ p ∈ Λ, p ∈ N.F'.Xa N.j → H.B ξ p ∈ (1 : Submodule (𝓞 K) K) := fun p hp hp' => by
    have := neg_mem (hint zt hzt p hp)
    simpa [hz', iso_Xa N.F' hι' hp', swap0 (zX' hp')] using this
  have hβ : -(β * N.T) - H.B x' ξ ∈ (1 : Submodule (𝓞 K) K) := by
    have := hvp zt hzt (by rw [hz']; exact sub_mem (sub_mem hzV (hXV (Xa_le _ _ hξ))) (hXV hι))
    convert this using 1
    simp [hz', hzz, zX hx, zX hi, zX hi₂, zX' hx', iso_Xa N.F hx hξ, iso_Xa N.F hi hξ, iso_Xa N.F hi₂ hξ,
      iso_Xa N.F hx hι, iso_Xa N.F hi hι, iso_Xa N.F hi₂ hι, iso_Xa N.F' hx' hι', swap0 (zX hξ), swap0 (zX hι)]
    ring
  have hβ2 : (γ₁ : K) * H.B x' ξ ∈ (1 : Submodule (𝓞 K) K) := by
    have := star_mem_one (hξp _ (hx2 γ₁ h₁) (Submodule.smul_mem _ _ hx'))
    rwa [H.herm, H.B.map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  obtain ⟨δ, hδ⟩ := hT γ₂ h₂
  obtain ⟨o₁, ho₁⟩ := Submodule.mem_one.1 hβ
  obtain ⟨o₂, ho₂⟩ := Submodule.mem_one.1 hβ2
  have ho : (γ₁ : K) * γ₂ * β = algebraMap (𝓞 K) K (-(δ * (γ₁ * o₁ + o₂))) := by
    rw [map_neg, map_mul, map_add, map_mul, ho₁, ho₂, hδ]
    show (γ₁ : K) * algebraMap (𝓞 K) K _ * β = -((δ : K) * ((γ₁ : K) * _ + _))
    rw [map_mul, map_natCast]
    show (γ₁ : K) * (_ * (δ : K)) * β = _
    ring
  set M := Λ ⊔ rs (𝓞 K) (II N.F N.F')
  have hI : ∀ {y : V}, y ∈ N.F.X → y ∈ N.F'.X → y ∈ M := fun h h' => Submodule.mem_sup_right ⟨h, h'⟩
  have hL : ∀ {y : V}, (γ₃ : K) • y ∈ Λ → γ₃ • y ∈ M := fun h =>
    Submodule.mem_sup_left (by rw [← algebraMap_smul K γ₃]; exact h)
  have hz3 : γ₃ • N.F.z ∈ M := by
    have : N.F.z = zt + ξ + ι := by rw [hz']; abel
    rw [this, smul_add, smul_add]
    exact add_mem (add_mem (M.smul_mem _ (Submodule.mem_sup_left hzt)) (hL (k1 γ₃ h₃ ξ hξ hξp)))
      (M.smul_mem _ (hI hι hι'))
  rw [smul_add γ₃, smul_add γ₂, smul_add γ₁]
  refine add_mem (M.smul_mem _ (M.smul_mem _ ?_)) ?_
  · rw [smul_add, smul_add, smul_add]
    exact add_mem (add_mem (hL (hx1 γ₃ h₃)) (M.smul_mem _ (hI hi hi')))
      (add_mem (hL (hx2 γ₃ h₃)) (M.smul_mem _ (hI hi₂ hi₂')))
  · have := M.smul_mem (-(δ * (γ₁ * o₁ + o₂))) hz3
    convert this using 1
    rw [← algebraMap_smul K (-(δ * (γ₁ * o₁ + o₂))), ← ho, ← algebraMap_smul K γ₁, ← algebraMap_smul K γ₂,
      smul_comm γ₃ β, smul_smul, smul_smul]

variable [FiniteDimensional K V]

theorem kill_Th (N : NF H r) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ) (hF : IsFrame N.F Λ N.aa)
    (hF' : IsFrame N.F' Λ N.aa) {𝔠 : Ideal (𝓞 K)} (hT : ∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x)
    (hD : ∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠,
      ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧
        (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) :
    𝔠 ^ 3 • dual H (latTh N.F N.F' Λ) ≤ latTh N.F N.F' Λ := by
  have hL := (isLatMod_top_bot_iff Λ).1 hU.1
  have hint : ∀ y ∈ Λ, ∀ x ∈ Λ, H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [← hU.2, mem_dual_iff] at hy
    exact hy.2
  set W := wSp N.F N.F' with hW
  have hUV : N.F.X ⊔ N.F'.X ≤ V0 N.F N.F' := le_sup_left
  have hIU : II N.F N.F' ≤ N.F.X ⊔ N.F'.X := inf_le_left.trans le_sup_left
  have hWU : W ≤ uPerp N.F N.F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hUV hx)
  have hWI : W ≤ perp H (II N.F N.F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hUV (hIU hx))
  have hIW : II N.F N.F' ≤ W := by
    intro y hy
    rw [hW, wSp, mem_perp_iff]
    intro x hx
    apply swap0
    have : V0 N.F N.F' ≤ LinearMap.ker (H.B.flip y) := by
      refine sup_le (sup_le (fun x hx => iso_Xa N.F hx hy.1) (fun x hx => iso_Xa N.F' hx hy.2)) ?_
      rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact swap0 (orth_Xa N.F N.F.zperp hy.1)
      · exact swap0 (orth_Xa N.F' N.F'.zperp hy.2)
    exact this hx
  have hin : ∀ y ∈ W, y ∈ Λ ⊔ rs (𝓞 K) (II N.F N.F') → y ∈ latTh N.F N.F' Λ := by
    intro y hy h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨⟨Submodule.add_mem_sup ⟨ha, hWI ?_⟩ hb, hWU hy⟩, hy⟩
    simpa using W.sub_mem hy (hIW hb)
  have key : ∀ γ₁ ∈ 𝔠, ∀ γ₂ ∈ 𝔠, ∀ γ₃ ∈ 𝔠, ∀ y ∈ dual H (latTh N.F N.F' Λ),
      γ₁ • γ₂ • γ₃ • y ∈ latTh N.F N.F' Λ := by
    intro γ₁ h₁ γ₂ h₂ γ₃ h₃ y hy
    rw [mem_dual_iff] at hy
    have hyW : y ∈ W := (Submodule.span_le.2 fun x hx => hx.2) hy.1
    have hx : ∀ x : ↥(Λ ⊓ rs (𝓞 K) W), IsIntegral ℤ (H.B x y) := by
      intro x
      rw [← mem_one_iff, ← H.herm]
      exact star_mem_one (hy.2 x (hin x x.2.2 (Submodule.mem_sup_left x.2.1)))
    let φ : ↥(Λ ⊓ rs (𝓞 K) W) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x y, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) y = H.B a y + H.B b y
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) y = algebraMap (𝓞 K) K a * H.B b y
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨y', hy', h'⟩ := exists_lattice_rep H hU W φ
    have hd : y' - y ∈ V0 N.F N.F' := by
      apply mem_of_perp_perp H
      intro v hv
      obtain ⟨s, hs⟩ := exists_smul_mem hL v
      have hc := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) s.2
      have h1 : H.B (algebraMap (𝓞 K) K s • v) y' = H.B (algebraMap (𝓞 K) K s • v) y :=
        h' ⟨_, by rw [algebraMap_smul]; exact hs, W.smul_mem _ hv⟩
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [map_sub, smul_right_injective K hc h1, sub_self]
    have h3 := kill_ideal_V0 N hint hF hF' hT hD hd (fun p hp hp' => by
      rw [map_sub, LinearMap.sub_apply, (mem_perp_iff H _ y).1 hyW p hp', sub_zero]
      exact hint _ hy' _ hp) h₁ h₂ h₃
    refine hin _ ((rs (𝓞 K) W).smul_mem _ ((rs (𝓞 K) W).smul_mem _ ((rs (𝓞 K) W).smul_mem _ hyW))) ?_
    have h4 := sub_mem (Submodule.mem_sup_left (Λ.smul_mem γ₁ (Λ.smul_mem γ₂ (Λ.smul_mem γ₃ hy')))) h3
    simpa [smul_sub] using h4
  rw [pow_three, mul_smul, mul_smul, Submodule.smul_le]
  intro γ₁ h₁ m hm
  refine Submodule.smul_induction_on hm (fun γ₂ h₂ m' hm' => ?_)
    (fun a b ha hb => by rw [smul_add]; exact add_mem ha hb)
  exact Submodule.smul_induction_on hm' (fun γ₃ h₃ y hy => key γ₁ h₁ γ₂ h₂ γ₃ h₃ y hy)
    (fun a b ha hb => by rw [smul_add, smul_add]; exact add_mem ha hb)

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → 𝔠 ^ 3 • dual H (latTh N.F N.F' Λ) ≤ latTh N.F N.F' Λ ∧ 𝔠 • dual H N.P0 ≤ N.P0 ∧ 𝔠 • N.P0 ≤ dual H N.P0 := by
  intro K V _ _ _ _ _ _ _ _ H _ r N g Λ _ hΛ 𝔠 _ hc hT hD
  obtain ⟨⟨hU, hF, hF'⟩, -⟩ := hΛ
  have hint : ∀ y ∈ Λ, ∀ x ∈ Λ, H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [← hU.2, mem_dual_iff] at hy
    exact hy.2
  exact ⟨kill_Th N hU hF hF' hT hD, kill_ideal_P0 N hint hF hF' hc hT hD⟩

end GlobalTheory.DegCnt.Kill
