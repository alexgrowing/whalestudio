import Formalism.LocalToGlobal.Columns.OcbBEntEntB

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Arith

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ocbS_q_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : ((q : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk P.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hq

theorem ocbS_natCast_eq_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hp : q.Prime) (i : ℕ) :
    ((i : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 ↔ q ∣ i := by
  constructor
  · intro h
    by_contra hn
    have hc : Nat.Coprime q i := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
    have h1 := Nat.gcd_eq_gcd_ab q i
    rw [hc.gcd_eq_one] at h1
    have h2 := congrArg (fun z : ℤ => (z : 𝓞 E ⧸ P.asIdeal)) h1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_one, Int.cast_one] at h2
    rw [ocbS_q_zero hq, h, zero_mul, zero_mul, add_zero] at h2
    exact one_ne_zero h2
  · rintro ⟨j, rfl⟩
    rw [Nat.cast_mul, ocbS_q_zero hq, zero_mul]

theorem ocbS_charP (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hp : q.Prime) : CharP (𝓞 E ⧸ P.asIdeal) q :=
  ⟨fun i => ocbS_natCast_eq_zero hq hp i⟩

theorem ocbS_natCast_surj (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hp : q.Prime) (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q)
    (ρ : 𝓞 E ⧸ P.asIdeal) : ∃ ρ₀ : ℕ, ρ₀ < q ∧ ((ρ₀ : ℕ) : 𝓞 E ⧸ P.asIdeal) = ρ := by
  haveI := ocbS_charP hq hp
  haveI : Fact q.Prime := ⟨hp⟩
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  let f := ZMod.castHom (dvd_refl q) (𝓞 E ⧸ P.asIdeal)
  have hinj : Function.Injective f := f.injective
  have hc : Fintype.card (ZMod q) = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨z, hz⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hc⟩).2 ρ
  refine ⟨z.val, ZMod.val_lt z, ?_⟩
  rw [← hz, ZMod.castHom_apply, ZMod.natCast_val]

theorem ocbS_intAt_natCast (i : ℕ) : IntAt P (i : E) := by
  have h := IntAt.coe P ((i : ℕ) : 𝓞 E)
  rwa [map_natCast] at h

theorem redP_natCast₂ (i : ℕ) : redP P (i : E) = ((i : ℕ) : 𝓞 E ⧸ P.asIdeal) := by
  have h := reduction_coe P ((i : ℕ) : 𝓞 E)
  rwa [map_natCast, map_natCast] at h

theorem ocbS_intAt_div_pow (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime) (a : ℕ) :
    ∀ i : ℕ, IntAt P ((i : E) / (q : E) ^ a) ↔ q ^ a ∣ i := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  induction a with
  | zero =>
    intro i
    simp only [pow_zero, div_one, one_dvd, iff_true]
    exact ocbS_intAt_natCast i
  | succ a ih =>
    intro i
    constructor
    · intro h
      have h1 : IntAt P ((i : E) / (q : E) ^ a) := by
        have e : (i : E) / (q : E) ^ a = (q : E) * ((i : E) / (q : E) ^ (a + 1)) := by
          rw [pow_succ]
          field_simp
        rw [e]
        exact (ciIntAt_q (P := P) (q := q)).mul h
      obtain ⟨j, rfl⟩ := (ih i).1 h1
      have h2 : IntAt P ((j : E) / (q : E)) := by
        have e : (((q ^ a * j : ℕ) : E)) / (q : E) ^ (a + 1) = (j : E) / (q : E) := by
          push_cast
          rw [pow_succ]
          field_simp
        rwa [e] at h
      have h3 := (ciRed_of_div hq hq0 h2).2
      rw [redP_natCast₂] at h3
      obtain ⟨l, rfl⟩ := (ocbS_natCast_eq_zero hq hp j).1 h3
      exact ⟨l, by ring⟩
    · rintro ⟨j, rfl⟩
      have e : (((q ^ (a + 1) * j : ℕ) : E)) / (q : E) ^ (a + 1) = (j : E) := by
        push_cast
        field_simp
      rw [e]
      exact ocbS_intAt_natCast j

open Classical in

theorem ocbS_card_res (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hp : q.Prime) (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {M : ℕ}
    (hM : 1 ≤ M) (ρ : 𝓞 E ⧸ P.asIdeal) :
    ((Finset.range (q ^ M)).filter (fun i => ((i : ℕ) : 𝓞 E ⧸ P.asIdeal) = ρ)).card = q ^ (M - 1) := by
  classical
  obtain ⟨ρ₀, hρ₀, rfl⟩ := ocbS_natCast_surj hq hp hcard ρ
  haveI := ocbS_charP hq hp
  have key : ∀ i : ℕ, ((i : ℕ) : 𝓞 E ⧸ P.asIdeal) = ((ρ₀ : ℕ) : 𝓞 E ⧸ P.asIdeal) ↔ i % q = ρ₀ := by
    intro i
    rw [CharP.natCast_eq_natCast (𝓞 E ⧸ P.asIdeal) q, Nat.ModEq, Nat.mod_eq_of_lt hρ₀]
  have hq1 : 0 < q := hp.pos
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  symm
  rw [← Finset.card_range (q ^ M')]
  refine Finset.card_bij (fun j _ => ρ₀ + q * j) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range, key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ₀]
    refine ⟨?_, rfl⟩
    calc ρ₀ + q * j < q + q * j := by omega
      _ = q * (j + 1) := by ring
      _ ≤ q * q ^ M' := Nat.mul_le_mul (le_refl q) hj
      _ = q ^ (M' + 1) := by ring
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hq1 (Nat.add_left_cancel h)
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range, key] at hi
    refine ⟨i / q, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hq1]
      calc i < q ^ (M' + 1) := hi.1
        _ = q ^ M' * q := by ring
    · have := Nat.mod_add_div i q
      rw [hi.2] at this
      exact this

open Classical in

theorem ocbS_card_vals (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {A B d : ℕ} (hd : d ≤ A) (hB : 1 ≤ B) (ρ : 𝓞 E ⧸ P.asIdeal) :
    ((LocE.valsQ E q A B).filter (fun v => IntAt P ((q : E) ^ d * v) ∧ redP P ((q : E) ^ d * v) = ρ)).card = q ^ (B + d - 1) := by
  classical
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hsplit : ∀ i : ℕ, (q : E) ^ d * ((i : E) / (q : E) ^ A) = (i : E) / (q : E) ^ (A - d) := by
    intro i
    have e : (q : E) ^ A = (q : E) ^ (A - d) * (q : E) ^ d := by rw [← pow_add, Nat.sub_add_cancel hd]
    rw [e]
    field_simp
  have hinj : Function.Injective (fun i : ℕ => ((i : ℕ) : E) / (q : E) ^ A) := by
    intro a b h
    simp only at h
    have := (div_left_inj' (pow_ne_zero A hq0)).1 h
    exact_mod_cast this
  have e2 : ∀ j : ℕ, (((q ^ (A - d) * j : ℕ) : E)) / (q : E) ^ (A - d) = (j : E) := by
    intro j
    push_cast
    field_simp
  unfold LocE.valsQ
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
  rw [← ocbS_card_res hq hp hcard (M := B + d) (by omega) ρ]
  symm
  refine Finset.card_bij (fun j _ => q ^ (A - d) * j) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    simp only [hsplit]
    rw [e2, redP_natCast₂]
    refine ⟨?_, ocbS_intAt_natCast j, hj.2⟩
    calc q ^ (A - d) * j < q ^ (A - d) * q ^ (B + d) := mul_lt_mul_of_pos_left hj.1 (pow_pos hp.pos _)
      _ = q ^ (A + B) := by rw [← pow_add]; congr 1; omega
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    simp only [hsplit] at hi
    obtain ⟨hlt, hint, hred⟩ := hi
    obtain ⟨j, rfl⟩ := (ocbS_intAt_div_pow hq hu hp (A - d) i).1 hint
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range]
    rw [e2, redP_natCast₂] at hred
    refine ⟨?_, hred⟩
    have : q ^ (A - d) * j < q ^ (A - d) * q ^ (B + d) := by
      calc q ^ (A - d) * j < q ^ (A + B) := hlt
        _ = q ^ (A - d) * q ^ (B + d) := by rw [← pow_add]; congr 1; omega
    exact Nat.lt_of_mul_lt_mul_left this

end Arith

theorem ocbS_sum_pi_fiber {ι α β M : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] [Fintype β] [DecidableEq β]
    [CommSemiring M] (V : ι → Finset α) (r : ι → α → β) (W : (ι → β) → M) :
    ∑ t ∈ Fintype.piFinset V, W (fun i => r i (t i)) =
      ∑ ω : ι → β, W ω * ∏ i, (((V i).filter (fun a => r i a = ω i)).card : M) := by
  classical
  rw [← Finset.sum_fiberwise (Fintype.piFinset V) (fun t i => r i (t i)) (fun t => W (fun i => r i (t i)))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hs : ∀ t ∈ (Fintype.piFinset V).filter (fun t => (fun i => r i (t i)) = ω), W (fun i => r i (t i)) = W ω := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [ht.2]
  rw [Finset.sum_congr rfl hs, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hpi : (Fintype.piFinset V).filter (fun t => (fun i => r i (t i)) = ω) =
      Fintype.piFinset (fun i => (V i).filter (fun a => r i a = ω i)) := by
    ext t
    simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact ⟨h1 i, h2 i⟩
    · intro h
      exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [hpi, Fintype.card_piFinset, Nat.cast_prod]

section Entries

variable {k : Type} [CommRing k]

theorem ocbS_eN_single {N s : ℕ} (hs : s < N) : Loc.eN k N s = Pi.single (⟨s, hs⟩ : Fin N) 1 := by
  funext j
  unfold Loc.eN
  by_cases h : j.1 = s
  · rw [if_pos h, Pi.single_apply, if_pos (Fin.ext h)]
  · rw [if_neg h, Pi.single_apply, if_neg (fun e => h (congrArg Fin.val e))]

theorem ocbS_atN_of_lt {N l : ℕ} (v : Fin N → k) (hl : l < N) : Loc.atN v l = v ⟨l, hl⟩ := by
  unfold Loc.atN
  rw [dif_pos hl]

theorem ocbS_atN_toLin' {a b : ℕ} (M : Matrix (Fin b) (Fin a) k) {l s : ℕ} (hl : l < b) (hs : s < a) :
    Loc.atN (Matrix.toLin' M (Loc.eN k a s)) l = M ⟨l, hl⟩ ⟨s, hs⟩ := by
  rw [ocbS_eN_single hs, Matrix.toLin'_apply, ocbS_atN_of_lt _ hl]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem ocbS_atN_toMatrix' {a b : ℕ} (f : (Fin a → k) →ₗ[k] (Fin b → k)) (i : Fin b) (j : Fin a) :
    LinearMap.toMatrix' f i j = Loc.atN (f (Loc.eN k a j.1)) i.1 := by
  rw [LinearMap.toMatrix'_apply, ocbS_eN_single j.2, ocbS_atN_of_lt _ i.2]

theorem ocbS_atN_comp {a b d : ℕ} (g : (Fin b → k) →ₗ[k] (Fin d → k)) (y : (Fin a → k) →ₗ[k] (Fin b → k)) {l s : ℕ}
    (hl : l < d) (hs : s < a) :
    Loc.atN ((g ∘ₗ y) (Loc.eN k a s)) l = ∑ m : Fin b, Loc.atN (g (Loc.eN k b m.1)) l * Loc.atN (y (Loc.eN k a s)) m.1 := by
  rw [show Loc.atN ((g ∘ₗ y) (Loc.eN k a s)) l = LinearMap.toMatrix' (g ∘ₗ y) ⟨l, hl⟩ ⟨s, hs⟩ from
    (ocbS_atN_toMatrix' (g ∘ₗ y) ⟨l, hl⟩ ⟨s, hs⟩).symm, LinearMap.toMatrix'_comp, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ocbS_atN_toMatrix' g, ocbS_atN_toMatrix' y]

theorem coord_unipotentExtension_basisVec {n' c' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : Loc.FC n' c' n c → k) {l s : ℕ}
    (hl : l < n + c) (hs : s < n' + c') :
    Loc.atN (Loc.xx1 xj t (Loc.eN k (n' + c') s)) l =
      if hf : Loc.IsFree n' n c l s then t ⟨(⟨l, hl⟩, ⟨s, hs⟩), hf⟩
      else if s < n' then (if l < n then Loc.atN (xj (Loc.eN k n' s)) l else 0)
      else if l = n + (s - n') then 1 else 0 := by
  unfold Loc.xx1
  rw [ocbS_atN_toLin' _ hl hs]
  simp only [Matrix.of_apply, ocbS_atN_toMatrix', dite_eq_ite]

end Entries

def ocbD (n' n l s : ℕ) : ℕ := (s - n' + 1) - (if l < n then 0 else l - n + 1)

theorem ocbS_scE_free {n' n c l s : ℕ} (hl : l < n + c) (hs : s < n' + (c + 1)) (hf : Loc.IsFree n' n c l s) :
    LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l = (ocbD n' n l s : ℤ) ∧
      1 ≤ ocbD n' n l s ∧ ocbD n' n l s ≤ c + 1 := by
  unfold Loc.IsFree at hf
  obtain ⟨u, rfl⟩ : ∃ u, s = n' + u := ⟨s - n', by omega⟩
  have hs' : ¬ n' + u < n' := by omega
  have h1 : LocE.scE n' (fun i => i + 1) (n' + u) = ((u + 1 : ℕ) : ℤ) := by
    unfold LocE.scE
    rw [if_neg hs']
    simp
  by_cases hln : l < n
  · have h2 : LocE.scE n (fun i => i + 1) l = 0 := by
      unfold LocE.scE
      rw [if_pos hln]
    have h3 : ocbD n' n l (n' + u) = u + 1 := by
      unfold ocbD
      rw [if_pos hln]
      omega
    rw [h1, h2, h3]
    refine ⟨by push_cast; ring, by omega, by omega⟩
  · obtain ⟨v, rfl⟩ : ∃ v, l = n + v := ⟨l - n, by omega⟩
    have h2 : LocE.scE n (fun i => i + 1) (n + v) = ((v + 1 : ℕ) : ℤ) := by
      unfold LocE.scE
      rw [if_neg hln]
      simp
    have h3 : ocbD n' n (n + v) (n' + u) = u - v := by
      unfold ocbD
      rw [if_neg hln]
      omega
    have hvu : v < u := by omega
    rw [h1, h2, h3]
    refine ⟨?_, by omega, by omega⟩
    rw [Nat.cast_sub hvu.le]
    push_cast
    ring

section EntE

variable {E : Type} [Field E] [NumberField E]

theorem scaledEntry_unipotentExtension {n' n c q : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : Loc.FC n' (c + 1) n c → E) {l s : ℕ}
    (hl : l < n + c) (hs : s < n' + (c + 1)) :
    ocbBEnt n' n q (Loc.xx1 xj t) l s =
      if hf : Loc.IsFree n' n c l s then t ⟨(⟨l, hl⟩, ⟨s, hs⟩), hf⟩ * (q : E) ^ ocbD n' n l s
      else if s < n' then (if l < n then Loc.atN (xj (Loc.eN E n' s)) l else 0)
      else if l = n + (s - n') then 1 else 0 := by
  unfold ocbBEnt
  rw [coord_unipotentExtension_basisVec xj t hl hs]
  by_cases hf : Loc.IsFree n' n c l s
  · rw [dif_pos hf, dif_pos hf, (ocbS_scE_free hl hs hf).1, zpow_natCast]
  · rw [dif_neg hf, dif_neg hf]
    by_cases hs' : s < n'
    · rw [if_pos hs']
      by_cases hln : l < n
      · rw [if_pos hln]
        unfold LocE.scE
        rw [if_pos hs', if_pos hln, sub_zero, zpow_zero, mul_one]
      · rw [if_neg hln, zero_mul]
    · rw [if_neg hs']
      by_cases he : l = n + (s - n')
      · rw [if_pos he]
        unfold LocE.scE
        rw [if_neg hs', if_neg (show ¬ l < n by omega), he]
        simp
      · rw [if_neg he, zero_mul]

theorem ocbS_chArg {n' c' n c q : ℕ} (hq0 : (q : E) ≠ 0) (y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    Loc.chArg y = (∑ i ∈ Finset.range c, ocbBEnt n' n q y (n + i) (n' + i + 1)) / (q : E) := by
  unfold Loc.chArg ocbBEnt
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : LocE.scE n' (fun i => i + 1) (n' + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
    unfold LocE.scE
    rw [if_neg (by omega), if_neg (by omega)]
    push_cast
    omega
  rw [e, zpow_one]
  field_simp

end EntE

section Main

variable {E K L : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field L] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def ocbXInt (P : HeightOneSpectrum (𝓞 E)) {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : Prop :=
  ∀ l s, l < n → s < n' → IntAt P (Loc.atN (xj (Loc.eN E n' s)) l)

def ocbXRed (P : HeightOneSpectrum (𝓞 E)) {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (xbj : (Fin n' → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin n → 𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ l s, l < n → s < n' → Loc.atN (xbj (Loc.eN _ n' s)) l = redP P (Loc.atN (xj (Loc.eN E n' s)) l)

def ocbExp (n' c n : ℕ) : ℕ := ∑ f : Loc.FC n' (c + 1) n c, (ocbD n' n f.1.1.1 f.1.2.1 - 1)

theorem firstUnfolding_eq_zero_of_not_integral {n' c' n c : ℕ} (hc' : c' = c + 1) (Ψ : Loc.SF E K (n' + c') (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (psi : E → K) (vals : Finset E) (wt : K) (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (hx : ¬ ocbXInt P xj) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Ψ xj = 0 := by
  subst hc'
  unfold Loc.E1
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  have h0 : Ψ (Loc.xx1 xj t) = 0 := by
    by_contra hne
    apply hx
    intro l s hl hs
    have h1 := hsupp _ hne l s (by omega) (by omega)
    rw [scaledEntry_unipotentExtension xj t (by omega) (by omega), dif_neg (fun hf => by unfold Loc.IsFree at hf; omega),
      if_pos hs, if_pos hl] at h1
    exact h1
  rw [h0, zero_mul]

theorem firstUnfolding_reduction_eq (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (xbj : (Fin n' → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin n → 𝓞 E ⧸ P.asIdeal)) (hx : ocbXInt P xj)
    (hxr : ocbXRed P xj xbj) :
    σ (Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj) =
      (q : L) ^ ocbExp n' c n *
        Loc.E1 (k := 𝓞 E ⧸ P.asIdeal) (n' := n') (c' := c + 1) (n := n) (c := c) ψ₀ (@Finset.univ _ (resFintype P)) 1 Ψr xbj := by
  subst hc'
  classical
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := resFintype P
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hqL : (q : L) ≠ 0 := by
    rw [← map_natCast σ]
    exact (map_ne_zero σ).2 (Nat.cast_ne_zero.2 hp.ne_zero)
  let r : Loc.FC n' (c + 1) n c → E → Option (𝓞 E ⧸ P.asIdeal) := fun f v =>
    if IntAt P ((q : E) ^ ocbD n' n f.1.1.1 f.1.2.1 * v) then some (redP P ((q : E) ^ ocbD n' n f.1.1.1 f.1.2.1 * v)) else none
  let G : (Loc.FC n' (c + 1) n c → 𝓞 E ⧸ P.asIdeal) → L := fun ρ => Ψr (Loc.xx1 xbj ρ) * ψ₀ (-Loc.chArg (Loc.xx1 xbj ρ))
  let W : (Loc.FC n' (c + 1) n c → Option (𝓞 E ⧸ P.asIdeal)) → L := fun ω =>
    if h : ∀ f, (ω f).isSome then G (fun f => (ω f).get (h f)) else 0
  have hterm : ∀ t : Loc.FC n' (c + 1) n c → E,
      σ (Ψ (Loc.xx1 xj t) * psi (-Loc.chArg (Loc.xx1 xj t))) = W (fun f => r f (t f)) := by
    intro t
    by_cases hall : ∀ f : Loc.FC n' (c + 1) n c, IntAt P ((q : E) ^ ocbD n' n f.1.1.1 f.1.2.1 * t f)
    · obtain ⟨ρ, hρ⟩ : ∃ ρ : Loc.FC n' (c + 1) n c → 𝓞 E ⧸ P.asIdeal,
          ρ = fun f => redP P ((q : E) ^ ocbD n' n f.1.1.1 f.1.2.1 * t f) := ⟨_, rfl⟩
      have hr : (fun f => r f (t f)) = fun f => some (ρ f) := by
        funext f
        rw [hρ]
        exact if_pos (hall f)
      rw [hr]
      have hW : W (fun f => some (ρ f)) = G ρ := by
        simp only [W]
        exact dif_pos (fun _ => rfl)
      rw [hW]
      have hint : ∀ l s, l < n + c → s < n' + (c + 1) → IntAt P (ocbBEnt n' n q (Loc.xx1 xj t) l s) := by
        intro l s hl hs
        rw [scaledEntry_unipotentExtension xj t hl hs]
        by_cases hf : Loc.IsFree n' n c l s
        · rw [dif_pos hf, mul_comm]
          exact hall ⟨(⟨l, hl⟩, ⟨s, hs⟩), hf⟩
        · rw [dif_neg hf]
          by_cases hs' : s < n'
          · rw [if_pos hs']
            by_cases hln : l < n
            · rw [if_pos hln]
              exact hx l s hln hs'
            · rw [if_neg hln]
              exact ciIntAt_zero
          · rw [if_neg hs']
            by_cases he : l = n + (s - n')
            · rw [if_pos he]
              exact ciIntAt_one
            · rw [if_neg he]
              exact ciIntAt_zero
      have hrd : ∀ l s, l < n + c → s < n' + (c + 1) →
          Loc.atN (Loc.xx1 xbj ρ (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q (Loc.xx1 xj t) l s) := by
        intro l s hl hs
        rw [scaledEntry_unipotentExtension xj t hl hs, coord_unipotentExtension_basisVec xbj ρ hl hs]
        by_cases hf : Loc.IsFree n' n c l s
        · rw [dif_pos hf, dif_pos hf, hρ]
          exact congrArg (redP P) (mul_comm _ _)
        · rw [dif_neg hf, dif_neg hf]
          by_cases hs' : s < n'
          · rw [if_pos hs', if_pos hs']
            by_cases hln : l < n
            · rw [if_pos hln, if_pos hln]
              exact hxr l s hln hs'
            · rw [if_neg hln, if_neg hln]
              exact redP_zero.symm
          · rw [if_neg hs', if_neg hs']
            by_cases he : l = n + (s - n')
            · rw [if_pos he, if_pos he]
              exact redP_one.symm
            · rw [if_neg he, if_neg he]
              exact redP_zero.symm
      rw [map_mul, hred _ _ hint hrd]
      simp only [G]
      congr 1
      have hS : ∀ i ∈ Finset.range c, IntAt P (ocbBEnt n' n q (Loc.xx1 xj t) (n + i) (n' + i + 1)) :=
        fun i hi => hint _ _ (by rw [Finset.mem_range] at hi; omega) (by rw [Finset.mem_range] at hi; omega)
      rw [ocbS_chArg hq0, ← neg_div, hpsi _ (ciIntAt_neg (ciIntAt_sum _ _ hS)), redP_neg (ciIntAt_sum _ _ hS),
        redP_sum _ _ hS]
      unfold Loc.chArg
      congr 2
      refine Finset.sum_congr rfl fun i hi => (hrd _ _ ?_ ?_).symm
      · rw [Finset.mem_range] at hi
        omega
      · rw [Finset.mem_range] at hi
        omega
    · push Not at hall
      obtain ⟨f, hf⟩ := hall
      have hW : W (fun f => r f (t f)) = 0 := by
        simp only [W]
        rw [dif_neg]
        intro h
        have h1 := h f
        simp [r, hf] at h1
      rw [hW]
      have h0 : Ψ (Loc.xx1 xj t) = 0 := by
        by_contra hne
        have h1 := hsupp _ hne f.1.1.1 f.1.2.1 f.1.1.2 f.1.2.2
        rw [scaledEntry_unipotentExtension xj t f.1.1.2 f.1.2.2, dif_pos f.2, mul_comm] at h1
        exact hf h1
      rw [h0, zero_mul, map_zero]
  have hcardf : ∀ (f : Loc.FC n' (c + 1) n c) (ρ : 𝓞 E ⧸ P.asIdeal),
      ((((LocE.valsQ E q A B).filter (fun v => r f v = some ρ)).card : ℕ) : L) =
        (q : L) ^ (B + ocbD n' n f.1.1.1 f.1.2.1 - 1) := by
    intro f ρ
    have hd := ocbS_scE_free f.1.1.2 f.1.2.2 f.2
    have e : (LocE.valsQ E q A B).filter (fun v => r f v = some ρ) =
        (LocE.valsQ E q A B).filter (fun v => IntAt P ((q : E) ^ ocbD n' n f.1.1.1 f.1.2.1 * v) ∧
          redP P ((q : E) ^ ocbD n' n f.1.1.1 f.1.2.1 * v) = ρ) := by
      refine Finset.filter_congr fun v _ => ?_
      simp only [r]
      split_ifs with h
      · simp [h]
      · simp [h]
    rw [e, ocbS_card_vals hq hu hp hcard (le_trans hd.2.2 hA) hB ρ, Nat.cast_pow]
  have hsumω : ∑ ω : Loc.FC n' (c + 1) n c → Option (𝓞 E ⧸ P.asIdeal),
      W ω * ∏ f, ((((LocE.valsQ E q A B).filter (fun v => r f v = ω f)).card : ℕ) : L) =
      ∑ ρ : Loc.FC n' (c + 1) n c → 𝓞 E ⧸ P.asIdeal,
        G ρ * ∏ f : Loc.FC n' (c + 1) n c, (q : L) ^ (B + ocbD n' n f.1.1.1 f.1.2.1 - 1) := by
    rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.image (fun ρ : Loc.FC n' (c + 1) n c → 𝓞 E ⧸ P.asIdeal => fun f => some (ρ f)))) ?_]
    · rw [Finset.sum_image (fun ρ₁ _ ρ₂ _ h => funext fun f => Option.some_injective _ (congrFun h f))]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      have hW : W (fun f => some (ρ f)) = G ρ := by
        simp only [W]
        exact dif_pos (fun _ => rfl)
      rw [hW]
      congr 1
      exact Finset.prod_congr rfl fun f _ => hcardf f (ρ f)
    · intro ω _ hω
      simp only [W]
      rw [dif_neg, zero_mul]
      intro h
      apply hω
      rw [Finset.mem_image]
      exact ⟨fun f => (ω f).get (h f), Finset.mem_univ _, funext fun f => Option.some_get (h f)⟩
  have hexp : ∑ f : Loc.FC n' (c + 1) n c, (B + ocbD n' n f.1.1.1 f.1.2.1 - 1) =
      B * Fintype.card (Loc.FC n' (c + 1) n c) + ocbExp n' c n := by
    unfold ocbExp
    rw [show B * Fintype.card (Loc.FC n' (c + 1) n c) = ∑ _f : Loc.FC n' (c + 1) n c, B by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm], ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have := (ocbS_scE_free f.1.1.2 f.1.2.2 f.2).2.1
    omega
  unfold Loc.E1
  rw [map_mul, map_pow, map_sum, Finset.sum_congr rfl (fun t _ => hterm t),
    ocbS_sum_pi_fiber (fun _ => LocE.valsQ E q A B) r W]
  rw [hsumω, Fintype.piFinset_univ, one_pow, one_mul, ← Finset.sum_mul, Finset.prod_pow_eq_pow_sum, hexp, map_inv₀, map_pow,
    map_natCast, inv_pow, ← pow_mul, pow_add]
  have hne : (q : L) ^ (B * Fintype.card (Loc.FC n' (c + 1) n c)) ≠ 0 := pow_ne_zero _ hqL
  have hG : ∑ ρ : Loc.FC n' (c + 1) n c → 𝓞 E ⧸ P.asIdeal, G ρ =
      ∑ ρ : Loc.FC n' (c + 1) n c → 𝓞 E ⧸ P.asIdeal, Ψr (Loc.xx1 xbj ρ) * ψ₀ (-Loc.chArg (Loc.xx1 xbj ρ)) := rfl
  rw [hG]
  generalize (∑ ρ : Loc.FC n' (c + 1) n c → 𝓞 E ⧸ P.asIdeal, Ψr (Loc.xx1 xbj ρ) * ψ₀ (-Loc.chArg (Loc.xx1 xbj ρ))) = S
  generalize (q : L) ^ (B * Fintype.card (Loc.FC n' (c + 1) n c)) = Z at hne ⊢
  rw [mul_comm S, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Main

end Formalism.L2.Col
