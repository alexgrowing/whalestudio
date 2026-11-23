import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv.EtaFn

section Var

variable {S : Type} [CommRing S] {l : ℕ} [Fact l.Prime] {ϖ x : S}

theorem pow_sub_one_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) (m : ℕ) :
    x ^ l ^ m - 1 ∈ Ideal.span {ϖ ^ l ^ m} := by
  rcases subsingleton_or_nontrivial S with h | h
  · rw [Subsingleton.elim (x ^ l ^ m - 1) 0]
    exact zero_mem _
  · haveI : CharP S l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl
    haveI : ExpChar S l := ExpChar.prime Fact.out
    have e : x ^ l ^ m - 1 = (x - 1) ^ l ^ m := by
      rw [sub_pow_char_pow, one_pow]
    rw [e, ← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hx _

theorem pow_sub_pow_mem (hl : (l : S) = 0) (hx : x - 1 ∈ Ideal.span {ϖ}) {a b m : ℕ}
    (h : a ≡ b [MOD l ^ m]) : x ^ a - x ^ b ∈ Ideal.span {ϖ ^ l ^ m} := by
  have key : ∀ a b : ℕ, a ≤ b → a ≡ b [MOD l ^ m] → x ^ b - x ^ a ∈ Ideal.span {ϖ ^ l ^ m} := by
    intro a b hab h
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hab).1 h
    have hb : b = a + l ^ m * c := by omega
    obtain ⟨d, hd⟩ : x ^ l ^ m - 1 ∣ (x ^ l ^ m) ^ c - 1 := by
      simpa using sub_dvd_pow_sub_pow (x ^ l ^ m) 1 c
    have e : x ^ b - x ^ a = (x ^ l ^ m - 1) * (d * x ^ a) := by
      rw [hb, pow_add, pow_mul]
      linear_combination x ^ a * hd
    rw [e]
    exact Ideal.mul_mem_right _ _ (pow_sub_one_mem hl hx m)
  rcases le_total a b with hab | hab
  · rw [← neg_sub]
    exact neg_mem (key a b hab h)
  · exact key b a hab h.symm

theorem span_pow_le {k n : ℕ} (h : k ≤ n) : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ k} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ h)

theorem le_pow (k : ℕ) : k ≤ l ^ k := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le

theorem exists_lim [IsAdicComplete (Ideal.span {ϖ}) S] (hl : (l : S) = 0)
    (hx : x - 1 ∈ Ideal.span {ϖ}) (a : ℕ → ℕ) (ha : ∀ m m', m ≤ m' → a m' ≡ a m [MOD l ^ m]) :
    ∃ L, ∀ m, L - x ^ a m ∈ Ideal.span {ϖ ^ l ^ m} := by
  obtain ⟨L, hL⟩ := exists_tends (ϖ := ϖ) (fun m => x ^ a m) fun k =>
    ⟨k, fun m hm => span_pow_le (le_pow (l := l) k) (pow_sub_pow_mem hl hx (ha k m hm))⟩
  refine ⟨L, fun m => ?_⟩
  obtain ⟨M, hM⟩ := hL (l ^ m)
  have h1 := hM (max M m) (le_max_left _ _)
  have h2 := pow_sub_pow_mem (ϖ := ϖ) hl hx (ha m (max M m) (le_max_right _ _))
  have := sub_mem h2 h1
  convert this using 1
  ring

theorem eq_of_forall_mem [IsHausdorff (Ideal.span {ϖ}) S] {a b : S}
    (h : ∀ m, a - b ∈ Ideal.span {ϖ ^ l ^ m}) : a = b :=
  Tends.unique (ϖ := ϖ) (x := fun _ => a) (tends_const a)
    fun k => ⟨0, fun _ _ => span_pow_le (le_pow (l := l) k) (h k)⟩

end Var

variable {l : ℕ} [Fact l.Prime]

theorem val_modEq {m m' : ℕ} (h : m ≤ m') (z : ℤ_[l]) :
    (PadicInt.toZModPow m' z).val ≡ (PadicInt.toZModPow m z).val [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val,
    PadicInt.cast_toZModPow _ _ h]

theorem val_add_one (m : ℕ) (z : ℤ_[l]) :
    (PadicInt.toZModPow m (z + 1)).val ≡ (PadicInt.toZModPow m z).val + 1 [MOD l ^ m] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    map_add, map_one, Nat.cast_one]

theorem exists_fn (A : PAlg l) (x : A.A) (hx : x - 1 ∈ Ideal.span {A.pi}) :
    ∃ η : (A.cont ℤ_[l]).A,
      (∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) η - x ^ (PadicInt.toZModPow m z).val ∈
        Ideal.span {A.pi ^ (l ^ m)}) ∧
      ∀ z : ℤ_[l], Hom.f (A.evCont (z + 1)) η = x * Hom.f (A.evCont z) η := by
  haveI hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have hl : (l : A.A) = 0 := A.natCast_l
  choose L hL using fun z : ℤ_[l] => exists_lim (ϖ := A.pi) hl hx
    (fun m => (PadicInt.toZModPow m z).val) (fun m m' h => val_modEq h z)
  refine ⟨⟨L, fun k => ?_⟩, fun m z => hL z m, fun z => ?_⟩
  · have e : (Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L =
        (fun c : ZMod (l ^ k) => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (x ^ c.val)) ∘
          PadicInt.toZModPow k := funext fun z =>
      Ideal.Quotient.eq.2 (span_pow_le (le_pow (l := l) k) (hL z k))
    have h : IsLocallyConstant ((Ideal.Quotient.mk (Ideal.span {A.pi ^ k})) ∘ L) := by
      rw [e]
      exact (GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l k).comp _
    exact h
  · refine eq_of_forall_mem (ϖ := A.pi) (l := l) fun m => ?_
    have h1 := hL (z + 1) m
    have h2 := Ideal.mul_mem_left _ x (hL z m)
    have h3 := pow_sub_pow_mem (ϖ := A.pi) hl hx (val_add_one m z)
    have := add_mem h1 (sub_mem h3 h2)
    change L (z + 1) - x * L z ∈ _
    convert this using 1
    ring

theorem exists_eta (ε : Eps l) : ∃ η : ((base l).cont ℤ_[l]).A,
    (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
    Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  have hx : (base l).s (ε.e 0) - 1 ∈ Ideal.span {(base l).pi} :=
    ((RL.sharp_cong (base l)).2.1 _ 1).1 (by
      rw [ε.sharp_e (base l), map_one, sub_self]
      exact zero_mem _)
  obtain ⟨η, h1, h2⟩ := exists_fn (base l) _ hx
  refine ⟨η, h1, cont_ext fun z => ?_⟩
  have e : Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) = (base l).s (ε.e 0) :=
    RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  rw [map_mul, e]
  exact h2 z

end GlobalTheory.CompanionTheory.ContUniv.EtaFn
