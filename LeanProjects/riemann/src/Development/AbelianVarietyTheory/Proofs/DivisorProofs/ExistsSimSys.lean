import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.TateCompare

variable {p : ℕ} [Fact p.Prime] {D : Datum p}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_zsmul (I : TateIsoO D k Q act e) (n : ℕ) (c : ℤ) (x : D.La) : I.ev n (c • x) = I.ev n x ^ c := by
  let φ : Multiplicative D.La →* Q := MonoidHom.mk' (fun y => I.ev n y.toAdd) (fun a b => I.add n _ _)
  exact map_zpow φ (Multiplicative.ofAdd x) c

theorem ev_nsmul (I : TateIsoO D k Q act e) (n : ℕ) (c : ℕ) (x : D.La) : I.ev n (c • x) = I.ev n x ^ c := by
  rw [← natCast_zsmul, ev_zsmul, zpow_natCast]

theorem ev_eq_iff (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) {x y : D.La} :
    I.ev n x = I.ev n y ↔ ∃ z, x = y + n • z := by
  constructor
  · intro h
    have h₁ : I.ev n y * I.ev n (x - y) = I.ev n y * 1 := by
      rw [← I.add, add_sub_cancel, h, _root_.mul_one]
    obtain ⟨z, hz⟩ := (I.ker n hn hc _).1 (mul_left_cancel h₁)
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  · rintro ⟨z, rfl⟩
    exact I.ev_add_nsmul hn hc _ _

theorem exists_lift (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ g : D.La →+ D.La, 0 < n → n.Coprime p → ∀ y, I₁.ev n (g y) = I₂.ev n y := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hpre : ∀ y, ∃ x, I₁.ev n x = I₂.ev n y := fun y =>
    (I₁.onto n hn hc _).1 ((I₂.onto n hn hc _).2 ⟨y, rfl⟩)
  choose f hf using hpre
  let g : D.La →ₗ[ℤ] D.La := b.constr ℤ (fun i => f (b i))
  refine ⟨g.toAddMonoidHom, fun _ _ y => ?_⟩
  show I₁.ev n (g y) = I₂.ev n y
  have hy : y ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp only [g, Module.Basis.constr_basis, hf]
  | zero =>
    rw [map_zero, (I₁.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩, (I₂.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩]
  | add x y _ _ hx hy => rw [map_add, I₁.add, I₂.add, hx, hy]
  | smul c x _ hx => rw [map_zsmul, ev_zsmul, ev_zsmul, hx]

theorem exists_mult (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ u : ℕ, 0 < n → n.Coprime p → I₁.ζ n ^ u = I₂.ζ n := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have : NeZero n := ⟨hn.ne'⟩
  have h₁ : IsPrimitiveRoot ((I₁.ζ n : kˣ) : k) n := IsPrimitiveRoot.coe_units_iff.2 (I₁.ζ_prim n hn hc)
  have h₂ : ((I₂.ζ n : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (I₂.ζ_prim n hn hc).pow_eq_one, Units.val_one]
  obtain ⟨u, -, hu⟩ := h₁.eq_pow_of_pow_eq_one h₂
  exact ⟨u, fun _ _ => Units.ext (by rw [Units.val_pow_eq_pow_val, hu])⟩

theorem exists_simSys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N M₁ : ℕ), 0 < N → 0 < M₁ → (N * M₁).Coprime p →
    ∀ (k : Type) [Field k] (Q : Type) [Group Q] (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
    (∀ n q q' z z', e n q q' z → e n q q' z' → z = z') → ∀ (I₁ I₂ : TateIsoO D k Q act e),
    (∀ y, I₁.ev N y = I₂.ev N y) →
    ∃ t : SimSys D N (N * M₁), ∀ y, I₂.ev (N * M₁) y = I₁.ev (N * M₁) (t.g (N * M₁) y) := by
  intro p _ D N M₁ hN hM hK k _ Q _ act e he I₁ I₂ hI
  choose g hg using exists_lift I₁ I₂
  choose u hu using exists_mult I₁ I₂
  have hdiv : ∀ {n m : ℕ}, (n * m).Coprime p → n.Coprime p := fun {n m} h =>
    Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) h
  have utow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n] := by
    intro n m hn hm hc
    have h : I₁.ζ n ^ u (n * m) = I₁.ζ n ^ u n := by
      rw [hu n hn (hdiv hc), ← I₂.ζ_pow n m hn hm hc, ← hu _ (Nat.mul_pos hn hm) hc, ← pow_mul, mul_comm (u _) m,
        pow_mul, I₁.ζ_pow n m hn hm hc]
    rwa [pow_eq_pow_iff_modEq, ← (I₁.ζ_prim n hn (hdiv hc)).eq_orderOf] at h
  have gtow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z := by
    intro n m hn hm hc x
    rw [← ev_eq_iff I₁ hn (hdiv hc), hg n hn (hdiv hc), ← I₁.tower n m hn hm hc, hg _ (Nat.mul_pos hn hm) hc,
      I₂.tower n m hn hm hc]
  have sim2 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y,
      (n : ℤ) ∣ 2 * (D.EF (g n x) (g n y) - u n * D.EF x y) := by
    intro n hn hc x y
    have h₁ := I₁.isom n hn hc (g n x) (g n y)
    rw [hg n hn hc, hg n hn hc] at h₁
    have h := he _ _ _ _ _ h₁ (I₂.isom n hn hc x y)
    rw [← hu n hn hc, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I₁.ζ_prim n hn hc).zpow_eq_one_iff_dvd, mul_sub, zpow_sub, h,
      show (u n : ℤ) * (2 * D.EF x y) = 2 * (u n * D.EF x y) by ring, mul_inv_cancel]
  refine ⟨{
    g := g
    u := u
    lin := fun n hn hc c x => ?_
    u_cop := fun n hn hc => ?_
    u_tower := utow
    surj := fun n hn hc x => ?_
    inj := fun n hn hc x z h => ?_
    sim := fun n hn hc x y => ?_
    tower := gtow
    one := fun x => ?_ }, fun y => (hg _ (Nat.mul_pos hN hM) hK y).symm⟩
  · rw [← ev_eq_iff I₁ hn hc, hg n hn hc, I₁.lin, I₂.lin, hg n hn hc]
  · rw [← (I₁.ζ_prim n hn hc).pow_iff_coprime hn, hu n hn hc]
    exact I₂.ζ_prim n hn hc
  · obtain ⟨y, hy⟩ := (I₂.onto n hn hc _).1 ((I₁.onto n hn hc _).2 ⟨x, rfl⟩)
    refine ⟨y, ?_⟩
    rw [← ev_eq_iff I₁ hn hc, hg n hn hc, hy]
  · rw [← I₂.ker n hn hc, ← hg n hn hc, h]
    exact I₁.ev_nsmul_self hn hc z
  · by_cases hp : p = 2
    · subst hp
      have hco : IsCoprime (n : ℤ) 2 := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hc
      exact hco.dvd_of_dvd_mul_left (sim2 n hn hc x y)
    · have hc2 : (n * 2).Coprime p :=
        Nat.Coprime.mul_left hc ((Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp))
      have h := sim2 (n * 2) (by omega) hc2 x y
      obtain ⟨z, hz⟩ := gtow n 2 hn two_pos hc2 x
      obtain ⟨w, hw⟩ := gtow n 2 hn two_pos hc2 y
      obtain ⟨a, ha⟩ := (utow n 2 hn two_pos hc2).dvd
      obtain ⟨c, hcc⟩ := h
      rw [hz, hw] at hcc
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at hcc
      push_cast at hcc
      refine ⟨c - D.EF (g n x) w - D.EF z (g n y) - n * D.EF z w - a * D.EF x y, ?_⟩
      have h2 : (2 : ℤ) ≠ 0 := two_ne_zero
      apply mul_left_cancel₀ h2
      linear_combination hcc - 2 * D.EF x y * ha
  · rw [← ev_eq_iff I₁ hN (hdiv hK), ← I₁.tower N M₁ hN hM hK, hg _ (Nat.mul_pos hN hM) hK,
      I₂.tower N M₁ hN hM hK, hI]

end GlobalTheory.UPel.HT.TateCompare
