import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit

variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

theorem finite_of_resAlg (h : ResAlg E τ q ε) : Finite E := by
  apply Nat.finite_of_card_ne_zero
  rw [h.card]
  have := h.one_lt
  exact pow_ne_zero 2 (by omega)

theorem nontrivial_of_resAlg (h : ResAlg E τ q ε) : Nontrivial E := by
  have := finite_of_resAlg h
  rw [← Finite.one_lt_card_iff_nontrivial, h.card]
  have := h.one_lt
  nlinarith

theorem card_fixed (h : ResAlg E τ q ε) : Nat.card {x : E // τ x = x} = q := by
  have := finite_of_resAlg h
  obtain ⟨u, hu, hb⟩ := h.basis
  have hbij : Function.Bijective
      (fun p : {x : E // τ x = x} × {x : E // τ x = x} => (p.1 : E) + p.2 * u) := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      simp only at hxy
      have h2 := congrArg τ hxy
      simp only [map_add, map_mul, hx, hy, hx', hy'] at h2
      have hyy : y = y' := by
        have h3 : (y - y') * (u - τ u) = 0 := by linear_combination hxy - h2
        rw [hu.mul_left_eq_zero, sub_eq_zero] at h3
        exact h3
      subst hyy
      have hxx : x = x' := by linear_combination hxy
      subst hxx
      rfl
    · intro a
      obtain ⟨x, y, hx, hy, rfl⟩ := hb a
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, h.card] at hc
  have h4 : Nat.card {x : E // τ x = x} ^ 2 = q ^ 2 := by rw [sq]; exact hc
  exact Nat.pow_left_injective (by norm_num) h4

theorem card_fixed_ne (h : ResAlg E τ q ε) : Nat.card {x : E // τ x = x ∧ x ≠ 0} = q - 1 := by
  classical
  have := finite_of_resAlg h
  have e1 : Nat.card {x : E // τ x = x ∧ x ≠ 0} =
      Nat.card {y : {x : E // τ x = x} // y ≠ ⟨0, map_zero τ⟩} := Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h0 => x.2.2 (congrArg Subtype.val h0)⟩
      invFun := fun y => ⟨y.1.1, y.1.2, fun h0 => y.2 (Subtype.ext h0)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 := Nat.card_congr (Equiv.optionSubtypeNe (⟨0, map_zero τ⟩ : {x : E // τ x = x}))
  rw [Finite.card_option, card_fixed h] at e2
  rw [e1, ← e2, Nat.add_sub_cancel]

theorem fixed_inv {s v : E} (hs : τ s = s) (hv : s * v = 1) : τ v = v := by
  have h2 : s * τ v = 1 := by
    have h3 := congrArg τ hv
    rwa [map_mul, map_one, hs] at h3
  calc τ v = (v * s) * τ v := by rw [mul_comm v s, hv, one_mul]
    _ = v := by rw [mul_assoc, h2, mul_one]

theorem exists_idem (h : ResAlg E τ q ε) (hnf : ¬ IsField E) :
    ∃ e : E, e + τ e = 1 ∧ e * τ e = 0 := by
  have := nontrivial_of_resAlg h
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra hc
    push Not at hc
    exact hnf ⟨exists_pair_ne E, mul_comm, fun {a} ha => by
      obtain ⟨b, hb⟩ := (hc a ha).exists_right_inv
      exact ⟨b, hb⟩⟩
  have haτ : a * τ a = 0 := by
    by_contra hne
    apply hau
    have hfix : τ (a * τ a) = a * τ a := by rw [map_mul, h.inv, mul_comm]
    exact isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne)
  have hw : ∃ w : E, a * w + τ (a * w) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 := hc 1
    have h2 := hc u
    rw [mul_one] at h1
    apply ha0
    have h3 : a * (u - τ u) = 0 := by
      rw [map_mul] at h2
      linear_combination h2 - τ u * h1
    exact hu.mul_left_eq_zero.1 h3
  obtain ⟨w, hw⟩ := hw
  have hTfix : τ (a * w + τ (a * w)) = a * w + τ (a * w) := by rw [map_add, h.inv, add_comm]
  obtain ⟨s, hs⟩ := (h.fixedUnit _ hTfix hw).exists_right_inv
  have hsf : τ s = s := fixed_inv hTfix hs
  refine ⟨a * w * s, ?_, ?_⟩
  · rw [map_mul, hsf]
    linear_combination hs
  · rw [map_mul, hsf, map_mul]
    linear_combination (w * τ w * s * s) * haτ

theorem card_fibre_split (h : ResAlg E τ q ε) (hnf : ¬ IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q - 1 := by
  obtain ⟨e, he1, he0⟩ := exists_idem h hnf
  have hτe : τ (τ e) = e := h.inv e
  have hee : e * e = e := by linear_combination e * he1 - he0
  have hff : τ e * τ e = τ e := by linear_combination τ e * he1 - he0
  have hiso : ∀ α : E, ∃ s : E, τ α = α → α ≠ 0 → α * s = 1 ∧ τ s = s := by
    intro α
    by_cases hc : τ α = α ∧ α ≠ 0
    · obtain ⟨s, hs⟩ := (h.fixedUnit α hc.1 hc.2).exists_right_inv
      exact ⟨s, fun _ _ => ⟨hs, fixed_inv hc.1 hs⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hiso
  have hfixA : ∀ a : E, τ (a * e + τ a * τ e) = a * e + τ a * τ e := by
    intro a
    simp only [map_add, map_mul, h.inv]
    ring
  have hneA : ∀ a : E, a * τ a = t → a * e + τ a * τ e ≠ 0 := by
    intro a ha hα
    apply t0
    have h1 : a * e = 0 := by linear_combination e * hα - a * hee - τ a * he0
    have h2 : τ a * τ e = 0 := by linear_combination τ e * hα - τ a * hff - a * he0
    linear_combination -ha + τ a * h1 + a * h2 - a * τ a * he1
  rw [← card_fixed_ne h]
  exact Nat.card_congr
    { toFun := fun a => ⟨a.1 * e + τ a.1 * τ e, hfixA a.1, hneA a.1 a.2⟩
      invFun := fun x => ⟨x.1 * e + t * s x.1 * τ e, by
        obtain ⟨hs1, hs2⟩ := hs x.1 x.2.1 x.2.2
        simp only [map_add, map_mul, x.2.1, ht, hs2, hτe]
        linear_combination (x.1 ^ 2 + t ^ 2 * s x.1 ^ 2) * he0 + x.1 * t * s x.1 * hee +
          x.1 * t * s x.1 * hff + x.1 * t * s x.1 * he1 + t * hs1⟩
      left_inv := fun a => by
        obtain ⟨hs1, -⟩ := hs _ (hfixA a.1) (hneA a.1 a.2)
        have ha := a.2
        apply Subtype.ext
        dsimp only
        linear_combination a.1 * hee + (τ a.1 - a.1 ^ 2 * s (a.1 * e + τ a.1 * τ e)) * he0 + a.1 * he1 -
          s (a.1 * e + τ a.1 * τ e) * τ e * ha + a.1 * τ e * hs1 -
          a.1 * τ a.1 * s (a.1 * e + τ a.1 * τ e) * hff
      right_inv := fun x => by
        obtain ⟨-, hs2⟩ := hs x.1 x.2.1 x.2.2
        apply Subtype.ext
        dsimp only
        simp only [map_add, map_mul, x.2.1, ht, hs2, hτe]
        linear_combination x.1 * hee + 2 * t * s x.1 * he0 + x.1 * hff + x.1 * he1 }

theorem isUnit_of_ne (hf : IsField E) {a : E} (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel ha
  exact IsUnit.of_mul_eq_one b hb

theorem card_units (h : ResAlg E τ q ε) (hf : IsField E) : Nat.card Eˣ = q ^ 2 - 1 := by
  classical
  have := finite_of_resAlg h
  have := nontrivial_of_resAlg h
  have e1 : Nat.card Eˣ = Nat.card {a : E // a ≠ 0} := Nat.card_congr
    { toFun := fun u => ⟨u, u.ne_zero⟩
      invFun := fun a => (isUnit_of_ne hf a.2).unit
      left_inv := fun u => Units.ext rfl
      right_inv := fun a => rfl }
  have e2 := Nat.card_congr (Equiv.optionSubtypeNe (0 : E))
  rw [Finite.card_option, h.card] at e2
  rw [e1, ← e2, Nat.add_sub_cancel]

def tauU (τ : E →+* E) : Eˣ →* Eˣ := Units.map (τ : E →* E)

def ratioU (τ : E →+* E) : Eˣ →* Eˣ := MonoidHom.id _ / tauU τ

def normU (τ : E →+* E) : Eˣ →* Eˣ := MonoidHom.id _ * tauU τ

theorem ratioU_apply (b : Eˣ) : ratioU τ b = b / tauU τ b := rfl

theorem normU_apply (b : Eˣ) : normU τ b = b * tauU τ b := rfl

theorem coe_tauU (b : Eˣ) : ((tauU τ b : Eˣ) : E) = τ b := rfl

theorem tauU_tauU (h : ResAlg E τ q ε) (b : Eˣ) : tauU τ (tauU τ b) = b := by
  apply Units.ext
  rw [coe_tauU, coe_tauU, h.inv]

theorem ratioU_eq_iff {c a : Eˣ} : ratioU τ c = a ↔ (c : E) = a * τ c := by
  rw [ratioU_apply, div_eq_iff_eq_mul, Units.ext_iff, Units.val_mul, coe_tauU]

theorem mem_ker_normU {k : Eˣ} : k ∈ (normU τ).ker ↔ (k : E) * τ k = 1 := by
  rw [MonoidHom.mem_ker, normU_apply, Units.ext_iff, Units.val_mul, coe_tauU, Units.val_one]

theorem mem_ker_ratioU {k : Eˣ} : k ∈ (ratioU τ).ker ↔ (k : E) = τ k := by
  rw [MonoidHom.mem_ker, ratioU_eq_iff, Units.val_one, one_mul]

theorem card_ker_ratioU (h : ResAlg E τ q ε) : Nat.card (ratioU τ).ker = q - 1 := by
  have := nontrivial_of_resAlg h
  rw [← card_fixed_ne h]
  exact Nat.card_congr
    { toFun := fun k => ⟨((k : Eˣ) : E), (mem_ker_ratioU.1 k.2).symm, (k : Eˣ).ne_zero⟩
      invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, mem_ker_ratioU.2 x.2.1.symm⟩
      left_inv := fun k => Subtype.ext (Units.ext rfl)
      right_inv := fun x => rfl }

theorem range_ratioU (h : ResAlg E τ q ε) (hf : IsField E) :
    (ratioU τ).range = (normU τ).ker := by
  have := nontrivial_of_resAlg h
  ext k
  constructor
  · intro hk
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hk
    rw [MonoidHom.mem_ker, normU_apply, ratioU_apply, map_div, tauU_tauU h]
    simp [div_eq_mul_inv, mul_assoc]
  · intro hk
    rw [mem_ker_normU] at hk
    obtain ⟨u, hu, -⟩ := h.basis
    have key : ∀ x : E, x + k * τ x = k * τ (x + k * τ x) := by
      intro x
      rw [map_add, map_mul, h.inv]
      linear_combination (-x) * hk
    have hx : ∃ x : E, x + k * τ x ≠ 0 := by
      by_contra hc
      push Not at hc
      have h1 := hc 1
      have h2 := hc u
      rw [map_one, mul_one] at h1
      apply hu.ne_zero
      linear_combination h2 - τ u * h1
    obtain ⟨x, hx⟩ := hx
    exact MonoidHom.mem_range.2 ⟨(isUnit_of_ne hf hx).unit, ratioU_eq_iff.2 (key x)⟩

theorem sq_sub_one (hq : 1 < q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h2 : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
  rw [h2, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem card_fibre_field (h : ResAlg E τ q ε) (hf : IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q + 1 := by
  have := finite_of_resAlg h
  have := nontrivial_of_resAlg h
  have hq := h.one_lt
  have hU : Nat.card Eˣ = q ^ 2 - 1 := card_units h hf
  have hsq := sq_sub_one hq
  have lag : ∀ f : Eˣ →* Eˣ, Nat.card Eˣ = Nat.card f.range * Nat.card f.ker := fun f => by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hR : Nat.card (ratioU τ).range = q + 1 := by
    have e := lag (ratioU τ)
    rw [card_ker_ratioU h, hU, hsq, mul_comm (q - 1)] at e
    exact (Nat.eq_of_mul_eq_mul_right (by omega) e).symm
  have hK : Nat.card (normU τ).ker = q + 1 := by
    rw [← range_ratioU h hf]
    exact hR
  have hN : Nat.card (normU τ).range = q - 1 := by
    have e := lag (normU τ)
    rw [hK, hU, hsq] at e
    exact (Nat.eq_of_mul_eq_mul_right (by omega) e).symm
  let S : Set Eˣ := {k | τ (k : E) = k}
  have hS : Nat.card S = q - 1 := by
    rw [← card_fixed_ne h]
    exact Nat.card_congr
      { toFun := fun k => ⟨((k.1 : Eˣ) : E), k.2, k.1.ne_zero⟩
        invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, x.2.1⟩
        left_inv := fun k => Subtype.ext (Units.ext rfl)
        right_inv := fun x => rfl }
  have hsub : ((normU τ).range : Set Eˣ) ⊆ S := by
    intro k hk
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hk
    show τ ((normU τ b : Eˣ) : E) = normU τ b
    rw [normU_apply, Units.val_mul, coe_tauU, map_mul, h.inv, mul_comm]
  have heq : ((normU τ).range : Set Eˣ) = S := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite S)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hS]
    exact hN.ge
  have htu : IsUnit t := isUnit_of_ne hf t0
  have hmem : htu.unit ∈ (normU τ).range := by
    rw [← SetLike.mem_coe, heq]
    exact ht
  obtain ⟨a₀, ha₀⟩ := MonoidHom.mem_range.1 hmem
  have hn : ∀ b : Eˣ, (b : E) * τ b = t → normU τ b = htu.unit := fun b hb =>
    Units.ext (by rw [normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec]; exact hb)
  have hna : (a₀ : E) * τ a₀ = t := by
    have h5 := congrArg Units.val ha₀
    rwa [normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec] at h5
  have hau : ∀ a : {a : E // a * τ a = t}, IsUnit a.1 := fun a =>
    isUnit_of_mul_isUnit_left (show IsUnit (a.1 * τ a.1) by rw [a.2]; exact htu)
  have hna' : ∀ a : {a : E // a * τ a = t}, normU τ (hau a).unit = htu.unit := fun a =>
    hn _ (by rw [IsUnit.unit_spec]; exact a.2)
  rw [← hK]
  symm
  exact Nat.card_congr
    { toFun := fun k => ⟨(((k : Eˣ) * a₀ : Eˣ) : E), by
        have hk := mem_ker_normU.1 k.2
        rw [Units.val_mul, map_mul]
        linear_combination ((a₀ : E) * τ (a₀ : E)) * hk + hna⟩
      invFun := fun a => ⟨(hau a).unit * a₀⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ha₀, hna' a, mul_inv_cancel]⟩
      left_inv := fun k => Subtype.ext (Units.ext (by simp [mul_assoc]))
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }

theorem card_fibre : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ t : E, τ t = t → t ≠ 0 → (Nat.card {a : E // a * τ a = t} : ℤ) = q - ε := by
  intro E _ τ q ε h t ht t0
  have hq := h.one_lt
  rcases h.eps with ⟨rfl, hf⟩ | ⟨rfl, hnf⟩
  · rw [card_fibre_field h hf ht t0]
    omega
  · rw [card_fibre_split h hnf ht t0]
    omega

end GlobalTheory.CompanionTheory.UnrDens.NormUnit
